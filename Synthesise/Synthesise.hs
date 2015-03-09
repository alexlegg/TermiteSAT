{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
        synthesise
      , playStrategy
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Loops
import Data.Functor
import Data.Maybe
import Data.Tree
import qualified Data.Traversable as T
import Data.List.Split
import System.IO

import Utils.Logger
import Utils.Utils
import Expression.Parse
import Expression.Compile
import Expression.Expression
import Synthesise.Solver
import Expression.AST
import SatSolver.Interpolator

synthesise :: Int -> ParsedSpec -> EitherT String (LoggerT IO) Bool
synthesise k spec = evalStateT (synthesise' k spec) emptyManager

synthesise' k spec = do
    (init, cspec) <- loadFmls k spec
    evalStateT (evalStateT (checkRank cspec k init) emptyLearnedStates) Nothing

playStrategy :: Int -> ParsedSpec -> FilePath -> EitherT String (LoggerT IO) Bool
playStrategy k spec sFile = evalStateT (playStrategy' k spec sFile) emptyManager

playStrategy' k spec sFile = do
    (player, strat) <- readStrategyFile k sFile
    (init, cspec)   <- loadFmls k spec
    vars            <- mapM (mapFstM (mapM (mapFstM lookupVarName))) strat
    let varTree     = unfoldTree makeStrategy vars
    let assTree     = fmap (\(vs, r) -> map (\(var, val) -> makeAssignmentValue (map (setVarRank (r+1)) var) val) vs) varTree

    evalStateT (evalStateT (checkStrategy cspec k init player assTree) emptyLearnedStates) Nothing

makeStrategy :: [(a, Int)] -> ((a, Int), [[(a, Int)]])
makeStrategy ((x, r):xrs) = ((x, r), children xrs)
    where
        children []                 = []
        children ((x', r'):xrs')    = if r' == r-1
                                    then let (cs, ncs) = span (\(a, b) -> b < r-1) xrs' in
                                        ((x', r') : cs) : children ncs
                                    else []

enumValidity vi@(VarInfo {enum = Nothing}) = return Nothing
enumValidity vi@(VarInfo {enum = Just es}) = do
    let vars = compileVar vi
    let invalid = [(length es)..((2 ^ sz vi)-1)]
    if null invalid
    then return Nothing
    else do 
        eqs <- mapM ((negation =<<) . equalsConstant vars) invalid
        c <- conjunct eqs
        c' <- setRank 1 c
        return (Just c')

loadFmls k spec = do
    let ParsedSpec{..} = spec

    t' <- mapM compile trans
    t <- conjunct t'
    g' <- compile goal
    cg <- setRank 0 g'
    ug <- negation cg
    u <- compile ucont

    let svars = concatMap compileVar stateVars
    let uvars = concatMap compileVar ucontVars
    let cvars = concatMap compileVar contVars

    let vinfo = stateVars ++ ucontVars ++ contVars

    u_idle <- equalsConstant (map (\v -> v {rank = 1}) uvars) 0
    c_idle <- equalsConstant (map (\v -> v {rank = 1}) cvars) 0

    cev <- mapM enumValidity contVars
    uev <- mapM enumValidity ucontVars

    vc <- equate c_idle u
---    vc  <- conjunct (vc' : catMaybes cev)
    vu' <- implicate u =<< (negation u_idle)
    vu  <- conjunct (vu' : catMaybes uev)

    ts  <- iterateNM (k-1) unrollExpression t
    cgs <- iterateNM (k-1) unrollExpression cg
    ugs <- iterateNM (k-1) unrollExpression ug
    us  <- iterateNM (k-1) unrollExpression u
    vcs <- iterateNM (k-1) unrollExpression vc
    vus <- iterateNM (k-1) unrollExpression vu

    steps <- zipWith3M (\t vc vu -> conjunct [t, vc, vu]) ts vcs vus

    let cspec = CompiledSpec {
          t     = steps
        , cg    = cgs
        , ug    = ugs
        , u     = us
        , vc    = vcs
        , vu    = vus
        , cont  = cvars
        , ucont = uvars
        , svars = svars
        , vinfo = vinfo
        }

    lift $ lift $ logSpec cspec

    init <- compile init
    init <- setRank k init

    initManager (map exprIndex (steps ++ cgs ++ ugs ++ us ++ vcs ++ vus))
    return (init, cspec)

iterateNM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateNM 0 f x = return [x]
iterateNM n f x = do
    fx <- f x
    xs <- iterateNM (n - 1) f fx
    return (x : xs)

readStrategyFile k fn = do
    liftIO $ withFile fn ReadMode $ \h -> do
        player <- hGetLine h
        strategy <- whileM (fmap not $ hIsEOF h) $ do
            line <- hGetLine h
            let depth   = length (takeWhile (== ' ') line) `div` 4
            let nvPairs = map readValue $ splitOn ", " (dropWhile (== ' ') line)
            return (nvPairs, k-(depth+1))
        return (player, strategy)

readValue s = let [l, r] = splitOn " = " s in (l, read r :: Int)
