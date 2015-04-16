{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
        synthesise
      , unboundedSynthesis
      , playStrategy
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Loops
import Data.Functor
import Data.Maybe
import Data.Tree
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Data.List.Split
import System.IO

import Utils.Logger
import Utils.Utils
import Expression.Parse
import Expression.Compile
import Expression.Expression
import Synthesise.Solver
import Synthesise.SolverT
import Synthesise.GameTree
import Expression.AST
import SatSolver.Interpolator

synthesise :: Int -> ParsedSpec -> EitherT String (LoggerT IO) (Maybe Int)
synthesise k spec = do
    evalStateT (synthesise' k spec BoundedLearning) emptyManager

unboundedSynthesis :: ParsedSpec -> EitherT String (LoggerT IO) (Maybe Int)
unboundedSynthesis spec = do
    evalStateT (unbounded spec) emptyManager

unbounded spec = do
    (init, cspec) <- loadFmls 1 spec
    evalStateT (unboundedLoop init cspec 1) (emptyLearnedStates UnboundedLearning)

unboundedLoop :: Expression -> CompiledSpec -> Int -> SolverT (Maybe Int)
unboundedLoop init spec k = do
    liftIO $ putStrLn $ "Unbounded Loop " ++ show k

    ls <-get 
    
    when (k == 6) $ do
        liftIO $ withFile "winningMay" WriteMode $ \h -> do
            forM (Map.toList (winningMay ls)) $ \(r, wm) -> do
                hPutStrLn h (show r)
                forM (Set.toList wm) $ \s ->
                    hPutStrLn h (printMove spec (Just s))
                hPutStrLn h "--"
            return ()

    exWins <- checkInit k init (winningMust ls) (head (cg spec))

    unWins <- checkUniversalWin spec k

    if exWins
    then return (Just (k-1))
    else do
        if unWins
        then return Nothing
        else do
            r <- checkRank spec k init
            if r
            then return (Just k) --Counterexample exists for Universal player
            else do
                spec' <- liftE $ unrollSpec spec
                init' <- liftE $ setRank (k+1) init
                unboundedLoop init' spec' (k+1)

synthesise' k spec learning = do
    (init, cspec) <- loadFmls k spec
    r <- evalStateT (checkRank cspec k init) (emptyLearnedStates learning)
    return $ if r then (Just k) else Nothing

playStrategy :: Int -> ParsedSpec -> FilePath -> EitherT String (LoggerT IO) (Maybe Int)
playStrategy k spec sFile = evalStateT (playStrategy' k spec sFile) emptyManager

playStrategy' k spec sFile = do
    (player, strat) <- readStrategyFile k sFile
    (init, cspec)   <- loadFmls k spec
    vars            <- mapM (mapFstM (mapM (mapFstM lookupVarName))) strat
    let varTree     = unfoldTree makeStrategy vars
    let assTree     = fmap (\(vs, r) -> map (\(var, val) -> makeAssignmentValue (map (setVarRank (r+1)) var) val) vs) varTree

    r <- evalStateT (checkStrategy cspec k init player assTree) (emptyLearnedStates BoundedLearning)
    return $ if r then (Just k) else Nothing

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
    cgs <- iterateNM k unrollExpression cg
    ugs <- iterateNM k unrollExpression ug
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

unrollSpec spec = do
    
    t'  <- unrollExpression (last (t spec))
    cg' <- unrollExpression (last (cg spec))
    ug' <- unrollExpression (last (ug spec))
    u'  <- unrollExpression (last (u spec))
    vc' <- unrollExpression (last (vc spec))
    vu' <- unrollExpression (last (vu spec))

    let spec' = spec {
          t   = t spec ++ [t']
        , cg  = cg spec ++ [cg']
        , ug  = ug spec ++ [ug']
        , u   = u spec ++ [u']
        , vc  = vc spec ++ [vc']
        , vu  = vu spec ++ [vu']
    }

    initManager (map exprIndex ((t spec') ++ (cg spec') ++ (ug spec') ++ (u spec') ++ (vc spec') ++ (vu spec')))
    return spec'

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
