{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
    synthesise
    ) where

import Debug.Trace
import Data.Maybe
import Data.List
import Data.Tuple.Update
import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map

import Expression.Parse
import Expression.Compile
import Expression.Expression
import Synthesise.GameTree 
import SatSolver.SatSolver

data CompiledSpec = CompiledSpec {
      t       :: [Expression]
    , g       :: [Expression]
    , u       :: [Expression]
    , vc      :: [Expression]
    , vu      :: [Expression]
    }
    

synthesise :: Int -> ParsedSpec -> EitherT String IO Bool
synthesise k spec = evalStateT (synthesise' k spec) emptyManager

synthesise' k spec = do
    let ParsedSpec{..} = spec

    t' <- mapM compile trans
    t <- conjunct t'
    g' <- compile goal
    g <- setRank 0 g'
    u <- compile ucont

    let xvars = map compileVar stateVars
    let uvars = map compileVar ucontVars
    let cvars = map compileVar contVars

    u_idle <- equalsConstant (concat uvars) 0
    c_idle <- equalsConstant (concat cvars) 0

    vc <- equate c_idle u
    vu <- implicate u =<< (negation u_idle)

    ts  <- iterateNM (k-1) unrollExpression t
    gs  <- iterateNM (k-1) unrollExpression g
    us  <- iterateNM (k-1) unrollExpression u
    vcs <- iterateNM (k-1) unrollExpression vc
    vus <- iterateNM (k-1) unrollExpression vu

    let cspec = CompiledSpec {
          t     = ts
        , g     = gs
        , u     = us
        , vc    = vcs
        , vu    = vus
        }

    init <- compile init
    solveAbstract cspec init (empty k)

solveAbstract spec s gt = do
    cand <- findCandidate spec s gt

    liftIO $ putStrLn (show cand)

    return False

findCandidate spec s gt = do
    let CompiledSpec{..} = spec
    let r = treerank gt

    d <- driverFml spec (r-1)

    dimacs <- toDimacs d
---    liftIO $ putStrLn (intercalate "\n" (map show dimacs))
    mi <- getMaxIndex
    res <- liftIO $ satSolve mi dimacs

    if satisfiable res
    then do
        move <- saveContMove r d (fromJust (model res))
        cmvalid <- isCMoveValid r spec (fromJust (model res))
        umvalid <- isUMoveValid r spec (fromJust (model res))
        liftIO $ putStrLn (show (cmvalid, umvalid))
        return (Just move)
    else do
        return Nothing

driverFml spec rank = do
    let CompiledSpec{..} = spec
    prev <- if rank == 0
        then trueExpr
        else driverFml spec (rank - 1)

    goal <- disjunct [(g !! rank), prev]
    conjunct [t !! rank, vc !! rank, vu !! rank, goal]

saveContMove rnk fml model = do
    move <- saveMove rnk fml model
    return $ filter isCont move
    where
        isCont (Assignment _ v) = varsect v == ContVar

saveMove rnk fml model = do
    exprs <- mapM (lookupExpression . abs) model
    let moves = zipMaybe2 model exprs
    let vmoves = map (mapSnd (getVar . operation)) moves
    let assignments = map makeAssignment ((uncurry zipMaybe2) (unzip vmoves))
    liftIO $ putStrLn (show assignments)
    return $ filter (isRank rnk) assignments
    where
        getVar (ELit v)  = Just v
        getVar _         = Nothing
        isRank r (Assignment _ v)   = r == (rank v)

isUMoveValid r spec model = do
    let CompiledSpec{..} = spec
    let vuIndex = (map index vu) !! (r - 1)
    let vuModel = model !! (vuIndex - 1)
    when ((abs vuModel) /= vuIndex) (throwError "Assumption about model incorrect")
    return $ vuModel > 0

isCMoveValid r spec model = do
    let CompiledSpec{..} = spec
    let vcIndex = (map index vc) !! (r - 1)
    let vcModel = model !! (vcIndex - 1)
    when ((abs vcModel) /= vcIndex) (throwError "Assumption about model incorrect")
    return $ vcModel > 0

iterateNM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateNM 0 f x = return [x]
iterateNM n f x = do
    fx <- f x
    xs <- iterateNM (n - 1) f fx
    return (x : xs)

zipMaybe2 :: [a] -> [Maybe b] -> [(a, b)]
zipMaybe2 as bs = mapMaybe f (zip as bs)
    where
    f (a, b) = do
        b' <- b
        return (a, b')

mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (x,y) = (f x,y)

mapSnd :: (a -> b) -> (c, a) -> (c, b)
mapSnd f (x,y) = (x,f y)

throwError :: Monad m => String -> ExpressionT m a
throwError = lift . left
