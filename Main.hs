{-# LANGUAGE RecordWildCards #-}

import System.Environment
import System.Console.GetOpt
import System.TimeIt
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Either
import Data.Maybe
import Data.String.Utils

import Utils.Logger
import Expression.Expression
import Expression.Parse
import qualified Expression.ParseAIG as AIG
import Synthesise.Synthesise

import SatSolver.Interpolator
import Synthesise.SolverT
import Synthesise.Config

data Option = InputFile String
            | Bound String
            | DebugMode (Maybe String)
            | Strategy FilePath
            | DefaultMoves String
            | DefaultMovesIt String
            | BadMoves
            | InitMinimisation String
            | StratShortening (Maybe String)


defaultConfig = Config {
      tslFile       = ""
    , bound         = Nothing
    , debugMode     = 0
    , strategyFile  = Nothing
    , moveLearning  = MLDefaultMoves 2
    , initMin       = Nothing
    , shortening    = ShortenExistential
    }

options =
    [ Option ['k']  ["bound"]   (ReqArg Bound "K")              "Bounded reachability unroll length"
    , Option ['d']  ["debug"]   (OptArg DebugMode "D")          "Debug mode. 0 = None, 1 = Output at end, 2 = Dump throughout, 3 = Dump after each loop"
    , Option ['s']  ["strat"]   (ReqArg Strategy "FILE")        "Strategy file"
    , Option ['m']  ["moves"]   (ReqArg DefaultMoves "FILE")    "Default moves files"
    , Option ['e']  ["default"] (ReqArg DefaultMovesIt "E")     "Default moves iterations"
    , Option ['b']  ["badmoves"] (NoArg BadMoves)               "Learn bad moves"
    , Option ['i']  ["initmin"] (ReqArg InitMinimisation "I")   "Minimise init cube"
    , Option ['h']  ["shorten"] (OptArg StratShortening "S")    "Strategy Shortening. 0 = None, 1 = Existential, 2 = Universal, 3 = Both"
    ]

addOption (InputFile fn) c          = c {tslFile = fn}
addOption (Bound k) c               = c {bound = Just (read k)}
addOption (DebugMode d) c           = maybe c (\x -> c {debugMode = read x}) d
addOption (Strategy s) c            = c {strategyFile = Just s}
addOption (DefaultMoves m) c        = c {moveLearning = MLFixedMoves m}
addOption (DefaultMovesIt i) c      = c {moveLearning = MLDefaultMoves (read i)}
addOption (BadMoves) c              = c {moveLearning = MLBadMoves}
addOption (InitMinimisation i)  c   = c {initMin = Just (read i)}
addOption (StratShortening s) c     = maybe c (\x -> c {shortening = toEnum (read x)}) s

main = do
    putStrLn "------------------------------------"
    putStrLn "TermiteSAT  v0.1"
    timeIt $ mainTimed

mainTimed = do
    config <- getConfig

    res <- case config of
        Left e -> return $ Left e
        Right config -> do
            putStrLn $ "TSL file    " ++ tslFile config
            putStrLn $ "Max Rank    " ++ show (bound config)
            putStrLn $ "Debug Mode  " ++ case debugMode config of
                0 -> "No output"
                1 -> "Print log"
                2 -> "Continuous log dumping"
                3 -> "Log each rank (unbounded)"
            putStrLn $ "Shortening  " ++ show (shortening config)
            putStrLn $ "Move Learning " ++ show (moveLearning config)

            when (isJust (strategyFile config)) $ 
                putStrLn ("Strategy    " ++ fromJust (strategyFile config))

            clearLogDir (debugMode config)
            f <- readFile (tslFile config)
            let log = runEitherT (run config f)
            printLog (debugMode config) log

    case res of
        Left s          -> putStrLn s
        Right (Just k)  -> putStrLn $ "Existential wins in " ++ (show k)
        Right Nothing   -> putStrLn "Universal wins"

    putStrLn "------------------------------------"

getConfig :: IO (Either String Config)
getConfig = do
    args <- liftIO getArgs

    let config = if length args == 0
        then Left "No filename given"
        else Right $ addOption (InputFile (last args)) defaultConfig

    case getOpt Permute options args of
        (o, n, [])  -> return $ (foldr (liftM . addOption) config o)
        _           -> return $ Left "Bad options"
    

run config f = do
    spec <- hoistEither $ parse (tslFile config) f
    case (bound config) of
        Nothing -> unboundedSynthesis spec config
        Just k  -> do
            if isJust (strategyFile config)
            then do
                playStrategy k spec config (fromJust (strategyFile config))
            else do
                synthesise k spec config

parse fn | endswith ".tsl" fn     = parser fn
         | endswith ".aag" fn     = AIG.parser fn
