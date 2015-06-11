{-# LANGUAGE RecordWildCards #-}

import System.Environment
import System.Console.GetOpt
import System.TimeIt
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Error
import Data.Maybe
import Data.String.Utils

import Utils.Logger
import Expression.Expression
import Expression.Parse
import qualified Expression.ParseAIG as AIG
import Synthesise.Synthesise

import SatSolver.Interpolator

data Option = InputFile String
            | Bound String
            | DebugMode (Maybe String)
            | Strategy FilePath
            | DefaultMoves FilePath
            | InitMinimisation

data Config = Config { tslFile      :: String
                     , bound        :: Maybe Int
                     , debugMode    :: Int
                     , strategyFile :: Maybe FilePath
                     , defaultMoves :: Maybe FilePath
                     , initMin      :: Bool
                     } deriving (Show, Eq)

defaultConfig = Config {
      tslFile       = ""
    , bound         = Nothing
    , debugMode     = 1
    , strategyFile  = Nothing
    , defaultMoves  = Nothing
    , initMin       = False
    }

options =
    [ Option ['k']  ["bound"]   (ReqArg Bound "K")              "Bounded reachability unroll length"
    , Option ['d']  ["debug"]   (OptArg DebugMode "D")          "Debug mode. 0 = None, 1 = Output at end, 2 = Dump throughout, 3 = Dump after each loop"
    , Option ['s']  ["strat"]   (ReqArg Strategy "FILE")        "Strategy file"
    , Option ['m']  ["moves"]   (ReqArg DefaultMoves "FILE")    "Default moves files"
    , Option ['i']  ["initmin"] (NoArg InitMinimisation)        "Minimise init cube"
    ]

addOption (InputFile fn) c      = c {tslFile = fn}
addOption (Bound k) c           = c {bound = Just (read k)}
addOption (DebugMode d) c       = maybe c (\x -> c {debugMode = read x}) d
addOption (Strategy s) c        = c {strategyFile = Just s}
addOption (DefaultMoves m) c    = c {defaultMoves = Just m}
addOption (InitMinimisation) c  = c {initMin = True}

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

            when (isJust (strategyFile config)) $ 
                putStrLn ("Strategy    " ++ fromJust (strategyFile config))

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
        Nothing -> unboundedSynthesis spec (defaultMoves config) (initMin config)
        Just k  -> do
            if isJust (strategyFile config)
            then do
                playStrategy k spec (fromJust (strategyFile config))
            else do
                synthesise k spec (defaultMoves config)

parse fn | endswith ".tsl" fn     = parser fn
         | endswith ".aag" fn     = AIG.parser fn
