{-# LANGUAGE RecordWildCards #-}

import System.Environment
import System.Console.GetOpt
import System.TimeIt
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Error

import Utils.Logger
import Expression.Expression
import Expression.Parse
import Synthesise.Synthesise

data Option = InputFile String
            | Bound String
            | DebugMode (Maybe String)

data Config = Config { tslFile      :: String
                     , bound        :: Int
                     , debugMode    :: Int
                     } deriving (Show, Eq)

defaultConfig = Config {
      tslFile     = ""
    , bound       = 3
    , debugMode   = 1
    }

options =
    [ Option ['k']  ["bound"]   (ReqArg Bound "K")      "Bounded reachability unroll length"
    , Option ['d']  ["debug"]   (OptArg DebugMode "D")  "Debug mode. 0 = None, 1 = Output at end, 2 = Dump throughout"
    ]

addOption (InputFile fn) c  = c {tslFile = fn}
addOption (Bound k) c       = c {bound = (read k)}
addOption (DebugMode d) c   = maybe c (\x -> c {debugMode = read x}) d

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

            f <- readFile (tslFile config)
            let log = runEitherT (run config f)
            printLog (debugMode config) log

    case res of
        Left s      -> putStrLn s
        Right True  -> putStrLn "Realisable"
        Right False -> putStrLn "Unrealisable"

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
    spec <- hoistEither $ parser (tslFile config) f
    synthesise (bound config) spec
