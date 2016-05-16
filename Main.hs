{-# LANGUAGE RecordWildCards, LambdaCase #-}
module Main (main) where

import System.Environment
import System.Console.GetOpt
import System.TimeIt
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Either
import Control.Concurrent
import Data.String.Utils

import Utils.Logger
import Expression.Parse
import qualified Expression.ParseAIG as AIG
import Synthesise.Synthesise
import Synthesise.Config

data Option = InputFile String
            | Bound String
            | DebugMode (Maybe String)
            | DefaultMoves String
            | DefaultMovesIt String
            | InitMinimisation String
            | StratShortening (Maybe String)
            | Portfolio


defaultConfig :: Config
defaultConfig = Config {
      tslFile       = ""
    , solverType    = Unbounded
    , debugMode     = 0
    , moveLearning  = MLDefaultMoves 2
    , initMin       = Nothing
    , shortening    = ShortenExistential
    , portfolio     = False
    }

options :: [OptDescr Option]
options =
    [ Option ['k']  ["bound"]       (ReqArg Bound "K")              "Bounded reachability unroll length"
    , Option ['d']  ["debug"]       (OptArg DebugMode "D")          "Debug mode. 0 = None, 1 = Output at end, 2 = Dump throughout, 3 = Dump after each loop"
    , Option ['m']  ["moves"]       (ReqArg DefaultMoves "FILE")    "Default moves files"
    , Option ['e']  ["default"]     (ReqArg DefaultMovesIt "E")     "Default moves iterations"
    , Option ['i']  ["initmin"]     (ReqArg InitMinimisation "I")   "Minimise init cube"
    , Option ['h']  ["shorten"]     (OptArg StratShortening "S")    "Strategy Shortening. 0 = None, 1 = Existential, 2 = Universal, 3 = Both"
    , Option ['p']  ["portfolio"]   (NoArg Portfolio)               "Portfolio solver"
    ]

addOption :: Option -> Config -> Config
addOption (InputFile fn) c          = c {tslFile = fn}
addOption (Bound k) c               = c {solverType = Bounded (read k)}
addOption (DebugMode d) c           = maybe c (\x -> c {debugMode = read x}) d
addOption (DefaultMoves m) c        = c {moveLearning = MLFixedMoves m}
addOption (DefaultMovesIt i) c      = c {moveLearning = MLDefaultMoves (read i)}
addOption (InitMinimisation i)  c   = c {initMin = Just (read i)}
addOption (StratShortening s) c     = maybe c (\x -> c {shortening = toEnum (read x)}) s
addOption (Portfolio) c             = c {portfolio = True}

main :: IO ()
main = timeIt $ mainTimed

mainTimed :: IO ()
mainTimed = do
    getConfig >>= \case
        Left e          -> putStrLn e
        Right config    -> do
            when (debugMode config > 0) $ do
                putStrLn $ "TSL file    " ++ tslFile config
                putStrLn $ "Solver Type " ++ show (solverType config)
                putStrLn $ "Debug Mode  " ++ case (debugMode config) of
                    0 -> "No output"
                    1 -> "Print log"
                    2 -> "Continuous log dumping"
                    3 -> "Log each rank (unbounded)"
                    _ -> "Log each rank (unbounded)"
                putStrLn $ "Shortening  " ++ show (shortening config)
                putStrLn $ "Move Learning " ++ show (moveLearning config)

            r <- if portfolio config
                then runPortfolio config
                else runSolver config

            printResult r

getConfig :: IO (Either String Config)
getConfig = do
    args <- liftIO getArgs

    let config = if length args == 0
        then Left "No filename given"
        else Right $ addOption (InputFile (last args)) defaultConfig

    case getOpt Permute options args of
        (o, _, [])  -> return $ (foldr (liftM . addOption) config o)
        _           -> return $ Left "Bad options"
    
runPortfolio :: Config -> IO (Either String (Maybe Int))
runPortfolio config = do
    mv <- newEmptyMVar

    _ <- forkSolver mv $ runSolver config
    _ <- forkSolver mv $ runSolver (config { initMin = Nothing })

    readMVar mv

forkSolver :: MVar (Either String a) -> (IO (Either String a)) -> IO ThreadId
forkSolver mv io =
    forkFinally io $ \case
        Left e  -> putMVar mv (Left (show e))
        Right r -> putMVar mv r

runSolver :: Config -> IO (Either String (Maybe Int))
runSolver config = do
    clearLogDir (debugMode config)
    f <- readFile (tslFile config)
    printLog (debugMode config) $ runEitherT (run config f)

run :: Config -> String -> EitherT String (LoggerT IO) (Maybe Int)
run config f = do
    spec <- hoistEither $ parse (tslFile config) f
    case (solverType config) of
        Unbounded   -> unboundedSynthesis spec config
        Bounded k   -> synthesise k spec config

parse :: String -> String -> Either String ParsedSpec
parse fn | endswith ".tsl" fn   = parser fn
         | endswith ".aag" fn   = AIG.parser fn
         | otherwise            = const (Left "Unsupported file type")

printResult :: Either String (Maybe a) -> IO ()
printResult (Left err)          = putStrLn err
printResult (Right (Just _))    = putStrLn "UNREALIZABLE"
printResult (Right Nothing)     = putStrLn "REALIZABLE"
