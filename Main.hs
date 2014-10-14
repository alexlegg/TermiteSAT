{-# LANGUAGE RecordWildCards #-}

import System.Environment
import System.Console.GetOpt
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Error

import Expression.Expression
import Expression.Parse
import Synthesise.Synthesise

data Option = InputFile String
            | Bound String

data Config = Config { tslFile      :: String
                     , bound        :: Int
                     } deriving (Show, Eq)

defaultConfig = Config {
    tslFile     = "",
    bound       = 3
    }

options =
    [ Option ['k']  ["bound"]   (ReqArg Bound "K") "Bounded reachability unroll length"]

addOption (InputFile fn) c  = c {tslFile = fn}
addOption (Bound k) c       = c {bound = (read k)}

main = do
    config <- getConfig

    res <- case config of
        Left e -> return $ Left e
        Right config -> do
            f <- readFile (tslFile config)
            runEitherT (run (tslFile config) f)

    case res of
        Left s  -> putStrLn s
        Right r -> putStrLn (show r)

getConfig :: IO (Either String Config)
getConfig = do
    args <- liftIO getArgs

    let config = if length args == 0
        then Left "No filename given"
        else Right $ addOption (InputFile (last args)) defaultConfig

    case getOpt Permute options args of
        (o, n, [])  -> return $ (foldr (liftM . addOption) config o)
        _           -> return $ Left "Bad options"
    

run fn f = do
    spec <- hoistEither $ parser fn f
    synthesise spec
