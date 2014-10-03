{-# LANGUAGE RecordWildCards #-}

import System.Environment
import System.Console.GetOpt
import Control.Monad
import Control.Monad.IO.Class

import Expression.Expression
import Expression.Parse

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
    args <- liftIO getArgs

    let config = if length args == 0
        then Nothing
        else Just $ addOption (InputFile (last args)) defaultConfig

    config <- case getOpt Permute options args of
        (o, n, [])  -> return $ (foldr (liftM . addOption) config o)
        _           -> return $ Nothing

    case config of
        Nothing     -> error "Invalid Config"
        Just config -> do
            f <- readFile (tslFile config)
            case parser f of
                Left err    -> error err
                Right spec  -> putStrLn (show spec)

