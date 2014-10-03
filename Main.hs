import System.Environment
import System.Console.GetOpt
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
    let config = addOption (InputFile (last args)) defaultConfig
    config <- case getOpt Permute options args of
        (o, n, [])  -> return $ foldr addOption config o
        _           -> error "Invalid Options"

    putStrLn (show config)

