module Utils.Logger (
      LoggerT(..)
    , printLog
    , logSolve
    , logSolveComplete
    , logVerify
    , logRefine
    ) where

import Synthesise.GameTree
import Control.Monad.State
import Data.Maybe
import Utils.Utils

data SynthTrace = SynthTrace {
      input             :: GameTree
    , candidate         :: Maybe GameTree
    , player            :: Player
    , result            :: Maybe GameTree
    , verification      :: [SynthTrace]
    , refinement        :: [SynthTrace]
} deriving (Eq)

instance Show SynthTrace where
    show st = "{ ver: " ++ concatMap show (verification st) ++ ", ref: " ++ concatMap show (refinement st) ++ "}"

data TraceCrumb = VerifyCrumb Int | RefineCrumb Int
    deriving (Show, Eq)

type LoggerT m = StateT (Maybe SynthTrace, [TraceCrumb]) m

printLog :: LoggerT IO a -> IO (a)
printLog logger = do
    (r, (Just trace, _)) <- runStateT logger (Nothing, [])
    writeFile "debug.html" (htmlHeader ++ outputHTML trace ++ htmlFooter)
    return r

htmlHeader = "<html><head>"
    ++ "<link rel=\"stylesheet\" href=\"debug.css\">"
    ++ "<script src=\"http://code.jquery.com/jquery-1.11.0.min.js\"></script>"
    ++ "<script src=\"http://code.jquery.com/jquery-migrate-1.2.1.min.js\"></script>"
    ++ "<script src=\"debug.js\"></script>"
    ++ "</head><body>"

htmlFooter = "</body></html>"

outputHTML trace = "<div class=\"trace " ++ show (player trace) ++ "\">"
    ++ "<h3><button type=\"button\" class=\"shrink\">-</button> Trace for " ++ (show (player trace)) ++ "</h3><hr />"
    ++ "<div class=\"input gametree\"><h3>Input GT</h3><pre>" ++ printTree (input trace) ++ "</pre></div>"
    ++ "<div class=\"candidate gametree\"><h3>Candidate</h3><pre>" ++ maybe "Nothing" printTree (candidate trace) ++ "</pre></div>"
    ++ "<div class=\"verifyRefineLoop\">" ++ verifyRefineLoopHTML (paddedZip (verification trace) (refinement trace)) ++ "</div>"
    ++ "<div class=\"result gametree\"><h3>Result</h3><pre>" ++ maybe "Nothing" printTree (result trace) ++ "</pre></div>"
    ++ "</div>"

verifyRefineLoopHTML [] = ""
verifyRefineLoopHTML ((v, r):vrs)   = "<hr />"
    ++ "<div class=\"verification\"><h3>Verification</h3>" ++ outputHTML v ++ "</div>"
    ++ maybe "" (\x -> "<div class=\"refinement\"><h3>Refinement</h3>" ++ outputHTML x ++ "</div>") r
    ++ "<hr />"
    ++ verifyRefineLoopHTML vrs


insertAt :: SynthTrace -> [TraceCrumb] -> SynthTrace -> SynthTrace
insertAt x [] t             = x
insertAt x ((VerifyCrumb c):[]) t
    | c == length (verification t)  = t { verification = verification t ++ [x] }
    | c < length (verification t)   = t { verification = adjust (\_ -> x) c (verification t) }
    | otherwise                     = error $ "Error in Logger"
insertAt x ((RefineCrumb c):[]) t
    | c == length (refinement t)  = t { refinement = refinement t ++ [x] }
    | c < length (refinement t)   = t { refinement = adjust (\_ -> x) c (refinement t) }
    | otherwise                     = error $ "Error in Logger"
insertAt x ((VerifyCrumb c):cs) t
    | null (verification t) = t { verification = [x] }
    | otherwise             = t { verification = adjust (insertAt x cs) c (verification t) }
insertAt x ((RefineCrumb c):cs) t   
    | null (refinement t)   = t { refinement = [x] }
    | otherwise             = t { refinement = adjust (insertAt x cs) c (refinement t) }

follow trace []                     = trace
follow trace ((VerifyCrumb c):cs)   = follow (verification trace !! c) cs
follow trace ((RefineCrumb c):cs)   = follow (refinement trace !! c) cs
    
updateAt :: (SynthTrace -> SynthTrace) -> [TraceCrumb] -> SynthTrace -> SynthTrace
updateAt f [] t                     = f t
updateAt f ((VerifyCrumb c):cs) t   = t { verification = adjust (updateAt f cs) c (verification t) }
updateAt f ((RefineCrumb c):cs) t   = t { refinement = adjust (updateAt f cs) c (refinement t) }

logSolve :: Monad m => GameTree -> Maybe GameTree -> Player -> LoggerT m ()
logSolve gt cand player = do
    (trace, crumb) <- get
    let newTrace = SynthTrace {
          input = gt
        , candidate = cand
        , player = player
        , result = Nothing
        , verification = []
        , refinement = []
    }
    let trace' = if isJust trace
        then insertAt newTrace crumb (fromJust trace)
        else newTrace
    put (Just trace', crumb)

logSolveComplete :: Monad m => Maybe GameTree -> LoggerT m ()
logSolveComplete gt = do
    (trace, crumb) <- get
    let trace' = updateAt (\x -> x { result = gt }) crumb (fromJust trace)
    put (Just trace', if null crumb then [] else init crumb)

logVerify :: Monad m => LoggerT m ()
logVerify = do
    (trace, crumb) <- get
    let currentTrace = follow (fromJust trace) crumb
    put (trace, crumb ++ [VerifyCrumb (length (verification currentTrace))])

logRefine :: Monad m => LoggerT m ()
logRefine = do
    (trace, crumb) <- get
    let currentTrace = follow (fromJust trace) crumb
    put (trace, crumb ++ [RefineCrumb (length (refinement currentTrace))])
