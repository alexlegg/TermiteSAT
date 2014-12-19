module Utils.Logger (
      LoggerT(..)
    , printLog
    , logSolve
    , logSolveComplete
    , logVerify
    , logRefine
    , logDumpLog
    , logLosingState
    , logCandidate
    , logSpec
    ) where

import Synthesise.GameTree
import Expression.Expression
import Expression.Compile
import Control.Monad.State
import Data.Maybe
import Data.List
import Utils.Utils
import qualified Debug.Trace as D

data SynthTrace = SynthTrace {
      input             :: GameTree
    , candidate         :: Maybe GameTree
    , prevLearned       :: [String]
    , learned           :: Maybe String
    , player            :: Player
    , result            :: Maybe GameTree
    , verification      :: [[SynthTrace]]
    , refinement        :: [SynthTrace]
}

instance Show SynthTrace where
    show st = "{ ver: " ++ concatMap show (verification st) ++ ", ref: " ++ concatMap show (refinement st) ++ "}"

data TraceCrumb = VerifyCrumb Int Int | RefineCrumb Int
    deriving (Show, Eq)

type LoggerT m = StateT (Maybe SynthTrace, [TraceCrumb], Maybe CompiledSpec) m

printLog :: LoggerT IO a -> IO (a)
printLog logger = do
    (r, (trace, _, spec)) <- runStateT logger (Nothing, [], Nothing)
    when (isJust trace && isJust spec) $ writeFile "debug.html" (htmlHeader ++ outputHTML (fromJust spec) (fromJust trace) ++ htmlFooter)
    return r

logDumpLog :: LoggerT IO ()
logDumpLog = do
    (trace, _, spec) <- get
    when (isJust trace && isJust spec) $ liftIO $ writeFile "debug_dump.html" (htmlHeader ++ outputHTML (fromJust spec) (fromJust trace) ++ htmlFooter)

htmlHeader = "<html><head>"
    ++ "<link rel=\"stylesheet\" href=\"debug.css\">"
    ++ "<script src=\"http://code.jquery.com/jquery-1.11.0.min.js\"></script>"
    ++ "<script src=\"http://code.jquery.com/jquery-migrate-1.2.1.min.js\"></script>"
    ++ "<script src=\"debug.js\"></script>"
    ++ "</head><body>"

htmlFooter = "</body></html>"

outputHTML spec trace = "<div class=\"trace " ++ show (player trace) ++ "\">"
    ++ "<h3><button type=\"button\" class=\"shrink\">-</button> Trace for " ++ (show (player trace)) ++ "</h3><hr />"
    ++ "<div class=\"input gametree\"><h3>Input GT</h3><pre>" ++ printTree spec (input trace) ++ "</pre></div>"
    ++ (if not (null (prevLearned trace))
        then "<div class=\"previousLearning\"><h3>Previously Learnt</h3><pre>" ++ intercalate " " (prevLearned trace) ++ "</pre></div>"
        else "")
    ++ "<div class=\"candidate gametree\"><h3>Candidate</h3><pre>" ++ maybe "Nothing" (printTree spec) (candidate trace) ++ "</pre></div>"
    ++ (if isJust (learned trace)
        then "<div class=\"learning\"><h3>Losing State</h3><pre>" ++ fromJust (learned trace) ++ "</pre></div>"
        else "")
    ++ "<div class=\"verifyRefineLoop\">" ++ verifyRefineLoopHTML spec (paddedZip (verification trace) (refinement trace)) ++ "</div>"
    ++ "<div class=\"result gametree\"><h3>Result</h3><pre>" ++ maybe "Nothing" (printTree spec) (result trace) ++ "</pre></div>"
    ++ "</div>"

verifyRefineLoopHTML spec [] = ""
verifyRefineLoopHTML spec ((vs, r):vrs)   = "<hr />"
    ++ verifyLoopHTML spec 1 vs
    ++ maybe "" (\x -> "<div class=\"refinement\"><h3>Refinement</h3>" ++ outputHTML spec x ++ "</div>") r
    ++ "<hr />"
    ++ verifyRefineLoopHTML spec vrs

verifyLoopHTML spec _ []     = ""
verifyLoopHTML spec i (v:vs) = "<div class=\"verification\"><h3>Verification " ++ show i ++ "</h3>" 
    ++ outputHTML spec v ++ "</div>" ++ verifyLoopHTML spec (i+1) vs

insertAt :: SynthTrace -> [TraceCrumb] -> SynthTrace -> SynthTrace
insertAt x [] t             = x
insertAt x ((VerifyCrumb c i):[]) t
    | c == length (verification t)  = t { verification = verification t ++ [[x]] }
    | c < length (verification t)   = t { verification = adjust (insVerify x i) c (verification t) }
    | otherwise                     = error $ "Error in Logger"
insertAt x ((RefineCrumb c):[]) t
    | c == length (refinement t)    = t { refinement = refinement t ++ [x] }
    | c < length (refinement t)     = t { refinement = adjust (\_ -> x) c (refinement t) }
    | otherwise                     = error $ "Error in Logger"
insertAt x ((VerifyCrumb c i):cs) t
    | null (verification t) = t { verification = [[x]] }
    | otherwise             = t { verification = adjust (adjust (insertAt x cs) i) c (verification t) }
insertAt x ((RefineCrumb c):cs) t   
    | null (refinement t)   = t { refinement = [x] }
    | otherwise             = t { refinement = adjust (insertAt x cs) c (refinement t) }

insVerify x i vs
    | i == length vs    = vs ++ [x]
    | i < length vs     = adjust (\_ -> x) i vs
    | otherwise         = error $ "Error in Logger"

follow trace []                     = trace
follow trace ((VerifyCrumb c i):cs) = follow ((verification trace !! c) !! i) cs
follow trace ((RefineCrumb c):cs)   = follow (refinement trace !! c) cs
    
updateAt :: (SynthTrace -> SynthTrace) -> [TraceCrumb] -> SynthTrace -> SynthTrace
updateAt f [] t                     = f t
updateAt f ((VerifyCrumb c i):cs) t = t { verification = adjust (adjust (updateAt f cs) i) c (verification t) }
updateAt f ((RefineCrumb c):cs) t   = t { refinement = adjust (updateAt f cs) c (refinement t) }

logSolve :: Monad m => GameTree -> Player -> [String] -> LoggerT m ()
logSolve gt player pLearn = do
    (trace, crumb, spec) <- get
    let newTrace = SynthTrace {
          input = gt
        , candidate = Nothing
        , prevLearned = pLearn
        , learned = Nothing
        , player = player
        , result = Nothing
        , verification = []
        , refinement = []
    }
    let trace' = if isJust trace
        then insertAt newTrace crumb (fromJust trace)
        else newTrace
    put (Just trace', crumb, spec)

logCandidate :: Monad m => Maybe GameTree -> LoggerT m ()
logCandidate cand = do
    (trace, crumb, spec) <- get
    put (Just $ updateAt (\t -> t { candidate = cand }) crumb (fromJust trace), crumb, spec)

logSolveComplete :: Monad m => Maybe GameTree -> LoggerT m ()
logSolveComplete gt = do
    (trace, crumb, spec) <- get
    let trace' = updateAt (\x -> x { result = gt }) crumb (fromJust trace)
    put (Just trace', if null crumb then [] else init crumb, spec)

logVerify :: Monad m => Int -> LoggerT m ()
logVerify i = do
    (trace, crumb, spec) <- get
    let currentTrace = follow (fromJust trace) crumb
    if i > 0
    then do
        put (trace, crumb ++ [VerifyCrumb ((length (verification currentTrace))-1) i], spec)
    else do
        put (trace, crumb ++ [VerifyCrumb (length (verification currentTrace)) i], spec)

logRefine :: Monad m => LoggerT m ()
logRefine = do
    (trace, crumb, spec) <- get
    let currentTrace = follow (fromJust trace) crumb
    put (trace, crumb ++ [RefineCrumb (length (refinement currentTrace))], spec)

logLosingState :: Monad m => String -> LoggerT m ()
logLosingState s = do
    (trace, crumb, spec) <- get
    put (Just $ updateAt (\t -> t { learned = Just s }) crumb (fromJust trace), crumb, spec)

logSpec :: Monad m => CompiledSpec -> LoggerT m ()
logSpec spec = do
    (trace, crumb, _) <- get
    put (trace, crumb, Just spec)
