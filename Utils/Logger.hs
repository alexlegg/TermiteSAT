{-# LANGUAGE OverloadedStrings, RecordWildCards #-}
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
import Control.Monad
import Data.Maybe
import Data.List
import Data.String
import System.IO
import qualified Data.ByteString as BS
import Text.Blaze.Html5 as H
import Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.Utf8
import Utils.Utils
import qualified Debug.Trace as D

data SynthTrace = SynthTrace {
      inputGT           :: GameTree
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

data DebugMode = NoDebug | FinalLogOnly | DumpLogs deriving (Show, Eq)

data Log = Log {
      trace     :: Maybe SynthTrace
    , crumb     :: [TraceCrumb]
    , spec      :: Maybe CompiledSpec
    , debugMode :: DebugMode
    }

emptyLog dm = Log {
      trace     = Nothing
    , crumb     = []
    , spec      = Nothing
    , debugMode = case dm of
        0   -> NoDebug
        1   -> FinalLogOnly
        2   -> DumpLogs
    }

type LoggerT m = StateT Log m

printLog :: Int -> LoggerT IO a -> IO (a)
printLog dm logger = do
    (r, Log{..}) <- runStateT logger (emptyLog dm)
    when (debugMode /= NoDebug && isJust trace && isJust spec) $ do
        putStrLn "Printing final log to debug.html"
        withFile "debug.html" WriteMode $ \h -> do
            renderHtmlToByteStringIO (BS.hPut h) (outputLog (fromJust spec) (fromJust trace))
    return r

logDumpLog :: Int -> LoggerT IO ()
logDumpLog k = do
    Log{..} <- get
    let dumpFn = "debug" ++ (show k) ++ ".html"
    when (debugMode == DumpLogs && isJust trace && isJust spec) $ liftIO $ do
        withFile dumpFn WriteMode $ \h -> do
            renderHtmlToByteStringIO (BS.hPut h) (outputLog (fromJust spec) (fromJust trace))

outputLog spec trace = H.docTypeHtml $ do
    H.head $ do
        H.title "TermiteSAT Trace"
        link ! rel "stylesheet" ! href "debug.css"
        script ! src "http://code.jquery.com/jquery-1.11.0.min.js" $ ""
        script ! src "http://code.jquery.com/jquery-1.11.0.min.js" $ ""
        script ! src "http://code.jquery.com/jquery-migrate-1.2.1.min.js" $ ""
        script ! src "debug.js" $ ""
    H.body (outputTrace spec trace)
        
outputTrace spec trace = H.div ! class_ (fromString ("trace " ++ (show (player trace)))) $ do
    h3 $ do
        button ! type_ "button" ! class_ "shrink" $ "-"
        toHtml $ "Trace for " ++ show (player trace)
    hr
    H.div ! class_ "input gametree" $ do
        h3 "Input GT"
        pre $ toHtml (printTree spec (inputGT trace))

        when (not (null (prevLearned trace))) $ H.div ! class_ "previousLearning" $ do
            h3 "Previously Learnt"
            pre $ toHtml (intercalate "\n" (prevLearned trace))

        H.div ! class_ "candidate gametree" $ do
            h3 "Candidate"
            pre $ toHtml $ maybe "Nothing" (printTree spec) (candidate trace)

        when (isJust (learned trace)) $ H.div ! class_ "learning" $ do
            h3 "Losing States"
            pre $ toHtml $ fromJust (learned trace)

        H.div ! class_ "verifyRefineLoop" $ forM_ (paddedZip (verification trace) (refinement trace)) (outputVerifyRefine spec)

        H.div ! class_ "result gametree" $ do
            h3 "Result"
            pre $ toHtml (maybe "Nothing" (printTree spec) (result trace))

outputVerifyRefine spec (vs, r) = do
    hr
    forM_ (zip [0..] vs) $ \(i, v) -> do
        H.div ! class_ "verification" $ do
            h3 $ toHtml ("Verification " ++ show i)
            outputTrace spec v

    when (isJust r) $ H.div ! class_ "refinement" $ do
        h3 "Refinement"
        outputTrace spec (fromJust r)
    hr

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
    log@Log{..} <- get
    when (debugMode /= NoDebug) $ do
        let newTrace = SynthTrace {
              inputGT = gt
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
        put $ log { trace = Just trace' }

logCandidate :: Monad m => Maybe GameTree -> LoggerT m ()
logCandidate cand = do
    log@Log{..} <- get
    when (debugMode /= NoDebug) $ do
        put $ log { trace = Just $ updateAt (\t -> t { candidate = cand }) crumb (fromJust trace) }

logSolveComplete :: Monad m => Maybe GameTree -> LoggerT m ()
logSolveComplete gt = do
    log@Log{..} <- get
    when (debugMode /= NoDebug) $ do
        let trace' = updateAt (\x -> x { result = gt }) crumb (fromJust trace)
        put $ log { trace = Just trace', crumb = if null crumb then [] else init crumb }

logVerify :: Monad m => Int -> LoggerT m ()
logVerify i = do
    log@Log{..} <- get
    when (debugMode /= NoDebug) $ do
        let currentTrace = follow (fromJust trace) crumb
        if i > 0
        then do
            put $ log { crumb = crumb ++ [VerifyCrumb ((length (verification currentTrace))-1) i] }
        else do
            put $ log { crumb = crumb ++ [VerifyCrumb (length (verification currentTrace)) i] }

logRefine :: Monad m => LoggerT m ()
logRefine = do
    log@Log{..} <- get
    when (debugMode /= NoDebug) $ do
        let currentTrace = follow (fromJust trace) crumb
        put $ log { crumb = crumb ++ [RefineCrumb (length (refinement currentTrace))] }

logLosingState :: Monad m => String -> LoggerT m ()
logLosingState s = do
    log@Log{..} <- get
    when (debugMode /= NoDebug) $ do
        put $ log { trace = Just $ updateAt (\t -> t { learned = Just s }) crumb (fromJust trace) }

logSpec :: Monad m => CompiledSpec -> LoggerT m ()
logSpec cspec = do
    log@Log{..} <- get
    when (debugMode /= NoDebug) $ do
        put $ log { spec = Just cspec }
