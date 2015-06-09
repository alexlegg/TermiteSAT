{-# LANGUAGE OverloadedStrings, RecordWildCards #-}
module Utils.Logger (
      LoggerT(..)
    , printLog
    , logSolve
    , logSolveComplete
    , logVerify
    , logRefine
    , logRank
    , logRankAux
    , logDumpLog
    , logLosingState
    , logCandidate
    , logLostInPrefix
    , logSpec
    ) where

import Synthesise.GameTree
import Expression.Expression
import Expression.Compile
import Control.Monad.State
import Control.Monad
import Data.Maybe
import Data.List as L
import Data.String
import qualified Data.Set as Set
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
    , learned           :: [Set.Set Assignment]
    , lostInPrefix      :: Maybe Bool
    , player            :: Player
    , result            :: Maybe GameTree
    , verification      :: [[SynthTrace]]
    , refinement        :: [SynthTrace]
}

instance Show SynthTrace where
    show st = "{ ver: " ++ concatMap show (verification st) ++ ", ref: " ++ concatMap show (refinement st) ++ "}"

data TraceCrumb = VerifyCrumb Int Int | RefineCrumb Int
    deriving (Show, Eq)

data DebugMode = NoDebug | FinalLogOnly | LogEachRank | DumpLogs deriving (Show, Eq)

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
        3   -> LogEachRank
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

logRank :: Int -> LoggerT IO ()
logRank k = do
    Log{..} <- get
    let dumpFn = "debug" ++ (show k) ++ ".html"
    when (debugMode == LogEachRank && isJust trace && isJust spec) $ liftIO $ do
        withFile dumpFn WriteMode $ \h -> do
            renderHtmlToByteStringIO (BS.hPut h) (outputLog (fromJust spec) (fromJust trace))

logRankAux :: Int -> Int -> LoggerT IO ()
logRankAux k a = do
    Log{..} <- get
    let dumpFn = "debug_aux" ++ show k ++ "_" ++ show a ++ ".html"
    when (debugMode == LogEachRank && isJust trace && isJust spec) $ liftIO $ do
        withFile dumpFn WriteMode $ \h -> do
            renderHtmlToByteStringIO (BS.hPut h) (outputLog (fromJust spec) (fromJust trace))

logDumpLog :: LoggerT IO ()
logDumpLog = do
    Log{..} <- get
    let dumpFn = "debug.html"
    when (debugMode == DumpLogs && isJust trace && isJust spec) $ liftIO $ do
        withFile dumpFn WriteMode $ \h -> do
            renderHtmlToByteStringIO (BS.hPut h) (outputLog (fromJust spec) (fromJust trace))

outputLog spec trace = H.docTypeHtml $ do
    H.head $ do
        H.title "TermiteSAT Trace"
        link ! rel "stylesheet" ! href "debug.css"
        link ! rel "stylesheet" ! href "http://code.jquery.com/ui/1.11.4/themes/ui-lightness/jquery-ui.css"
        script ! src "http://code.jquery.com/jquery-1.11.3.min.js" $ ""
        script ! src "http://code.jquery.com/jquery-migrate-1.2.1.min.js" $ ""
        script ! src "http://code.jquery.com/ui/1.11.3/jquery-ui.min.js" $ ""
        script ! src "debug.js" $ ""
    H.body $ do
        H.div ! A.id "options" $ img ! src "options.png"
        H.div ! A.id "optionsVarnames" $ do
            let getNames = nub . sort . (L.map varname)
            let allVars = getNames (svars spec) ++ getNames (cont spec) ++ getNames (ucont spec)
            toHtml $ intercalate ", " (L.map sanitise allVars)
        H.div ! A.id "optionsDialog" $ "Select variables to show/hide"
        outputTrace spec trace
        
outputTrace spec trace = H.div ! class_ (fromString ("trace " ++ (show (player trace)))) $ do
    h3 $ do
        button ! type_ "button" ! class_ "shrink" $ "-"
        toHtml $ "Trace for " ++ show (player trace)
    hr
    H.div ! class_ "input gametree" $ do
        h3 "Input GT"
        br
        outputTree spec (gtRoot (inputGT trace))
        br

---        when (not (null (prevLearned trace))) $ H.div ! class_ "previousLearning" $ do
---            h3 "Previously Learnt"
---            pre $ toHtml (intercalate "\n" (prevLearned trace))

        H.div ! class_ "candidate gametree" $ do
            h3 "Candidate"
            br
            case candidate trace of
                Nothing     -> "Nothing"
                Just tree   -> outputTree spec (gtRoot tree)
            br

        when (not (null (learned trace))) $ H.div ! class_ "learning" $ do
            h3 "Losing States"
            if (lostInPrefix trace == Just True)
                then "Lost in Prefix"
                else pre $ toHtml $ intercalate "\n" $ L.map (printMove spec . Just . Set.toList) (learned trace)

        H.div ! class_ "verifyRefineLoop" $ forM_ (paddedZip (verification trace) (refinement trace)) (outputVerifyRefine spec)

        H.div ! class_ "result gametree" $ do
            h3 "Result"
            br
            case result trace of
                Nothing     -> "Nothing"
                Just tree   -> outputTree spec (gtRoot tree)
            br

sanitise = filter (\c -> c /= '<' && c /= '>')

outputVar spec v = do
    H.span ! class_ (toValue ("var_" ++ sanitise vname)) $ toHtml (printVar spec v)
    where
        vname = let (Assignment _ vi) = (L.head v) in varname vi

outputMove spec Nothing = "Nothing" >> return ()
outputMove spec (Just m) = do
    mapM_ (outputVar spec) (groupMoveVars m)

groupMoveVars as = groupBy f (sortBy g as)
    where
        f (Assignment _ x) (Assignment _ y) = varname x == varname y
        g (Assignment _ x) (Assignment _ y) = compare (varname x) (varname y)

outputTree spec gt = do
    H.div ! class_ "tree" $ do
        case gtPlayer gt of
            Existential -> "E "
            Universal   -> "U "
        when (gtPlayer gt == Universal && gtExWins gt == Just True) $ "EXWINS: "
        outputMove spec (gtMove gt)
        when (gtPlayer gt == Universal) $ do
            " | "
            outputMove spec (gtState gt)
        mapM_ (outputTree spec) (gtChildren gt)

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
            , learned = []
            , lostInPrefix = Nothing
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

logLosingState :: Monad m => [Assignment] -> LoggerT m ()
logLosingState s = do
    log@Log{..} <- get
    return ()
    when (debugMode /= NoDebug) $ do
        put $ log { trace = Just $ updateAt (\t -> t { learned = learned t ++ [Set.fromList s] }) crumb (fromJust trace) }

logLostInPrefix :: Monad m => LoggerT m ()
logLostInPrefix = do
    log@Log{..} <- get
    return ()
    when (debugMode /= NoDebug) $ do
        put $ log { trace = Just $ updateAt (\t -> t { lostInPrefix = Just True }) crumb (fromJust trace) }

logSpec :: Monad m => CompiledSpec -> LoggerT m ()
logSpec cspec = do
    log@Log{..} <- get
    when (debugMode /= NoDebug) $ do
        put $ log { spec = Just cspec }
