{-# LANGUAGE ViewPatterns #-}
module Expression.ParseAIG (
    parser
    ) where

import Prelude hiding (init)
import Control.Monad
import Data.EitherR
import Data.Maybe
import Data.List hiding (init)
import Data.String.Utils
import Text.Parsec hiding (space, spaces)

import Utils.Utils
import qualified Expression.HAST as HAST
import Expression.Parse(ParsedSpec(..))
import Expression.AST

data AIG = AIG [Input] [Latch] [Output] [Gate]
    deriving (Show, Eq)

data Header = Header Int Int Int Int Int    deriving (Show, Eq)

data Input  = Input Int (Maybe String)      deriving (Show, Eq)
data Latch  = Latch Int Int (Maybe String)  deriving (Show, Eq)
data Output = Output Int (Maybe String)     deriving (Show, Eq)
data Gate   = Gate Int Int Int              deriving (Show, Eq)

gateToTuple :: Gate -> (Int, Int, Int)
gateToTuple (Gate x y z) = (x, y, z)

inputId :: Input -> Int
inputId (Input i _) = i

latchId :: Latch -> Int
latchId (Latch i _ _) = i

outputId :: Output -> Int
outputId (Output i _) = i

gateId :: Gate -> Int
gateId (Gate i _ _) = i

data SymTyp = ISym Int | LSym Int | OSym Int
    deriving (Show, Eq)

data Symbol = Symbol SymTyp String
    deriving (Show, Eq)

parser :: String -> String -> Either String ParsedSpec
parser fn f = do
    (AIG inputs latches outputs gates) <- fmapL show $ parse aig fn f

    let iVars   = map makeInputVar inputs
    let lVars   = map makeLatchVar latches
    let oVars   = map makeOutputVar outputs

    let sVars           = lVars ++ oVars
    let (cVars, uVars)  = partition ((==) ContVar . section) iVars
    
    let varIds  =   map inputId inputs
                ++  map latchId latches
                ++  map outputId outputs

    let vMap    = zip varIds (map makeVarAST (iVars ++ lVars))
    let gates'' = gates -- preprocess gates
    let gates'  = makeGates vMap gates''
    let ts      = map (makeLatch gates') latches
    let o       = makeOutput gates' (head outputs)

    let aigLatches (Latch i x nm)   = (makeVarAST (makeVar (varName "_l" i nm) StateVar 0), x)
    let aigOutput (Output i n)      = (makeVarAST (makeVar (varName "_o" i n) StateVar 0), i)

    let spec = ParsedSpec {
          initial   = zip sVars (repeat 0)
        , goal      = makeVarAST (head oVars)
        , ucont     = Nothing
        , trans     = ts ++ [o]
        , aigTrans  = Just (map aigLatches latches ++ map aigOutput outputs, map gateToTuple gates)
        , aigVars   = Just vMap
        , stateVars = sVars
        , ucontVars = uVars
        , contVars  = cVars
        }

    Right spec

inputVarType :: Maybe String -> Section
inputVarType Nothing                = UContVar
inputVarType (Just nm)
    | startswith "controllable_" nm = UContVar
    | otherwise                     = ContVar

makeInputVar :: Input -> VarInfo
makeInputVar (Input i n) = makeVar (varName "_i" i n) (inputVarType n) 1

makeLatchVar :: Latch -> VarInfo
makeLatchVar (Latch i _ n) = makeVar (varName "_l" i n) StateVar 1

makeOutputVar :: Output -> VarInfo
makeOutputVar (Output i n) = makeVar (varName "_o" i n) StateVar 1

varName :: String -> Int -> Maybe String -> String
varName pre i nm = fromMaybe "" nm ++ pre ++ show i

makeVar :: String -> Section -> Int -> VarInfo
makeVar nm sect r = VarInfo {
      name      = fromMaybe nm (stripPrefix "controllable_" nm)
    , sz        = 1
    , section   = sect
    , slice     = Nothing
    , virank    = r
    , enum      = Nothing
    }

makeVarAST :: VarInfo -> HAST.AST VarInfo e c v
makeVarAST var = HAST.Var (HAST.FVar var)

varId :: Int -> Int
varId x | odd x     = x - 1
        | otherwise = x

makeGates :: [(Int, AST)] -> [Gate] -> [(Int, AST)]
makeGates done []       = done
makeGates done gates    = makeGates (done ++ map (gateId >< fromJust) done') (map fst gates')
    where
        loop            = map (makeGate done) gates
        (done', gates') = partition (isJust . snd) (zip gates loop)

setSign :: Int -> HAST.AST VarInfo e c v -> HAST.AST VarInfo e c v
setSign x ast | x <= 1      = ast
              | odd x       = HAST.Not ast
              | otherwise   = ast

makeGate :: [(Int, HAST.AST VarInfo e c v)] -> Gate -> Maybe (HAST.AST VarInfo e c v)
makeGate done (Gate _ x y) = case (x', y') of
    (Just xd, Just yd)  -> Just (HAST.And (setSign x xd) (setSign y yd))
    _                   -> Nothing
    where
        x'  = lookupDone done x
        y'  = lookupDone done y

lookupDone :: [(Int, HAST.AST f e c v)] -> Int -> Maybe (HAST.AST f e c v)
lookupDone _ 0      = Just HAST.F
lookupDone _ 1      = Just HAST.T
lookupDone done i   = lookup (varId i) done

makeLatch :: [(Int, HAST.AST VarInfo e c v)] -> Latch -> HAST.AST VarInfo e c v
makeLatch done (Latch i x nm) = HAST.XNor var (setSign x x')
    where
        var     = makeVarAST $ makeVar (varName "_l" i nm) StateVar 0
        Just x' = lookupDone done x

makeOutput :: [(Int, HAST.AST VarInfo e c v)] -> Output -> HAST.AST VarInfo e c v
makeOutput done (Output i nm) = HAST.XNor var (setSign i x')
    where
        var     = makeVarAST $ makeVar (varName "_o" i nm) StateVar 0
        Just x' = lookupDone done i

-- AIG Parsing

aig :: Monad m => ParsecT String u m AIG
aig = do
    Header _ i l o a    <- header
    inputs              <- count i input
    latches             <- count l latch
    outputs             <- count o output
    gates               <- count a gate
    symbols             <- many symbol

    let symTab          = map makeSymTab symbols
    let inputs'         = zipWith (setSymbol symTab) (map ISym [0..]) inputs
    let latches'        = zipWith (setSymbol symTab) (map LSym [0..]) latches
    let outputs'        = zipWith (setSymbol symTab) (map OSym [0..]) outputs

    return $ AIG inputs' latches' outputs' gates

header :: Monad m => ParsecT String u m Header
header = Header <$ string "aag" <* spaces
    <*> number <* spaces
    <*> number <* spaces
    <*> number <* spaces
    <*> number <* spaces
    <*> number <* eol

makeSymTab :: Symbol -> (SymTyp, String)
makeSymTab (Symbol t n) = (t, n)

setSymbol :: [(SymTyp, String)] -> SymTyp -> (Maybe String -> a) -> a
setSymbol st i f = f (lookup i st)

input :: Monad m => ParsecT String u m (Maybe String -> Input)
input = Input <$> number <* eol

latch :: Monad m => ParsecT String u m (Maybe String -> Latch)
latch = Latch <$> number <* spaces <*> number <* eol

output :: Monad m => ParsecT String u m (Maybe String -> Output)
output = Output <$> number <* eol

gate :: Monad m => ParsecT String u m Gate
gate = Gate <$> number <* spaces <*> number <* spaces <*> number <* eol

symbol :: Monad m => ParsecT String u m Symbol
symbol  = Symbol <$> (iSymbol <|> lSymbol <|> oSymbol) <* spaces <*> identifier <* eol

iSymbol :: Monad m => ParsecT String u m SymTyp
iSymbol = ISym <$ char 'i' <*> number

lSymbol :: Monad m => ParsecT String u m SymTyp
lSymbol = LSym <$ char 'l' <*> number

oSymbol :: Monad m => ParsecT String u m SymTyp
oSymbol = OSym <$ char 'o' <*> number

space :: Monad m => ParsecT String u m Char
space = satisfy isSpace <?> "space"

spaces :: Monad m => ParsecT String u m ()
spaces = skipMany space <?> "white space"

eol :: Monad m => ParsecT String u m ()
eol = spaces <* endOfLine

number :: Monad m => ParsecT String u m Int
number = liftM read (many1 digit)

identifier :: Monad m => ParsecT String u m String
identifier = many1 (noneOf "\n\r")

-- Definition is different than normal, we don't want to consume newlines
isSpace :: Char -> Bool
isSpace ' '     = True
isSpace '\t'    = True
isSpace _       = False
