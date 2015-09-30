{-# LANGUAGE ViewPatterns #-}
module Expression.ParseAIG (
    parser
    ) where

import Prelude hiding (init)
import Control.Monad
import Text.Read hiding (Symbol)
import Data.EitherR
import Data.Maybe
import Data.List hiding (init)
import Data.String.Utils
import Expression.Parse(ParsedSpec(..))
import Expression.AST
import qualified Expression.HAST as HAST
import Text.Parsec hiding (space, spaces)
import Utils.Utils
import Debug.Trace

data AIG = AIG [Input] [Latch] [Output] [Gate]
    deriving (Show, Eq)

data Header = Header Int Int Int Int Int    deriving (Show, Eq)

data Input  = Input Int (Maybe String)      deriving (Show, Eq)
data Latch  = Latch Int Int (Maybe String)  deriving (Show, Eq)
data Output = Output Int (Maybe String)     deriving (Show, Eq)
data Gate   = Gate Int Int Int              deriving (Show, Eq)

gateToTuple (Gate x y z) = (x, y, z)

inputId (Input i _)     = i
latchId (Latch i _ _)   = i
outputId (Output i _)   = i
gateId (Gate i _ _)     = i

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
          init      = makeEqualsZero sVars
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

inputVarType Nothing                = UContVar
inputVarType (Just nm)
    | startswith "controllable_" nm = UContVar
    | otherwise                     = ContVar

makeInputVar (Input i n)    = makeVar (varName "_i" i n) (inputVarType n) 1
makeLatchVar (Latch i _ n)  = makeVar (varName "_l" i n) StateVar 1
makeOutputVar (Output i n)  = makeVar (varName "_o" i n) StateVar 1

varName pre i nm = fromMaybe "" nm ++ pre ++ show i

makeVar nm sect r = VarInfo {
      name      = fromMaybe nm (stripPrefix "controllable_" nm)
    , sz        = 1
    , section   = sect
    , slice     = Nothing
    , virank    = r
    , enum      = Nothing
    }

makeEqualsZero vars = map (\v -> (v, 0)) vars

makeVarAST var = HAST.Var (HAST.FVar var)

varId x | odd x     = x - 1
        | otherwise = x

makeGates :: [(Int, AST)] -> [Gate] -> [(Int, AST)]
makeGates done []       = done
makeGates done gates    = makeGates (done ++ map (gateId >< fromJust) done') (map fst gates')
    where
        loop            = map (makeGate done) gates
        (done', gates') = partition (isJust . snd) (zip gates loop)

setSign x ast | x <= 1      = ast
              | odd x       = HAST.Not ast
              | otherwise   = ast

makeGate done (Gate i x y) = case (x', y') of
    (Just xd, Just yd)  -> Just (HAST.And (setSign x xd) (setSign y yd))
    _                   -> Nothing
    where
        x'  = lookupDone done x
        y'  = lookupDone done y

lookupDone done 0 = Just HAST.F
lookupDone done 1 = Just HAST.T
lookupDone done i = lookup (varId i) done

makeLatch done (Latch i x nm) = HAST.XNor var (setSign x x')
    where
        var     = makeVarAST $ makeVar (varName "_l" i nm) StateVar 0
        Just x' = lookupDone done x

makeOutput done (Output i nm) = HAST.XNor var (setSign i x')
    where
        var     = makeVarAST $ makeVar (varName "_o" i nm) StateVar 0
        Just x' = lookupDone done i

-- AIG Parsing

aig = do
    Header m i l o a    <- header
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

header = Header <$ string "aag" <* spaces
    <*> number <* spaces
    <*> number <* spaces
    <*> number <* spaces
    <*> number <* spaces
    <*> number <* eol

makeSymTab (Symbol t n) = (t, n)

setSymbol :: [(SymTyp, String)] -> SymTyp -> (Maybe String -> a) -> a
setSymbol st i f = f (lookup i st)

input   = Input <$> number <* eol
latch   = Latch <$> number <* spaces <*> number <* eol
output  = Output <$> number <* eol
gate    = Gate <$> number <* spaces <*> number <* spaces <*> number <* eol

symbol  = Symbol <$> (iSymbol <|> lSymbol <|> oSymbol) <* spaces <*> identifier <* eol

iSymbol = ISym <$ char 'i' <*> number
lSymbol = LSym <$ char 'l' <*> number
oSymbol = OSym <$ char 'o' <*> number

space       = satisfy isSpace <?> "space"
spaces      = skipMany space <?> "white space"
eol         = spaces <* endOfLine
number      = liftM read (many1 digit)
identifier  = many1 (noneOf "\n\r")

-- Definition is different than normal, we don't want to consume newlines
isSpace ' '     = True
isSpace '\t'    = True
isSpace _       = False

preprocess gates = map replaceAll gates
    where
        rMap                    = catMaybes (map findSingleGates gates)
        gateInd (Gate i _ _)    = i
        replaceAll (Gate i x y) = Gate i (replace x) (replace y)
        fixSign x x'            
            | odd x && odd x'   = x' - 1
            | odd x && even x'  = x' + 1
            | even x            = x'
        replace x               = case (lookup (varId x) rMap) of
                                    Just x' -> fixSign x x'
                                    Nothing -> x

findSingleGates (Gate i x y) = if x == y then Just (i, x) else Nothing

printHAST HAST.T = "T"
printHAST HAST.F = "F"
printHAST (HAST.And a b)    = "(" ++ printHAST a ++ " && " ++ printHAST b ++ ")"
printHAST (HAST.Not x)      = "not(" ++ printHAST x ++ ")"
printHAST (HAST.XNor a b)   = printHAST a ++ " := " ++ printHAST b
printHAST (HAST.Var (HAST.FVar x))  = (name x)
