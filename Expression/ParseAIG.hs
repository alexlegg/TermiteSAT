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

data AIG = AIG [Input] [Latch] [Output] [Gate]
    deriving (Show, Eq)

data Header = Header Int Int Int Int Int    deriving (Show, Eq)

data Input  = Input Int (Maybe String)      deriving (Show, Eq)
data Latch  = Latch Int Int (Maybe String)  deriving (Show, Eq)
data Output = Output Int (Maybe String)     deriving (Show, Eq)
data Gate   = Gate Int Int Int              deriving (Show, Eq)

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

    let vMap    = zip varIds (map makeVarAST (iVars ++ lVars ++ oVars))
    let gates'  = makeGates vMap gates
    let ts      = map (makeLatch gates') latches

    let spec = ParsedSpec {
          init      = makeEqualsZero sVars
        , goal      = makeVarAST (head oVars)
        , ucont     = HAST.F
        , trans     = ts
        , stateVars = sVars
        , ucontVars = uVars
        , contVars  = cVars
        }

    Right spec

inputVarType Nothing                = UContVar
inputVarType (Just nm)
    | startswith "controllable_" nm = ContVar
    | otherwise                     = UContVar

makeInputVar (Input i n)    = makeVar (fromMaybe ("i" ++ show i) n) (inputVarType n) 1
makeLatchVar (Latch i _ n)  = makeVar (fromMaybe ("l" ++ show i) n) StateVar 1
makeOutputVar (Output i n)  = makeVar (fromMaybe ("o" ++ show i) n) StateVar 1

makeVar nm sect r = VarInfo {
      name      = nm
    , sz        = 1
    , section   = sect
    , slice     = Nothing
    , virank    = r
    , enum      = Nothing
    }

makeEqualsZero vars = HAST.Conj $ map (\v -> HAST.EqConst v 0) (map HAST.FVar vars)

makeVarAST var = HAST.Var (HAST.FVar var)

varId x | odd x     = x - 1
        | otherwise = x

makeGates :: [(Int, AST)] -> [Gate] -> [(Int, AST)]
makeGates done []       = done
makeGates done gates    = makeGates (done ++ map (gateId >< fromJust) done') (map fst gates')
    where
        loop            = map (makeGate done) gates
        (done', gates') = partition (isJust . snd) (zip gates loop)

makeGate done (Gate i x y) = case (x', y') of
    (Just xd, Just yd)  -> Just (HAST.And xd yd)
    _                   -> Nothing
    where
        x'  = lookupDone done x
        y'  = lookupDone done y

lookupDone done 0 = Just HAST.F
lookupDone done 1 = Just HAST.T
lookupDone done i = lookup (varId i) done

makeLatch done (Latch i x nm) = HAST.XNor var x'
    where
        var     = makeVarAST $ makeVar (fromMaybe ("l" ++ show i) nm) StateVar 0
        Just x' = lookupDone done x

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

