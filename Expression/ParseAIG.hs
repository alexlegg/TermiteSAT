module Expression.ParseAIG (
    parser
    ) where

import Control.Monad
import Text.Read hiding (Symbol)
import Data.EitherR
import Expression.Parse(ParsedSpec)
import Expression.AST
import qualified Expression.HAST as HAST
import Text.Parsec hiding (space, spaces)

data AIG = AIG [Input] [Latch] [Output] [Gate]
    deriving (Show, Eq)

data Header = Header Int Int Int Int Int    deriving (Show, Eq)

data Input  = Input Int (Maybe String)      deriving (Show, Eq)
data Latch  = Latch Int Int (Maybe String)  deriving (Show, Eq)
data Output = Output Int (Maybe String)     deriving (Show, Eq)
data Gate   = Gate Int Int Int              deriving (Show, Eq)

data SymTyp = ISym Int | LSym Int | OSym Int
    deriving (Show, Eq)

data Symbol = Symbol SymTyp String
    deriving (Show, Eq)

parser :: String -> String -> Either String ParsedSpec
parser fn f = do
    file <- fmapL show $ parse aig fn f
    Left (show file)

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

