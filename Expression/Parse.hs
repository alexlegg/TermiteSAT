{-# LANGUAGE GADTs, RecordWildCards, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Expression.Parse (
    Decl(..),
    Type(..),
    ParsedSpec(..),
    parser
    ) where

import Control.Applicative
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.String
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Data.Functor
import Data.Foldable hiding (concat, concatMap)
import Data.Traversable hiding (mapM)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Bits
import Control.Monad
import Data.EitherR
import Control.Arrow
import Debug.Trace

import qualified Expression.HAST as HAST
import Expression.AST

data ParsedSpec = ParsedSpec {
    init        :: AST, 
    goal        :: AST, 
    ucont       :: AST, 
    trans       :: [AST],
    stateVars   :: [VarInfo],
    ucontVars   :: [VarInfo],
    contVars    :: [VarInfo]
    }

data Type where
    BoolType ::             Type
    IntType  :: Int      -> Type
    EnumType :: [String] -> Type

data Decl = Decl {
    vars    :: [String],
    varType :: Type
}

data Decls = Decls {
    stateDecls   :: [Decl],
    labelDecls   :: [Decl],
    outcomeDecls :: [Decl]
}

data Rels a = Rels {
    initR        :: BinExpr a,
    goalR        :: [BinExpr a],
    fair         :: [BinExpr a],
    cont         :: BinExpr a,
    slRel        :: BinExpr a,
    transR       :: CtrlExpr String a
}

data Spec = Spec {
    decls :: Decls,
    rels  :: Rels (Either (String, Slice) Int)
}

--The transition section
data CtrlExpr a v where
    Assign :: a -> ValExpr v                   -> CtrlExpr a v
    Signal :: String -> ValExpr v              -> CtrlExpr a v
    CaseC  :: [(BinExpr v, CtrlExpr a v)]      -> CtrlExpr a v
    Conj   :: [CtrlExpr a v]                   -> CtrlExpr a v
    deriving (Show, Functor, Foldable, Traversable)

data ValExpr v where
    Lit       :: v                             -> ValExpr v
    CaseV     :: [(BinExpr v, ValExpr v)]      -> ValExpr v
    deriving (Show, Functor, Foldable, Traversable)

data BinOpType = And | Or deriving (Show)
data PredType  = Eq | Neq deriving (Show)

data BinExpr v where
    TrueE  ::                                        BinExpr v
    FalseE ::                                        BinExpr v
    Not    :: BinExpr v                           -> BinExpr v
    Bin    :: BinOpType -> BinExpr v -> BinExpr v -> BinExpr v
    Pred   :: PredType -> ValExpr v -> ValExpr v  -> BinExpr v
    deriving (Show, Functor, Foldable, Traversable)

parser fn f = do
    (Spec Decls{..} Rels{..}) <- fmapL show $ parse top fn f
    let theMap = case (doDecls stateDecls labelDecls outcomeDecls) of
                    Left s -> error s
                    Right m -> m
    Rels{..} <- Rels <$> resolve theMap initR
                     <*> mapM (resolve theMap) goalR
                     <*> mapM (resolve theMap) fair
                     <*> resolve theMap cont
                     <*> resolve theMap slRel
                     <*> resolve theMap transR

    Right ParsedSpec { init         = binExprToHAST initR
                     , goal         = head (map binExprToHAST goalR)
                     , ucont        = head (map binExprToHAST fair)
                     , trans        = map (resolveTransLHS theMap) (ctrlExprToHAST transR)
                     , stateVars    = concatMap (declToVarInfo StateVar) stateDecls
                     , ucontVars    = concatMap (declToVarInfo UContVar) outcomeDecls
                     , contVars     = concatMap (declToVarInfo ContVar) labelDecls
                     }

declToVarInfo sect decl = map mk (vars decl)
    where 
        size = case varType decl of
                BoolType        -> 1
                IntType sz      -> sz
                EnumType es     -> ceiling (logBase 2 (fromIntegral (length es)))
        mk n = VarInfo {
                  name      = n
                , sz        = size
                , section   = sect
                , slice     = Nothing
                , virank    = 0
            }

resolveTransLHS st (s, f) = f v
    where
        v = VarInfo {
            name = s,
            sz = sz,
            section = sect,
            slice = Nothing,
            virank = 0 }
        (sect, sz) = case Map.lookup s st of
            Nothing                 -> error "LHS of transition relation not in sym tab"
            Just (Left (se, sz))    -> (se, sz)
            Just (Right sz)         -> error ("LHS of transition relation right: " ++ show sz)

--The lexer
reservedNames = ["case", "true", "false", "else", "abs", "conc", "uint", "bool"]
reservedOps   = ["!", "&&", "||", "!=", "==", ":=", "<="]

--Variable types
boolTyp   t@T.TokenParser{..} = BoolType <$  reserved "bool"
intTyp    t@T.TokenParser{..} = IntType  <$  reserved "uint" <*> angles (fromIntegral <$> natural)
enumTyp   t@T.TokenParser{..} = EnumType <$> braces (sepBy identifier comma)
typ       t@T.TokenParser{..} = boolTyp t <|> intTyp t <|> enumTyp t

--Variable declarations
decl      t@T.TokenParser{..} = Decl <$> (sepBy identifier comma <* colon) <*> typ t
---decl      t@T.TokenParser{..} = Decl <$> sepBy identifier comma <* colon <*> absTypes t <*> typ t

--Expressions

--The Bin expression parser
binExpr   t@T.TokenParser{..} =   buildExpressionParser (table t) (term t)
                              <?> "expression"

predicate t@T.TokenParser{..} =   try (Pred Eq  <$> valExpr t <* reservedOp "==" <*> valExpr t)
                              <|> try (Pred Neq <$> valExpr t <* reservedOp "!=" <*> valExpr t)

term      t@T.TokenParser{..} =   parens (binExpr t)
                              <|> TrueE <$ (reserved "true"  <|> reserved "else")
                              <|> FalseE <$ reserved "false"
                              <|> try (predicate t)
                              <?> "simple expression"

table     t@T.TokenParser{..} = [[prefix t "!"  Not]
                                ,[binary t  "&&" (Bin And) AssocLeft]
                                ,[binary t  "||" (Bin Or)  AssocLeft]
                                ]

binary    t@T.TokenParser{..} name fun assoc = Infix  (fun <$ reservedOp name) assoc
prefix    t@T.TokenParser{..} name fun       = Prefix (fun <$ reservedOp name) 

--Control expressions
assign    t@T.TokenParser{..} = Assign <$> identifier <* reservedOp ":=" <*> valExpr t
signal    t@T.TokenParser{..} = Signal <$> identifier <* reservedOp "<=" <*> valExpr t
ccase     t@T.TokenParser{..} = CaseC  <$  reserved "case" <*> braces (sepEndBy ((,) <$> binExpr t <* colon <*> ctrlExpr t) semi)
conj      t@T.TokenParser{..} = Conj   <$> braces (sepEndBy (ctrlExpr t) semi)
ctrlExpr  t@T.TokenParser{..} = conj t <|> ccase t <|> try (assign t) -- <|> signal t

--Value expressions

pslice    t@T.TokenParser{..} = brackets $ f <$> integer <*> optionMaybe (colon *> integer)
    where
    f start Nothing    = (fromIntegral start, fromIntegral start)
    f start (Just end) = (fromIntegral start, fromIntegral end)
slicedVar t@T.TokenParser{..} = (,) <$> identifier <*> optionMaybe (pslice t)

lit       t@T.TokenParser{..} = Lit   <$> ((Left <$> slicedVar t) <|> ((Right . fromIntegral) <$> integer))
vcase     t@T.TokenParser{..} = CaseV <$  reserved "case" <*> braces (sepEndBy ((,) <$> binExpr t <* colon <*> valExpr t) semi)
valExpr   t@T.TokenParser{..} = vcase t <|> lit t


stdDef = emptyDef {T.reservedNames = reservedNames 
                  ,T.reservedOpNames = reservedOps
                  ,T.identStart = letter <|> char '_'
                  ,T.identLetter = alphaNum <|> char '_'
                  ,T.commentStart = "/*"
                  ,T.commentEnd = "*/"
                  ,T.commentLine = "//"
                  }

lexer = T.makeTokenParser (stdDef {T.reservedNames = T.reservedNames stdDef ++ ["STATE", "LABEL", "OUTCOME", "INIT", "GOAL", "TRANS", "FAIR", "CONT", "LABELCONSTRAINTS"]})

T.TokenParser {..} = lexer

parseDecls = Decls
    <$  reserved "STATE"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "LABEL"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "OUTCOME"
    <*> sepEndBy (decl lexer) semi

parseRels = Rels
    <$  reserved "INIT"
    <*> binExpr lexer
    <*  reserved "GOAL"
    <*> sepEndBy (binExpr lexer) semi
    <*  reserved "FAIR"
    <*> sepEndBy (binExpr lexer) semi
    <*  reserved "CONT"
    <*> binExpr lexer
    <*  reserved "LABELCONSTRAINTS"
    <*> binExpr lexer
    <*  reserved "TRANS"
    <*> (Conj <$> sepEndBy (ctrlExpr lexer) semi)

spec = Spec <$> parseDecls <*> parseRels

top = whiteSpace *> (spec <* eof)

type SymTab = Map String (Either (Section, Int) Int)

resolve :: (Traversable t) => SymTab -> t (Either (String, Slice) Int) -> Either String (t (Either VarInfo Int))
resolve = traverse . func

func :: SymTab -> Either (String, Slice) Int -> Either String (Either VarInfo Int)
func mp lit = case lit of 
    Left (str, slice) -> case Map.lookup str mp of
        Nothing                     -> Left  $ "Var doesn't exist: " ++ str
        Just (Left (sect, sz)) -> Right $ Left $ VarInfo str sz sect slice 1
        Just (Right c)              -> Right $ Right $ getBits slice c
    Right x -> Right $ Right x

constructSymTab :: (Ord a) => [(a, b)] -> Either a (Map a b)
constructSymTab = foldM func (Map.empty) 
    where
    func mp (key, val) = case Map.lookup key mp of
        Nothing -> Right $ Map.insert key val mp
        Just _  -> Left key

doDecls :: [Decl] -> [Decl] -> [Decl] -> Either String SymTab
doDecls sd ld od = fmapL ("Variable already exists: " ++) $ constructSymTab $ concat [concatMap (go StateVar) sd, concatMap (go ContVar) ld, concatMap (go UContVar) od]
    where
    go sect (Decl vars vtype) = concatMap go' vars
        where
        go' var = (var, Left (sect, sz)) : map (second Right) consts
        sz      = doTypeSz vtype
        consts  = doTypeconsts vtype

--Logarithm to base 2. Equivalent to floor(log2(x))
log2 :: Int -> Int
log2 0 = 0
log2 1 = 0
log2 n 
    | n>1 = 1 + log2 (n `div` 2)
    | otherwise = error "log2: negative argument"

typeSize :: Int -> Int
typeSize 0 = error "Enum with no items"
typeSize 1 = error "Enum with one item"
typeSize i = 1 + log2 (i - 1)

doTypeSz BoolType      = 1
doTypeSz (IntType n)   = n
doTypeSz (EnumType es) = typeSize $ length es

doTypeconsts BoolType      = []
doTypeconsts (IntType n)   = []
doTypeconsts (EnumType es) = zip es [0..]

getBits :: Slice -> Int -> Int
getBits Nothing x       = x
getBits (Just (l, u)) x = (shift (-l) x) .&. (2 ^ (u - l + 1) - 1)

predToHAST :: ValExpr (Either VarInfo Int) -> ValExpr (Either VarInfo Int) -> AST
predToHAST (Lit (Right a)) (Lit (Right b))   = if (a == b) then HAST.T else HAST.F
predToHAST (Lit (Left a)) (Lit (Right b))    = HAST.EqConst (HAST.NVar a) b
predToHAST (Lit (Right a)) (Lit (Left b))    = HAST.EqConst (HAST.NVar b) a
predToHAST (Lit (Left a)) (Lit (Left b))     = HAST.EqVar (HAST.NVar a) (HAST.NVar b)

binExprToHAST :: BinExpr (Either VarInfo Int) -> AST
binExprToHAST TrueE             = HAST.T
binExprToHAST FalseE            = HAST.F
binExprToHAST (Not e)           = HAST.Not (binExprToHAST e)
binExprToHAST (Bin And a b)     = HAST.And (binExprToHAST a) (binExprToHAST b)
binExprToHAST (Bin Or a b)      = HAST.Or (binExprToHAST a) (binExprToHAST b)
binExprToHAST (Pred Eq a b)     = predToHAST a b
binExprToHAST (Pred Neq a b)    = HAST.Not (predToHAST a b)

ctrlExprToHAST :: CtrlExpr String (Either VarInfo Int) -> [(String, (VarInfo -> AST))]
ctrlExprToHAST (Assign var val) = [(var, valExprToHAST val)]
ctrlExprToHAST (Conj cs)        = concatMap ctrlExprToHAST cs
ctrlExprToHAST (Signal var val) = error "Signal not implemented"
ctrlExprToHAST (CaseC cs)       = error "CaseC not implemented"

valExprToHAST :: ValExpr (Either VarInfo Int) -> (VarInfo -> AST)
valExprToHAST (Lit (Left a))    = (\x -> HAST.EqVar (HAST.FVar x) (HAST.NVar a))
valExprToHAST (Lit (Right a))   = (\x -> HAST.EqConst (HAST.FVar x) a)
valExprToHAST (CaseV cases)     = f
    where
        bs = map (binExprToHAST . fst) cases
        vs = map (valExprToHAST . snd) cases
        f x = HAST.Case (zip bs (map ($ x) vs))

