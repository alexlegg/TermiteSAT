{-# LANGUAGE GADTs, RecordWildCards, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Expression.Parse (
    Decl(..),
    Type(..),
    ParsedSpec(..),
    parser
    ) where

import Control.Applicative hiding (optional)
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Data.Functor.Identity
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Bits
import Control.Monad
import Data.EitherR
import Control.Arrow

import qualified Expression.HAST as HAST
import Expression.AST

data ParsedSpec = ParsedSpec {
    initial     :: [(VarInfo, Int)], 
    goal        :: AST, 
    ucont       :: Maybe AST, 
    trans       :: [AST],
    aigTrans    :: Maybe ([(AST, Int)], [(Int, Int, Int)]),
    aigVars     :: Maybe [(Int, AST)],
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
    initR        :: [AssignmentExpr String],
    goalR        :: [BinExpr a],
    fair         :: Maybe [BinExpr a],
    transR       :: CtrlExpr String a
}

data Spec = Spec Decls (Rels (Either (String, Slice) Int))

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

data BinOpType = And | Or | LogEq deriving (Show)
data PredType  = Eq | Neq deriving (Show)

data BinExpr v where
    TrueE  ::                                        BinExpr v
    FalseE ::                                        BinExpr v
    Not    :: BinExpr v                           -> BinExpr v
    Bin    :: BinOpType -> BinExpr v -> BinExpr v -> BinExpr v
    Pred   :: PredType -> ValExpr v -> ValExpr v  -> BinExpr v
    deriving (Show, Functor, Foldable, Traversable)

data AssignmentExpr a = AssignmentExpr a Int

parser :: SourceName -> String -> Either String ParsedSpec
parser fn f = do
    (Spec decls rels) <- fmapL show $ parse top fn f
    let theMap = case (doDecls (stateDecls decls) (labelDecls decls) (outcomeDecls decls)) of
                    Left s -> error s
                    Right m -> m

    Rels{..} <- Rels     (initR rels)
                     <$> mapM (resolve theMap) (goalR rels)
                     <*> case fair rels of
                            Just fr -> (liftM Just) $ mapM (resolve theMap) fr
                            Nothing -> return Nothing
                     <*> resolve theMap (transR rels)

    Right ParsedSpec { initial      = map (assignmentToVarInfo theMap) initR
                     , goal         = head (map binExprToHAST goalR)
                     , ucont        = case fair of
                                        Just fr -> Just $ head (map binExprToHAST fr)
                                        Nothing -> Nothing
                     , trans        = map (resolveTransLHS theMap) (ctrlExprToHAST transR)
                     , aigTrans     = Nothing
                     , aigVars      = Nothing
                     , stateVars    = concatMap (declToVarInfo StateVar) (stateDecls decls)
                     , ucontVars    = concatMap (declToVarInfo UContVar) (outcomeDecls decls)
                     , contVars     = concatMap (declToVarInfo ContVar) (labelDecls decls)
                     }

declToVarInfo :: Section -> Decl -> [VarInfo]
declToVarInfo sect d = map mk (vars d)
    where 
        size = case varType d of
                BoolType        -> 1
                IntType sz      -> sz
                EnumType es     -> ceiling (logBase (2::Double) (fromIntegral (length es)))
        enums = case varType d of
                BoolType        -> Nothing
                IntType _       -> Nothing
                EnumType es     -> Just (zip es [0..])
        mk n = VarInfo {
                  name      = n
                , sz        = size
                , section   = sect
                , slice     = Nothing
                , virank    = 0
                , enum      = enums
                , aigId     = Nothing
            }

resolveTransLHS :: Show a => Map String (Either (Section, Int, Maybe [(String, Int)]) a) -> (String, VarInfo -> t) -> t
resolveTransLHS st (s, f) = f v
    where
        v = VarInfo {
            name = s,
            sz = sz,
            section = sect,
            slice = Nothing,
            virank = 0,
            enum = es,
            aigId = Nothing}
        (sect, sz, es) = case Map.lookup s st of
            Nothing                     -> error "LHS of transition relation not in sym tab"
            Just (Left (se, size, ens)) -> (se, size, ens)
            Just (Right size)           -> error ("LHS of transition relation right: " ++ show size)

--The lexer
reservedNames :: [String]
reservedNames = ["case", "true", "false", "else", "abs", "conc", "uint", "bool"]

reservedOps :: [String]
reservedOps = ["!", "&&", "||", "!=", "==", ":=", "<=", "<->"]

--Variable types
boolTyp :: T.GenTokenParser String () Identity -> ParsecT String () Identity Type
boolTyp T.TokenParser{..} = BoolType <$  reserved "bool"

intTyp :: T.GenTokenParser String () Identity -> ParsecT String () Identity Type
intTyp T.TokenParser{..} = IntType  <$  reserved "uint" <*> angles (fromIntegral <$> natural)

enumTyp :: T.GenTokenParser String () Identity -> ParsecT String () Identity Type
enumTyp T.TokenParser{..} = EnumType <$> braces (sepBy identifier comma)

typ :: T.GenTokenParser String () Identity -> ParsecT String () Identity Type
typ t@T.TokenParser{..} = boolTyp t <|> intTyp t <|> enumTyp t

--Variable declarations
decl :: T.GenTokenParser String () Identity -> ParsecT String () Identity Decl
decl t@T.TokenParser{..} = Decl <$> (sepBy identifier comma <* colon) <*> typ t

--Expressions

--The Bin expression parser
binExpr :: T.GenTokenParser String () Identity -> ParsecT String () Identity (BinExpr (Either (String, Maybe (Int, Int)) Int))
binExpr   t@T.TokenParser{..} =   buildExpressionParser (table t) (term t)
                              <?> "expression"

assignExpr :: T.GenTokenParser String () Identity -> ParsecT String () Identity (AssignmentExpr String)
assignExpr T.TokenParser{..} = AssignmentExpr <$> identifier <* reservedOp ":=" <*> (fromIntegral <$> integer)

predicate :: T.GenTokenParser String () Identity -> ParsecT String () Identity (BinExpr (Either (String, Maybe (Int, Int)) Int))
predicate t@T.TokenParser{..} =   try (Pred Eq  <$> valExpr t <* reservedOp "==" <*> valExpr t)
                              <|> try (Pred Neq <$> valExpr t <* reservedOp "!=" <*> valExpr t)

term :: T.GenTokenParser String () Identity -> ParsecT String () Identity (BinExpr (Either (String, Maybe (Int, Int)) Int))
term t@T.TokenParser{..} = parens (binExpr t)
                         <|> TrueE <$ (reserved "true"  <|> reserved "else")
                         <|> FalseE <$ reserved "false"
                         <|> try (predicate t)
                         <?> "simple expression"

table :: T.GenTokenParser String () Identity -> [[Operator String () Identity (BinExpr v)]]
table t@T.TokenParser{..} = [[prefix t "!"  Not]
                            ,[binary t  "&&" (Bin And) AssocLeft]
                            ,[binary t  "||" (Bin Or)  AssocLeft]
                            ,[binary t  "<->" (Bin LogEq) AssocLeft]
                            ]

binary :: T.GenTokenParser String () Identity -> String -> (a -> a -> a) -> Assoc -> Operator String () Identity a
binary T.TokenParser{..} name fun assoc = Infix  (fun <$ reservedOp name) assoc

prefix :: T.GenTokenParser String () Identity -> String -> (a -> a) -> Operator String () Identity a
prefix T.TokenParser{..} name fun = Prefix (fun <$ reservedOp name) 

--Control expressions
assign :: T.GenTokenParser String () Identity -> ParsecT String () Identity (CtrlExpr String (Either (String, Maybe (Int, Int)) Int))
assign t@T.TokenParser{..} = Assign <$> identifier <* reservedOp ":=" <*> valExpr t

ccase :: T.GenTokenParser String () Identity -> ParsecT String () Identity (CtrlExpr String (Either (String, Maybe (Int, Int)) Int))
ccase t@T.TokenParser{..} = CaseC  <$  reserved "case" <*> braces (sepEndBy ((,) <$> binExpr t <* colon <*> ctrlExpr t) semi)

conj :: T.GenTokenParser String () Identity -> ParsecT String () Identity (CtrlExpr String (Either (String, Maybe (Int, Int)) Int))
conj t@T.TokenParser{..} = Conj   <$> braces (sepEndBy (ctrlExpr t) semi)

ctrlExpr :: T.GenTokenParser String () Identity -> ParsecT String () Identity (CtrlExpr String (Either (String, Maybe (Int, Int)) Int))
ctrlExpr t@T.TokenParser{..} = conj t <|> ccase t <|> try (assign t)

--Value expressions
pslice :: T.GenTokenParser String () Identity -> ParsecT String () Identity (Int, Int)
pslice T.TokenParser{..} = brackets $ f <$> integer <*> optionMaybe (colon *> integer)
    where
    f start Nothing    = (fromIntegral start, fromIntegral start)
    f start (Just end) = (fromIntegral start, fromIntegral end)

slicedVar :: T.GenTokenParser String () Identity -> ParsecT String () Identity (String, Maybe (Int, Int))
slicedVar t@T.TokenParser{..} = (,) <$> identifier <*> optionMaybe (pslice t)

lit :: T.GenTokenParser String () Identity -> ParsecT String () Identity (ValExpr (Either (String, Maybe (Int, Int)) Int))
lit t@T.TokenParser{..} = Lit <$> ((Left <$> slicedVar t) <|> ((Right . fromIntegral) <$> integer))

vcase :: T.GenTokenParser String () Identity -> ParsecT String () Identity (ValExpr (Either (String, Maybe (Int, Int)) Int))
vcase t@T.TokenParser{..} = CaseV <$ reserved "case" <*> braces (sepEndBy ((,) <$> binExpr t <* colon <*> valExpr t) semi)

valExpr :: T.GenTokenParser String () Identity -> ParsecT String () Identity (ValExpr (Either (String, Maybe (Int, Int)) Int))
valExpr t@T.TokenParser{..} = vcase t <|> lit t


stdDef :: GenLanguageDef String () Identity
stdDef = emptyDef {T.reservedNames = reservedNames 
                  ,T.reservedOpNames = reservedOps
                  ,T.identStart = letter <|> char '_'
                  ,T.identLetter = alphaNum <|> char '_'
                  ,T.commentStart = "/*"
                  ,T.commentEnd = "*/"
                  ,T.commentLine = "//"
                  }

lexer :: T.GenTokenParser String () Identity
lexer = T.makeTokenParser (stdDef {T.reservedNames = T.reservedNames stdDef ++ ["STATE", "LABEL", "OUTCOME", "INIT", "GOAL", "TRANS", "FAIR", "CONT", "LABELCONSTRAINTS"]})

parseDecls :: ParsecT String () Identity Decls
parseDecls = Decls
    <$  reserved "STATE"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "LABEL"
    <*> sepEndBy (decl lexer) semi
    <*  reserved "OUTCOME"
    <*> sepEndBy (decl lexer) semi
    where
        T.TokenParser {..} = lexer

parseRels :: ParsecT String () Identity (Rels (Either (String, Maybe (Int, Int)) Int))
parseRels = Rels
    <$  reserved "INIT"
    <*> sepEndBy (assignExpr lexer) semi
    <*  reserved "GOAL"
    <*> sepEndBy (binExpr lexer) semi

    <*> optionMaybe (reserved "FAIR" *> (sepEndBy (binExpr lexer) semi))

    -- These are left in for backwards compatibility
    <*  optional (reserved "CONT" <*  binExpr lexer)
    <*  optional (reserved "LABELCONSTRAINTS" <*  binExpr lexer)

    <*  reserved "TRANS"
    <*> (Conj <$> sepEndBy (ctrlExpr lexer) semi)
    where
        T.TokenParser {..} = lexer

spec :: ParsecT String () Identity Spec
spec = Spec <$> parseDecls <*> parseRels

top :: ParsecT String () Identity Spec
top = whiteSpace *> (spec <* eof)
    where
        T.TokenParser {..} = lexer

type SymTab = Map String (Either (Section, Int, Maybe [(String, Int)]) Int)

resolve :: (Traversable t) => SymTab -> t (Either (String, Slice) Int) -> Either String (t (Either VarInfo Int))
resolve = traverse . func

func :: SymTab -> Either (String, Slice) Int -> Either String (Either VarInfo Int)
func mp l = case l of 
    Left (str, slice) -> case Map.lookup str mp of
        Nothing                     -> Left  $ "Var doesn't exist: " ++ str
        Just (Left (sect, sz, es))  -> Right $ Left $ VarInfo str sz sect slice 1 es Nothing
        Just (Right c)              -> Right $ Right $ getBits slice c
    Right x -> Right $ Right x

constructSymTab :: (Ord a) => [(a, b)] -> Either a (Map a b)
constructSymTab = foldM f (Map.empty) 
    where
    f mp (key, val) = case Map.lookup key mp of
        Nothing -> Right $ Map.insert key val mp
        Just _  -> Left key

doDecls :: [Decl] -> [Decl] -> [Decl] -> Either String SymTab
doDecls sd ld od = fmapL ("Variable already exists: " ++) $ constructSymTab $ concat [concatMap (go StateVar) sd, concatMap (go ContVar) ld, concatMap (go UContVar) od]
    where
    go sect (Decl vars vtype) = concatMap go' vars
        where
        go' var = (var, Left (sect, sz, (Just consts))) : map (second Right) consts
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

doTypeSz :: Type -> Int
doTypeSz BoolType      = 1
doTypeSz (IntType n)   = n
doTypeSz (EnumType es) = typeSize $ length es

doTypeconsts :: Type -> [(String, Int)]
doTypeconsts BoolType      = []
doTypeconsts (IntType _)   = []
doTypeconsts (EnumType es) = zip es [0..]

getBits :: Slice -> Int -> Int
getBits Nothing x       = x
getBits (Just (l, u)) x = (shift (-l) x) .&. (2 ^ (u - l + 1) - 1)

assignmentToVarInfo :: SymTab -> AssignmentExpr String -> (VarInfo, Int)
assignmentToVarInfo st (AssignmentExpr s val) = (v, val)
    where
        v = VarInfo {
            name = s,
            sz = sz,
            section = sect,
            slice = Nothing,
            virank = 0,
            enum = es,
            aigId = Nothing}
        (sect, sz, es) = case Map.lookup s st of
            Nothing                     -> error "LHS of transition relation not in sym tab"
            Just (Left (se, size, ens)) -> (se, size, ens)
            Just (Right size)           -> error ("LHS of transition relation right: " ++ show size)

predToHAST :: ValExpr (Either VarInfo Int) -> ValExpr (Either VarInfo Int) -> AST
predToHAST (Lit (Right a)) (Lit (Right b))   = if (a == b) then HAST.T else HAST.F
predToHAST (Lit (Left a)) (Lit (Right b))    = HAST.EqConst (HAST.NVar a) b
predToHAST (Lit (Right a)) (Lit (Left b))    = HAST.EqConst (HAST.NVar b) a
predToHAST (Lit (Left a)) (Lit (Left b))     = HAST.EqVar (HAST.NVar a) (HAST.NVar b)
predToHAST _ _                               = error "predToHAST called incorrectly"

binExprToHAST :: BinExpr (Either VarInfo Int) -> AST
binExprToHAST TrueE             = HAST.T
binExprToHAST FalseE            = HAST.F
binExprToHAST (Not e)           = HAST.Not (binExprToHAST e)
binExprToHAST (Bin And a b)     = HAST.And (binExprToHAST a) (binExprToHAST b)
binExprToHAST (Bin Or a b)      = HAST.Or (binExprToHAST a) (binExprToHAST b)
binExprToHAST (Bin LogEq a b)   = HAST.XNor (binExprToHAST a) (binExprToHAST b)
binExprToHAST (Pred Eq a b)     = predToHAST a b
binExprToHAST (Pred Neq a b)    = HAST.Not (predToHAST a b)

ctrlExprToHAST :: CtrlExpr String (Either VarInfo Int) -> [(String, (VarInfo -> AST))]
ctrlExprToHAST (Assign var val) = [(var, valExprToHAST val)]
ctrlExprToHAST (Conj cs)        = concatMap ctrlExprToHAST cs
ctrlExprToHAST (Signal _ _ )    = error "Signal not implemented"
ctrlExprToHAST (CaseC _)        = error "CaseC not implemented"

valExprToHAST :: ValExpr (Either VarInfo Int) -> (VarInfo -> AST)
valExprToHAST (Lit (Left a))    = (\x -> HAST.EqVar (HAST.FVar x) (HAST.NVar a))
valExprToHAST (Lit (Right a))   = (\x -> HAST.EqConst (HAST.FVar x) a)
valExprToHAST (CaseV cases)     = f
    where
        bs = map (binExprToHAST . fst) cases
        vs = map (valExprToHAST . snd) cases
        f x = HAST.Case (zip bs (map ($ x) vs))

