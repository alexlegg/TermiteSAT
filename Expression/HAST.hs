{-# LANGUAGE OverloadedStrings, RecordWildCards, PolymorphicComponents, FlexibleInstances #-}

module Expression.HAST(AST(..),
                 ASTVar(..),
                 existsMany,
                 nExistsMany,
                 printAST) where

import Data.Text.Lazy hiding (intercalate, map, take, length)
import Text.PrettyPrint.Leijen.Text
import Utils.Utils

-- f   == type of anonymous free variables 
-- e   == type of variables bound by exists statements 
-- c   == type of single bit variables bound by let statements
-- var == type of free variable identifiers

data ASTVar f e v = FVar f
                  | EVar e
                  | NVar v

instance (Show f, Show e, Show v) => Show (ASTVar f e v) where
    show (FVar f) = show f
    show (EVar e) = show e
    show (NVar v) = show v

data AST f e c v = T
                 | F
                 | Not     (AST f e c v)
                 | And     (AST f e c v) (AST f e c v)
                 | Or      (AST f e c v) (AST f e c v)
                 | Imp     (AST f e c v) (AST f e c v)
                 | XOr     (AST f e c v) (AST f e c v)
                 | XNor    (AST f e c v) (AST f e c v)
                 | Conj    [AST f e c v]
                 | Disj    [AST f e c v]
                 | Case    [(AST f e c v, AST f e c v)]
                 | Var     (ASTVar f e v)                 -- only valid for 1-bit variables
                 | EqVar   (ASTVar f e v) (ASTVar f e v)  -- variables must have the same width
                 | EqConst (ASTVar f e v) Int
                 | Exists  Int (e -> AST f e c v)
                 | NExists String Int (e -> AST f e c v)
                 | Let     (AST f e c v) (c -> AST f e c v)
                 | LetLit  c

instance (Show f, Show e, Show c, Show v) => Show (AST f e c v) where
    show T          = "True"
    show F          = "False"
    show (Not x)    = "Not (" ++ show x ++ ")"
    show (And x y)  = "And (" ++ show x ++ ", " ++ show y ++ ")"
    show (Conj xs)  = "Conj (" ++ interMap ", " show xs ++ ")"
    show (XNor x y) = "XNor (" ++ show x ++ ", " ++ show y ++ ")"
    show (Var x)    = show x

existsMany :: [Int] -> ([e] -> AST f e c v) -> AST f e c v
existsMany ws f = existsMany' ws [] f

existsMany' :: [Int] -> [e] -> ([e] -> AST f e c v) -> AST f e c v
existsMany' []     vs f = f vs
existsMany' (w:ws) vs f = Exists w (\x -> existsMany' ws (vs++[x]) f)

nExistsMany :: [(String, Int)] -> ([e] -> AST f e c v) -> AST f e c v
nExistsMany ws f = nExistsMany' ws [] f

nExistsMany' :: [(String, Int)] -> [e] -> ([e] -> AST f e c v) -> AST f e c v
nExistsMany' []     vs f = f vs
nExistsMany' ((n,w):ws) vs f = NExists n w (\x -> nExistsMany' ws (vs++[x]) f)


--newtype TAST sp lp = TAST forall f e c . AST f e c (BAVar sp lp)
--type TASTVar sp lp = forall f e   . ASTVar f e (BAVar sp lp)

printAST :: Show v => AST Doc Doc Doc v -> Doc
printAST = prettyPrint' 0
    where
    prettyPrint' :: (Show  v) => Int -> AST Doc Doc Doc v -> Doc
    prettyPrint' ng = prettyPrint''
        where
        prettyPrint'' T                     = text "True"
        prettyPrint'' F                     = text "False"
        prettyPrint'' (Not e)               = text "!" <+> prettyPrint'' e
        prettyPrint'' (And x y)             = parens $ prettyPrint'' x <+> text "&&"  <+> prettyPrint'' y
        prettyPrint'' (Or x y)              = parens $ prettyPrint'' x <+> text "||"  <+> prettyPrint'' y
        prettyPrint'' (Imp x y)             = parens $ prettyPrint'' x <+> text "->"  <+> prettyPrint'' y
        prettyPrint'' (XNor x y)            = parens $ prettyPrint'' x <+> text "<->" <+> prettyPrint'' y
        prettyPrint'' (Conj es)             = text "CONJ" <+> lbrace <$$> indent 2 (vcat $ map ((<> semi) . prettyPrint'') es) <$$> rbrace
        prettyPrint'' (Disj es)             = text "Disj" <+> lbrace <$$> indent 2 (vcat $ map ((<> semi) . prettyPrint'') es) <$$> rbrace
        prettyPrint'' (Case cases)          = text "case" <+> lbrace <$$> indent 2 (vcat $ map (uncurry f) cases) <$$> rbrace
            where  
            f c v = prettyPrint'' c <+> colon <+> prettyPrint'' v <+> semi
        prettyPrint'' (EqVar v1 v2)         = text (pack (show v1)) <+> text "==" <+> text (pack (show v2))
        prettyPrint'' (EqConst v c)         = text (pack (show v)) <+> text "==" <+> text (pack (show c))
        prettyPrint'' (Exists   _ func)     = text "exists" <+> parens (text $ pack $ "tvar" ++ show ng) <+> lbrace <$$> (prettyPrint' (ng + 1) $ func (text $ pack $ "tvar" ++ show ng)) <$$> rbrace
        prettyPrint'' (NExists n w func)    = text "exists" <+> parens ((text $ pack n) <+> (parens (text $ pack $ show w))) <+> lbrace <$$> (prettyPrint' (ng + 1) $ func (text $ pack n)) <$$> rbrace
        prettyPrint'' (Var v)               = text $ pack $ show v
        prettyPrint'' (Let x f)             = text "let" <+> text "tmp" <+> text ":=" <+> prettyPrint'' x <+> text "in" <$$> indent 2 (prettyPrint'' $ f (text "tmp"))
        prettyPrint'' (LetLit x)            = x


instance (Show v) => Show (AST Doc Doc Doc v) where
    show = show . printAST
