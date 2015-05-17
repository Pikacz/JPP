{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Printabc where

-- pretty-printer generated by the BNF converter

import Absabc
import Data.Char


-- the top-level printing method
printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts -> showString t . showChar ')' . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else (' ':s))

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: [a] -> Doc
  prtList = concatD . map (prt 0)

instance Print a => Print [a] where
  prt _ = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Integer where
  prt _ x = doc (shows x)


instance Print Double where
  prt _ x = doc (shows x)


instance Print Ident where
  prt _ (Ident i) = doc (showString ( i))



instance Print Program where
  prt i e = case e of
   Prog stms -> prPrec i 0 (concatD [prt 0 stms])


instance Print Stm where
  prt i e = case e of
   StmExpr expr -> prPrec i 0 (concatD [prt 0 expr])
   StmDec dec -> prPrec i 0 (concatD [prt 0 dec])
   StmWhile expr stm -> prPrec i 0 (concatD [doc (showString "while") , doc (showString "(") , prt 0 expr , doc (showString ")") , prt 0 stm])
   StmIf expr stm -> prPrec i 0 (concatD [doc (showString "if") , doc (showString "(") , prt 0 expr , doc (showString ")") , prt 0 stm , doc (showString "fi")])
   StmIfE expr stm0 stm -> prPrec i 0 (concatD [doc (showString "if") , doc (showString "(") , prt 0 expr , doc (showString ")") , prt 0 stm0 , doc (showString "else") , prt 0 stm])
   StmBloc stms -> prPrec i 0 (concatD [doc (showString "{") , prt 0 stms , doc (showString "}")])
   StmFor dec expr stm0 stm -> prPrec i 0 (concatD [doc (showString "for") , doc (showString "(") , prt 0 dec , doc (showString ";") , prt 0 expr , doc (showString ";") , prt 0 stm0 , doc (showString ")") , prt 0 stm])
   StmRet  -> prPrec i 0 (concatD [doc (showString "return")])
   StmRetV expr -> prPrec i 0 (concatD [doc (showString "return") , prt 0 expr])
   StmPrint expr -> prPrec i 0 (concatD [doc (showString "print") , prt 0 expr])
   StmRead var -> prPrec i 0 (concatD [doc (showString "read") , prt 0 var])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Dec where
  prt i e = case e of
   DVar type' id -> prPrec i 0 (concatD [prt 0 type' , prt 0 id])
   DInit type' id expr -> prPrec i 0 (concatD [prt 0 type' , prt 0 id , doc (showString "=") , prt 0 expr])
   DArr type' id expr -> prPrec i 0 (concatD [prt 0 type' , prt 0 id , doc (showString "[") , prt 0 expr , doc (showString "]")])
   DRec id decs -> prPrec i 0 (concatD [doc (showString "struct") , prt 0 id , doc (showString "{") , prt 0 decs , doc (showString "}")])
   DFunc type' id params stm -> prPrec i 0 (concatD [prt 0 type' , prt 0 id , doc (showString "(") , prt 0 params , doc (showString ")") , prt 0 stm])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , doc (showString ";") , prt 0 xs])

instance Print Param where
  prt i e = case e of
   PVal type' id -> prPrec i 0 (concatD [prt 0 type' , prt 0 id])
   PVar type' id -> prPrec i 0 (concatD [prt 0 type' , doc (showString "&") , prt 0 id])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Type where
  prt i e = case e of
   TCust id -> prPrec i 0 (concatD [prt 0 id])
   TInt  -> prPrec i 0 (concatD [doc (showString "int")])
   TBool  -> prPrec i 0 (concatD [doc (showString "bool")])
   TChar  -> prPrec i 0 (concatD [doc (showString "char")])
   TStr  -> prPrec i 0 (concatD [doc (showString "string")])
   TVoid  -> prPrec i 0 (concatD [doc (showString "void")])
   TArr type' -> prPrec i 1 (concatD [prt 0 type' , doc (showString "[]")])


instance Print Expr where
  prt i e = case e of
   ExprAss var expr -> prPrec i 0 (concatD [prt 0 var , doc (showString "=") , prt 0 expr])
   ExprAssO var assopr expr -> prPrec i 0 (concatD [prt 0 var , prt 0 assopr , prt 0 expr])
   ExprIR var -> prPrec i 0 (concatD [prt 0 var , doc (showString "++")])
   ExprIL var -> prPrec i 0 (concatD [doc (showString "++") , prt 0 var])
   ExprDR var -> prPrec i 0 (concatD [prt 0 var , doc (showString "--")])
   ExprDL var -> prPrec i 0 (concatD [doc (showString "--") , prt 0 var])
   ExprAnd expr0 expr -> prPrec i 1 (concatD [prt 2 expr0 , doc (showString "&&") , prt 2 expr])
   ExprOr expr0 expr -> prPrec i 1 (concatD [prt 2 expr0 , doc (showString "||") , prt 2 expr])
   ExprNot expr -> prPrec i 1 (concatD [doc (showString "~") , prt 2 expr])
   ExprLt expr0 expr -> prPrec i 2 (concatD [prt 3 expr0 , doc (showString "<") , prt 3 expr])
   ExprLte expr0 expr -> prPrec i 2 (concatD [prt 3 expr0 , doc (showString "<=") , prt 3 expr])
   ExprEq expr0 expr -> prPrec i 2 (concatD [prt 3 expr0 , doc (showString "==") , prt 3 expr])
   ExprNEq expr0 expr -> prPrec i 2 (concatD [prt 3 expr0 , doc (showString "!=") , prt 3 expr])
   ExprGte expr0 expr -> prPrec i 2 (concatD [prt 3 expr0 , doc (showString ">=") , prt 3 expr])
   ExprGt expr0 expr -> prPrec i 2 (concatD [prt 3 expr0 , doc (showString ">") , prt 3 expr])
   ExprAdd expr0 expr -> prPrec i 3 (concatD [prt 3 expr0 , doc (showString "+") , prt 4 expr])
   ExprSub expr0 expr -> prPrec i 3 (concatD [prt 3 expr0 , doc (showString "-") , prt 4 expr])
   ExprMod expr0 expr -> prPrec i 3 (concatD [prt 3 expr0 , doc (showString "%") , prt 4 expr])
   ExprMul expr0 expr -> prPrec i 4 (concatD [prt 4 expr0 , doc (showString "*") , prt 5 expr])
   ExprDiv expr0 expr -> prPrec i 4 (concatD [prt 4 expr0 , doc (showString "/") , prt 5 expr])
   ExprVal val -> prPrec i 5 (concatD [prt 0 val])
   ExprVar var -> prPrec i 5 (concatD [prt 0 var])
   ExprCall var exprs -> prPrec i 5 (concatD [prt 0 var , doc (showString "(") , prt 0 exprs , doc (showString ")")])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print AssOpr where
  prt i e = case e of
   AssAdd  -> prPrec i 0 (concatD [doc (showString "+=")])
   AssSub  -> prPrec i 0 (concatD [doc (showString "-=")])
   AssMul  -> prPrec i 0 (concatD [doc (showString "*=")])
   AssDiv  -> prPrec i 0 (concatD [doc (showString "/=")])
   AssMod  -> prPrec i 0 (concatD [doc (showString "%=")])


instance Print Val where
  prt i e = case e of
   ValInt n -> prPrec i 0 (concatD [prt 0 n])
   ValChar c -> prPrec i 0 (concatD [prt 0 c])
   ValStr str -> prPrec i 0 (concatD [prt 0 str])
   ValTrue  -> prPrec i 0 (concatD [doc (showString "true")])
   ValFalse  -> prPrec i 0 (concatD [doc (showString "false")])


instance Print Var where
  prt i e = case e of
   VarArr var expr -> prPrec i 0 (concatD [prt 0 var , doc (showString "[") , prt 0 expr , doc (showString "]")])
   VarRec var id -> prPrec i 1 (concatD [prt 0 var , doc (showString ".") , prt 0 id])
   VarVar id -> prPrec i 2 (concatD [prt 0 id])



