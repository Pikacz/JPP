module Absabc where

-- Haskell module generated by the BNF converter


newtype Ident = Ident String deriving (Eq,Ord,Show)
data Program =
   Prog [Stm]
  deriving (Eq,Ord,Show)

data Stm =
   StmExpr Expr
 | StmDec Dec
 | StmWhile Expr Stm
 | StmIf Expr Stm
 | StmIfE Expr Stm Stm
 | StmBloc [Stm]
 | StmFor Dec Expr Stm Stm
 | StmRet
 | StmRetV Expr
 | StmPrint Expr
 | StmPrintLn Expr
 | StmRead Var
  deriving (Eq,Ord,Show)

data Dec =
   DVar Type Ident
 | DInit Type Ident Expr
 | DAuto Ident Expr
 | DArr Type Ident Expr
 | DRec Ident [Dec]
 | DFunc Type Ident [Param] Stm
  deriving (Eq,Ord,Show)

data Param =
   PVal Type Ident
 | PVar Type Ident
  deriving (Eq,Ord,Show)

data Type =
   TCust Ident
 | TInt
 | TBool
 | TChar
 | TStr
 | TVoid
 | TArr Type
  deriving (Eq,Ord,Show)

data Expr =
   ExprAss Var Expr
 | ExprAssO Var AssOpr Expr
 | ExprIR Var
 | ExprIL Var
 | ExprDR Var
 | ExprDL Var
 | ExprAnd Expr Expr
 | ExprOr Expr Expr
 | ExprNot Expr
 | ExprLt Expr Expr
 | ExprLte Expr Expr
 | ExprEq Expr Expr
 | ExprNEq Expr Expr
 | ExprGte Expr Expr
 | ExprGt Expr Expr
 | ExprAdd Expr Expr
 | ExprSub Expr Expr
 | ExprMod Expr Expr
 | ExprMul Expr Expr
 | ExprDiv Expr Expr
 | ExprVal Val
 | ExprVar Var
 | ExprCall Var [Expr]
  deriving (Eq,Ord,Show)

data AssOpr =
   AssAdd
 | AssSub
 | AssMul
 | AssDiv
 | AssMod
  deriving (Eq,Ord,Show)

data Val =
   ValInt Integer
 | ValChar Char
 | ValStr String
 | ValTrue
 | ValFalse
  deriving (Eq,Ord,Show)

data Var =
   VarArr Var Expr
 | VarRec Var Ident
 | VarVar Ident
  deriving (Eq,Ord,Show)

