module Skelabc where

-- Haskell module generated by the BNF converter

import Absabc
import ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

transIdent :: Ident -> Result
transIdent x = case x of
  Ident str  -> failure x


transProgram :: Program -> Result
transProgram x = case x of
  Prog stms  -> failure x


transStm :: Stm -> Result
transStm x = case x of
  StmExpr expr  -> failure x
  StmDec dec  -> failure x
  StmWhile expr stm  -> failure x
  StmIf expr stm  -> failure x
  StmIfE expr stm1 stm2  -> failure x
  StmBloc stms  -> failure x
  StmFor dec expr stm1 stm2  -> failure x
  StmRet  -> failure x
  StmRetV expr  -> failure x
  StmPrint expr  -> failure x
  StmRead var  -> failure x


transDec :: Dec -> Result
transDec x = case x of
  DVar type' id  -> failure x
  DInit type' id expr  -> failure x
  DArr type' id expr  -> failure x
  DRec id decs  -> failure x
  DFunc type' id params stm  -> failure x


transParam :: Param -> Result
transParam x = case x of
  PVal type' id  -> failure x
  PVar type' id  -> failure x


transType :: Type -> Result
transType x = case x of
  TCust id  -> failure x
  TInt  -> failure x
  TBool  -> failure x
  TChar  -> failure x
  TStr  -> failure x
  TVoid  -> failure x
  TArr type'  -> failure x


transExpr :: Expr -> Result
transExpr x = case x of
  ExprAss var expr  -> failure x
  ExprAssO var assopr expr  -> failure x
  ExprIR var  -> failure x
  ExprIL var  -> failure x
  ExprDR var  -> failure x
  ExprDL var  -> failure x
  ExprAnd expr1 expr2  -> failure x
  ExprOr expr1 expr2  -> failure x
  ExprNot expr  -> failure x
  ExprLt expr1 expr2  -> failure x
  ExprLte expr1 expr2  -> failure x
  ExprEq expr1 expr2  -> failure x
  ExprNEq expr1 expr2  -> failure x
  ExprGte expr1 expr2  -> failure x
  ExprGt expr1 expr2  -> failure x
  ExprAdd expr1 expr2  -> failure x
  ExprSub expr1 expr2  -> failure x
  ExprMod expr1 expr2  -> failure x
  ExprMul expr1 expr2  -> failure x
  ExprDiv expr1 expr2  -> failure x
  ExprVal val  -> failure x
  ExprVar var  -> failure x
  ExprCall var exprs  -> failure x


transAssOpr :: AssOpr -> Result
transAssOpr x = case x of
  AssAdd  -> failure x
  AssSub  -> failure x
  AssMul  -> failure x
  AssDiv  -> failure x
  AssMod  -> failure x


transVal :: Val -> Result
transVal x = case x of
  ValInt n  -> failure x
  ValChar c  -> failure x
  ValStr str  -> failure x
  ValTrue  -> failure x
  ValFalse  -> failure x


transVar :: Var -> Result
transVar x = case x of
  VarArr var expr  -> failure x
  VarRec var id  -> failure x
  VarVar id  -> failure x


