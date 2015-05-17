module Interpreter where

import Absabc as Abs
import TypeCheck as TC
import Environment as Env



runStm :: Abs.Stm -> Env.Environment -> Env.State -> Env.TypeEnv -> Either RuntimeError (Env.Environment, Env.State, Env.TypeEnv, Env.Value)
runStm (Abs.StmExpr e) ev st te = case exprToVal e ev st of
        Left err -> Left err
        Right (_, st') -> Right (ev, st', te, Env.VVoid)


{-
runDec :: Abs.Dec -> Env.Environment -> Env.State -> Env.TypeEnv -> Either RuntimeError (Env.Environment, Env.State, Env.TypeEnv)
runDec (Abs.DVar at nm) ev st te = case Env.getTypeAbs at te of
        Right t -> 
-}

exprToVal :: Abs.Expr -> Env.Environment -> Env.State -> Either RuntimeError (Env.Value, Env.State)

exprToVal (Abs.ExprVar var) ev st = varToVal var ev st
exprToVal (Abs.ExprVal val) _ st = Right (valToVal val, st)
--exprToVal (Abs.ExprCall exprs) ec st =

exprToVal (Abs.ExprAdd e1 e2) ev st = case arithmeticExpr e1 e2 ev st of
    Left e -> Left e
    Right (i1, i2, st') -> Right (Env.VInt (i1 + i2), st')




valToVal :: Abs.Val -> Env.Value
valToVal (Abs.ValInt i) = Env.VInt $ fromInteger i
valToVal (Abs.ValChar c) = Env.VChar c
valToVal (Abs.ValStr s) = Env.VString s
valToVal Abs.ValTrue = Env.VBool True
valToVal Abs.ValFalse = Env.VBool False


varToVal :: Abs.Var -> Env.Environment -> Env.State -> Either RuntimeError (Env.Value, Env.State)
varToVal (Abs.VarVar nm) ev st = 
    let l = Env.getVariable nm ev in Right  (Env.getValue l st, st)
varToVal (Abs.VarArr var expr) ev st = case varToVal var ev st of
        Left e -> Left e
        Right (arr, st') -> case exprToVal expr ev st' of
            Left e -> Left e
            Right (idx, st'') -> Right (Env.getValFromArray idx arr, st'')
varToVal (Abs.VarRec var nm) ev st = let l = Env.getVariable nm ev in
        case Env.getValue l st of
            (Env.VStruct ev') -> varToVal var ev' st


--callToVal :: Env.VFunc -> [Abs.Expr] -> Env.Environment -> Env.State -> Either


arithmeticExpr :: Abs.Expr -> Abs.Expr -> Env.Environment -> Env.State -> Either RuntimeError (Int, Int, Env.State)
arithmeticExpr e1 e2 ev st = case exprToVal e1 ev st of
        Left e -> Left e
        Right (Env.VInt i1, st') -> case exprToVal e2 ev st' of
            Left e -> Left e
            Right (Env.VInt i2, st'') -> Right (i1, i2, st'')


data RuntimeError = 
      ZeroDiv




interpret:: Program -> String
interpret p = case TC.parseProg p TC.emptyVariableType Env.emptyTypeEnv of
        Nothing -> "OK"
        Just e -> show e


