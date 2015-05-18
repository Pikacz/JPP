module Interpreter where

import Absabc as Abs
import TypeCheck as TC
import Environment as Env
import System.IO



runProgram :: Abs.Program -> Env.Environment -> Env.State -> Env.TypeEnv -> IO ()
runProgram (Abs.Prog []) ev st te = putStr ""
runProgram (Abs.Prog (s : ss)) ev st te =
    do x <- runStm s ev st te
       case x of
        Left e -> putStr $ show e
        Right (ev', st', te', _) -> runProgram (Abs.Prog ss) ev' st' te'



runStm :: Abs.Stm -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError (Env.Environment, Env.State, Env.TypeEnv, Env.Value))
runStm (Abs.StmExpr e) ev st te = do x <- exprToVal e ev st te
                                     case x of
                                        Left err -> return $ Left err
                                        Right (_, st') -> return $ Right (ev, st', te, Env.VNothing)
runStm (Abs.StmDec dec) ev st te =
    do x <- runDec dec ev st te
       case x of
        Left e -> return $ Left e
        Right (Left (nm, v, st')) -> let l = Env.next st' in
            let ev' = Env.addVariable nm l ev
                st'' = Env.addValue l v st' in
                return $ Right (ev', st'', te, Env.VNothing)
        Right (Right (tn, t, st')) -> let te' = Env.insertType tn t te in
            return $ Right (ev, st', te', Env.VNothing)

runStm (Abs.StmWhile ex stm) ev st te = 
    do x <- exprToVal ex ev st te
       case x of
        Left e -> return $ Left e
        Right (v, st') -> if v == (Env.VBool True) then
            do x <-  runStm stm ev st' te 
               case x of
                    Left e -> return $ Left e
                    Right (ev', st'', te', val) -> if val == Env.VNothing then  runStm (Abs.StmWhile ex stm) ev' st'' te'
                        else return $ Right (ev', st'', te', val)
            else
                return $ Right (ev, st', te, Env.VNothing)
runStm (Abs.StmIf ex stm) ev st te = 
    do x <- exprToVal ex ev st te
       case x of
        Left e -> return $ Left e
        Right (v, st') -> if v == (Env.VBool True) then runStm stm ev st' te
            else return $ Right (ev, st', te, Env.VNothing)
runStm (Abs.StmIfE ex st1 st2) ev st te = 
    do x <- exprToVal ex ev st te
       case x of 
        Left e -> return $ Left e
        Right (v, st') -> if v == (Env.VBool True) then runStm st1 ev st' te
            else runStm st2 ev st' te
runStm (Abs.StmBloc []) ev st te = return $ Right (ev, st, te, Env.VNothing)
runStm (Abs.StmBloc (stm : ss)) ev st te =
    do x <- runStm stm ev st te
       case x of
        Left e -> return $ Left e
        Right (ev', st', te', val) -> case val of
            Env.VNothing -> runStm (Abs.StmBloc ss) ev' st' te'
            v -> return $ Right (ev, st', te, val)
runStm (Abs.StmFor dec exp stm1 stm2) ev st te =
    let sdec = Abs.StmDec dec
        stm = Abs.StmBloc [stm1, stm2] in
        let wh = Abs.StmWhile exp stm in
            let all = Abs.StmBloc [sdec, wh] in
                runStm all ev st te
runStm Abs.StmRet ev st te = return $ Right (ev, st, te, Env.VVoid)
runStm (Abs.StmRetV expr) ev st te =
    do x <- exprToVal expr ev st te
       case x of
        Left e -> return $ Left e
        Right (v, st') -> return $ Right (ev, st', te, v)
runStm (Abs.StmPrint expr) ev st te = 
    do x <- exprToVal expr ev st te
       case x of
        Left e -> return $ Left e
        Right (v, st') ->
            do print v
               return $ Right (ev, st', te, Env.VNothing)


-- Right Left variable, Right Right type
runDec :: Abs.Dec -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError 
         (Either (Abs.Ident, Env.Value, Env.State) 
                 (Env.TypeName, Env.Type, Env.State)))
runDec (Abs.DVar at nm) ev st te = case Env.getTypeAbs at te of
        Right t -> let (v, st') = Env.defValue t st ev in
            return $ Right $ Left (nm, v, st')
runDec (Abs.DInit at nm expr) ev st te = 
    do x <- exprToVal expr ev st te
       case x of
        Left e -> return $ Left e
        Right (v, st') -> return $ Right $ Left (nm, v, st')
runDec (Abs.DArr at nm expr) ev st te = 
    do x <- exprToVal expr ev st te
       case x of
        Left e -> return $ Left e
        Right (Env.VInt i, st') -> case Env.getTypeAbs at te of
            Right t -> let (v, st'') = Env.defValue (Env.TArray t i) st ev in
                let l = Env.next st'' in
                    return $ Right $ Left (nm, v, st'')
runDec (Abs.DRec (Abs.Ident nm) decs) ev st te =
    do x <- runDecs decs ev st te Env.emptySE
       case x of
        Left e -> return $ Left e
        Right (t, st') -> return $ Right $ Right (nm, t, st')
runDec (Abs.DFunc t nm params stm) ev st te = let par = Env.tParamsToVParams params [] in
        let l = Env.next st 
            fev = Env.addVariable nm l ev in
            let func = Env.VFunc par stm fev in
                let st' = Env.addValue l func st in
                    return $ Right $ Left (nm, func, st')



-- parses declarations into struct
runDecs :: [Abs.Dec] -> Env.Environment -> Env.State -> Env.TypeEnv -> Env.StructEnv -> IO (Either RuntimeError (Env.Type, Env.State))
runDecs [] ev st te acc = return $ Right (Env.TStruct Env.emptyTypeEnv acc, st)
runDecs (dec : ds) ev st te acc = 
    do x <- runDec dec ev st te
       case x of
        Left e -> return $ Left e
        Right (Left (nm, val, st')) -> let acc' = Env.addToSE nm val acc in
            runDecs ds ev st' te acc'
        Right (Right (nm, t, st')) -> let te' = Env.insertType nm t te in
            runDecs ds ev st' te' acc



exprToVal :: Abs.Expr -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError (Env.Value, Env.State))



exprToVal (Abs.ExprVar var) ev st te = varToVal var ev st te
exprToVal (Abs.ExprVal val) _ st te = return $ Right (valToVal val, st)
exprToVal (Abs.ExprCall var exprs) ev st te = 
    do x <- varToVal var ev st te
       case x of
        Left e -> return $ Left e
        Right ((Env.VFunc params stm fev), st') ->
            do xx <- paramsToEnv params exprs fev st' te
               case xx of
                Left e -> return $ Left e
                Right (ev', st'') -> 
                    do xxx <- runStm stm ev' st'' te
                       case xxx of
                        Left e -> return $ Left e
                        Right (_, st''', _, v) -> return $ Right (v, st''')
exprToVal (Abs.ExprAdd e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VInt (i1 + i2), st')



valToVal :: Abs.Val -> Env.Value
valToVal (Abs.ValInt i) = Env.VInt $ fromInteger i
valToVal (Abs.ValChar c) = Env.VChar c
valToVal (Abs.ValStr s) = Env.VString s
valToVal Abs.ValTrue = Env.VBool True
valToVal Abs.ValFalse = Env.VBool False


varToVal :: Abs.Var -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError (Env.Value, Env.State))
varToVal (Abs.VarVar nm) ev st te = 
    let l = Env.getVariable nm ev in return $ Right (Env.getValue l st, st)
varToVal (Abs.VarArr var expr) ev st te = 
    do x <- varToVal var ev st te
       case x of
        Left e -> return $ Left e
        Right (arr, st') -> 
            do xx <- exprToVal expr ev st' te
               case xx of
                Left e -> return $ Left e
                Right (idx, st'') -> case Env.getValFromArray idx arr of
                    Left e -> return $ Left $ EnvErr e
                    Right l -> return $ Right (Env.getValue l st'', st'')
varToVal (Abs.VarRec var nm) ev st te = let l = Env.getVariable nm ev in
        case Env.getValue l st of
            (Env.VStruct ev') -> varToVal var ev' st te

varToLoc :: Abs.Var -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError (Env.Loc, Env.State))
varToLoc (Abs.VarVar nm) ev st te = return $ Right (Env.getVariable nm ev, st)
varToLoc (Abs.VarRec var nm) ev st te = let l = Env.getVariable nm ev in
        case Env.getValue l st of
            (Env.VStruct ev') -> varToLoc var ev' st te
varToLoc (Abs.VarArr var expr) ev st te = 
    do x <- varToVal var ev st te
       case x of
        Left e -> return $ Left e
        Right (arr, st') -> 
            do xx <- exprToVal expr ev st' te
               case xx of
                Left e -> return $ Left e
                Right (idx, st'') -> case Env.getValFromArray idx arr of
                    Left e -> return $ Left $ EnvErr e
                    Right l -> return $ Right (l, st'') 

paramsToEnv :: [Env.Param] -> [Abs.Expr] -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError (Env.Environment, Env.State))
paramsToEnv [] [] ev st te = return $ Right (ev, st)
paramsToEnv (p : ps) (e : es) ev st te = case p of
        Env.Val nm ->  
            do x <- exprToVal e ev st te
               case x of
                Left e -> return $ Left e
                Right (v, st') -> let l = Env.next st' in
                    let ev' = Env.addVariable nm l ev
                        st'' = Env.addValue l v st' in
                        paramsToEnv ps es ev' st'' te
        Env.Ref nm -> case e of
            (ExprVar var) -> 
                do x <- varToLoc var ev st te
                   case x of
                    Left e -> return $ Left e
                    Right (l, st') -> let ev' = Env.addVariable nm l ev in
                        paramsToEnv ps es ev' st' te

arithmeticExpr :: Abs.Expr -> Abs.Expr -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError (Int, Int, Env.State))
arithmeticExpr e1 e2 ev st te =
    do x <- exprToVal e1 ev st te
       case x of
        Left e -> return $ Left e
        Right (Env.VInt i1, st') -> 
            do xx <- exprToVal e2 ev st' te
               case xx of
                Left e -> return $ Left e
                Right (Env.VInt i2, st'') -> return $ Right (i1, i2, st'')


data RuntimeError = 
      ZeroDiv
    | EnvErr Env.EnvError deriving (Show)




interpret:: Program -> IO ()
interpret p = case TC.parseProg p TC.emptyVariableType Env.emptyTypeEnv of
        Nothing ->
            do putStrLn "type check was succesfull!"
               runProgram p Env.emptyEnvironment Env.emptyState Env.emptyTypeEnv
               
                
--            Just e -> show e
        Just e -> print e


