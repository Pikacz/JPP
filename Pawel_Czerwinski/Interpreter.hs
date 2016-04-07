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
runStm (Abs.StmBloc ss) ev st te = runBloc ss ev st te ev te
runStm (Abs.StmFor dec exp stm2 stm1) ev st te =
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
            case v of
                Env.VArray locs -> 
                    do putStr $ printArrTmp locs st'
                       return $ Right (ev, st', te, Env.VNothing)
                _ -> do putStr $ show v
                        return $ Right (ev, st', te, Env.VNothing)
runStm (Abs.StmPrintLn expr) ev st te = 
    do x <- exprToVal expr ev st te
       case x of
        Left e -> return $ Left e
        Right (v, st') -> case v of
            Env.VArray locs -> 
                do putStrLn $ printArrTmp locs st'
                   return $ Right (ev, st', te, Env.VNothing)
            _ -> do print v
                    return $ Right (ev, st', te, Env.VNothing)

printArrTmp :: [Env.Loc] -> Env.State -> String
printArrTmp [] st = ""
printArrTmp (l : ls) st = case Env.getValue l st of
    Env.VChar c -> c : (printArrTmp' ls st)
    v -> '[' : (show v) ++ (printArrTmp' ls st) ++ "]"
 

printArrTmp' :: [Env.Loc] -> Env.State -> String
printArrTmp' [] st = ""
printArrTmp' (l : ls) st = case Env.getValue l st of
    Env.VChar c -> c :  (printArrTmp' ls st)
    v -> ", " ++ (show v) ++ (printArrTmp' ls st) 

runBloc :: [Abs.Stm] -> Env.Environment -> Env.State -> Env.TypeEnv -> Env.Environment -> Env.TypeEnv ->
     IO (Either RuntimeError (Env.Environment, Env.State, Env.TypeEnv, Env.Value))
runBloc [] ev st te accev accte = return $ Right (accev, st, accte, Env.VNothing)
runBloc (s:ss) ev st te accev accte =
    do x <- runStm s ev st te
       case x of
        Left e -> return $ Left e
        Right (ev', st', te', v) -> if v /= Env.VNothing then return $ Right (accev, st', accte, v) else
            runBloc ss ev' st' te' accev accte

 
-- Right Left variable, Right Right type
runDec :: Abs.Dec -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError 
         (Either (Abs.Ident, Env.Value, Env.State) 
                 (Env.TypeName, Env.Type, Env.State)))
runDec (Abs.DVar at nm) ev st te = case Env.getTypeAbs at te of
        Right t -> case t of 
            Env.TStruct te _ decs ev -> 
                do xx <- createStruct' decs ev st te Env.emptyEnvironment 
                   case xx of
                    Left e -> return $ Left e
                    Right (v, st') -> return $ Right $ Left (nm, v, st')
            _ -> let (v, st') = Env.defValue t st ev in
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
    do x <- runDecs decs ev st te Env.emptySE decs
       case x of
        Left e -> return $ Left e
        Right (t, st') -> return $ Right $ Right (nm, t, st')
runDec (Abs.DFunc t nm params stm) ev st te = let par = Env.tParamsToVParams params [] in
        let l = Env.next st 
            fev = Env.addVariable nm l ev in
            let func = Env.VFunc par stm fev in
                let st' = Env.addValue l func st in
                    return $ Right $ Left (nm, func, st')




createStruct' :: [Abs.Dec] -> Env.Environment -> Env.State -> Env.TypeEnv -> Env.Environment ->
    IO (Either RuntimeError (Env.Value, Env.State))
createStruct' [] ev st te sev = return $ Right (Env.VStruct sev, st)
createStruct' (dec : ds) ev st te sev =
    do x <- runDec dec ev st te
       case x of
        Left e -> return $ Left e
        Right ( Left (nm, val, st')) -> let l = Env.next st' in
            let sev' = Env.addVariable nm l sev
                ev' = Env.addVariable nm l ev
                st'' = Env.addValue l val st' in
                    createStruct' ds ev' st'' te sev'
        Right ( Right (n, t, st')) -> let te' = Env.insertType n t te in
            createStruct' ds ev st' te' sev

-- parses declarations into struct
runDecs :: [Abs.Dec] -> Env.Environment -> Env.State -> Env.TypeEnv -> Env.StructEnv -> [Abs.Dec] ->
    IO (Either RuntimeError (Env.Type, Env.State))
runDecs [] ev st te acc dacc= return $ Right (Env.TStruct Env.emptyTypeEnv acc dacc ev, st)
runDecs (dec : ds) ev st te acc dacc = 
    do x <- runDec dec ev st te
       case x of
        Left e -> return $ Left e
        Right (Left (nm, val, st')) -> let acc' = Env.addToSE nm val acc 
                                           l = Env.next st' in
            let ev' = Env.addVariable nm l ev
                st'' = Env.addValue l val st' in
                    runDecs ds ev' st'' te acc' dacc
        Right (Right (nm, t, st')) -> let te' = Env.insertType nm t te in
            runDecs ds ev st' te' acc dacc



exprToVal :: Abs.Expr -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError (Env.Value, Env.State))
exprToVal (Abs.ExprAss var ex) ev st te = 
    do x <- varToLoc var ev st te
       case x of
        Left e -> return $ Left e
        Right (l, st') -> 
            do xx <- exprToVal ex ev st te
               case xx of
                Left e -> return $ Left e
                Right (v, st'') -> let st''' = Env.addValue l v st'' in
                    return $ Right (v, st''')
exprToVal (ExprAssO var ao ex) ev st te = case ao of
    Abs.AssAdd -> association var ex ev st te (+)
    Abs.AssSub -> association var ex ev st te (-)
    Abs.AssMul -> association var ex ev st te (*)
    Abs.AssDiv -> 
        do x <- exprToVal ex ev st te
           case x of
            Left e -> return $ Left e
            Right (Env.VInt i, _) -> if i == 0 then return $ Left ZeroDiv
                else association var ex ev st te (div)
    Abs.AssMod -> 
        do x <- exprToVal ex ev st te
           case x of
            Left e -> return $ Left e
            Right (Env.VInt i, _) -> if i == 0 then return $ Left ZeroDiv
                else association var ex ev st te (mod)


exprToVal (Abs.ExprIR var) ev st te =
    do x <- varToLoc var ev st te
       case x of
        Left e -> return $ Left e
        Right (l, st') -> let Env.VInt v = Env.getValue l st' in
            let st'' = Env.addValue l (Env.VInt (v+1)) st' in
                return $ Right (Env.VInt v, st'')
exprToVal (Abs.ExprIL var) ev st te =
    do x <- varToLoc var ev st te
       case x of
        Left e -> return $ Left e
        Right (l, st') -> let Env.VInt v = Env.getValue l st' in
            let st'' = Env.addValue l (Env.VInt (v+1)) st' in
                return $ Right (Env.VInt (v+1), st'')
exprToVal (Abs.ExprDR var) ev st te =
    do x <- varToLoc var ev st te
       case x of
        Left e -> return $ Left e
        Right (l, st') -> let Env.VInt v = Env.getValue l st' in
            let st'' = Env.addValue l (Env.VInt (v-1)) st' in
                return $ Right (Env.VInt v, st'')
exprToVal (Abs.ExprDL var) ev st te =
    do x <- varToLoc var ev st te
       case x of
        Left e -> return $ Left e
        Right (l, st') -> let Env.VInt v = Env.getValue l st' in
            let st'' = Env.addValue l (Env.VInt (v-1)) st' in
                return $ Right (Env.VInt (v-1), st'')

exprToVal (Abs.ExprAnd e1 e2) ev st te = 
    do x <- exprToVal e1 ev st te 
       case x of
        Left e -> return $ Left e
        Right (Env.VBool b1, st') ->
            do xx <- exprToVal e2 ev st' te
               case xx of
                Left e -> return $ Left e
                Right (Env.VBool b2, st'') -> return $ Right (Env.VBool (b1 && b2), st'')

exprToVal (Abs.ExprOr e1 e2) ev st te = 
    do x <- exprToVal e1 ev st te 
       case x of
        Left e -> return $ Left e
        Right (Env.VBool b1, st') ->
            do xx <- exprToVal e2 ev st' te
               case xx of
                Left e -> return $ Left e
                Right (Env.VBool b2, st'') -> return $ Right (Env.VBool (b1 || b2), st'')

exprToVal (Abs.ExprNot e) ev st te = 
    do x <- exprToVal e ev st te 
       case x of
        Left e -> return $ Left e
        Right (Env.VBool b, st') -> return $ Right (Env.VBool (not b), st')
 
exprToVal (Abs.ExprLt e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VBool (i1 < i2), st')

exprToVal (Abs.ExprLte e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VBool (i1 <= i2), st')

exprToVal (Abs.ExprEq e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VBool (i1 == i2), st')

exprToVal (Abs.ExprNEq e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VBool (i1 /= i2), st')

exprToVal (Abs.ExprGte e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VBool (i1 >= i2), st')

exprToVal (Abs.ExprGt e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VBool (i1 > i2), st')

exprToVal (Abs.ExprAdd e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VInt (i1 + i2), st')

exprToVal (Abs.ExprSub e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VInt (i1 - i2), st')

exprToVal (Abs.ExprMod e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> if i2 == 0 then return $ Left ZeroDiv else return $ Right (Env.VInt (mod i1 i2), st')

exprToVal (Abs.ExprMul e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> return $ Right (Env.VInt (i1 * i2), st')

exprToVal (Abs.ExprDiv e1 e2) ev st te =
    do x <- arithmeticExpr e1 e2 ev st te
       case x of
        Left e -> return $ Left e
        Right (i1, i2, st') -> if i2 == 0 then return $ Left ZeroDiv else return $ Right (Env.VInt (i1 `div` i2), st')




exprToVal (Abs.ExprVar var) ev st te = varToVal var ev st te
exprToVal (Abs.ExprVal val) _ st te = let (v, st') = valToVal val st in return $ Right (v, st')
exprToVal (Abs.ExprCall var exprs) ev st te = 
    do x <- varToVal var ev st te
       case x of
        Left e -> return $ Left e
        Right ((Env.VFunc params stm fev), st') ->
            do xx <- paramsToEnv params exprs fev ev st' te
               case xx of
                Left e -> return $ Left e
                Right (ev', st'') -> 
                    do xxx <- runStm stm ev' st'' te
                       case xxx of
                        Left e -> return $ Left e
                        Right (_, st''', _, v) -> return $ Right (v, st''')


association :: Abs.Var -> Abs.Expr -> Env.Environment -> Env.State -> Env.TypeEnv -> (Int -> Int -> Int) -> 
    IO (Either RuntimeError (Env.Value, Env.State))
association var expr ev st te f = 
    do x <- varToVal var ev st te
       case x of
        Left e -> return $ Left e
        Right (Env.VInt i1, st') ->
            do xx <- exprToVal expr ev st' te
               case xx of
                Left e -> return $ Left e
                Right (Env.VInt i2, st'') ->
                    let v = toInteger $ f i1 i2 in
                        exprToVal (Abs.ExprAss var (Abs.ExprVal (Abs.ValInt v))) ev st'' te


tmpStringVal :: [Char] -> Env.State -> [Env.Loc] -> ([Env.Loc], Env.State)
tmpStringVal [] st acc = (reverse acc, st)
tmpStringVal (h : hs) st acc = let l = Env.next st in
    let st' = Env.addValue l (Env.VChar h) st in
        tmpStringVal hs st' (l : acc)


valToVal :: Abs.Val -> Env.State -> (Env.Value, Env.State)
valToVal (Abs.ValInt i) st = (Env.VInt $ fromInteger i, st)
valToVal (Abs.ValChar c) st = (Env.VChar c, st)
valToVal (Abs.ValStr s) st = let (locs, st') = tmpStringVal s st [] in (Env.VArray locs, st')
valToVal Abs.ValTrue st = (Env.VBool True, st)
valToVal Abs.ValFalse st = (Env.VBool False, st)


varToVal :: Abs.Var -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError (Env.Value, Env.State))
varToVal (Abs.VarVar nm) ev st te = 
    let l = Env.getVariable nm ev in return $ Right (Env.getValue l st, st)
varToVal (Abs.VarArr var expr) ev st te = 
    do x <- varToVal var ev st te
       case x of
        Left e -> return $ Left e
        Right (arr@(Env.VArray _), st') -> 
            do xx <- exprToVal expr ev st' te
               case xx of
                Left e -> return $ Left e
                Right (idx, st'') -> case Env.getValFromArray idx arr of
                    Left e -> return $ Left $ EnvErr e
                    Right l -> return $ Right (Env.getValue l st'', st'')
varToVal (Abs.VarRec var nm) ev st te = 
    do x <- varToVal var ev st te
       case x of
        Left e -> return $ Left e
        Right (Env.VStruct ev', st') -> return $ Right (Env.getValue (Env.getVariable nm ev') st', st')

varToLoc :: Abs.Var -> Env.Environment -> Env.State -> Env.TypeEnv -> IO (Either RuntimeError (Env.Loc, Env.State))
varToLoc (Abs.VarVar nm) ev st te = return $ Right (Env.getVariable nm ev, st)
varToLoc (Abs.VarRec var nm) ev st te =
    do x <- varToVal var ev st te
       case x of
        Left e -> return $ Left e
        Right (Env.VStruct ev', st') -> let l = Env.getVariable nm ev' in
            return $ Right (l, st')
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

paramsToEnv :: [Env.Param] -> [Abs.Expr] -> Env.Environment -> Env.Environment -> Env.State -> Env.TypeEnv ->
    IO (Either RuntimeError (Env.Environment, Env.State))
paramsToEnv [] [] fev ev st te = return $ Right (fev, st)
paramsToEnv (p : ps) (e : es) fev ev st te = case p of
        Env.Val nm ->  
            do 
               x <- exprToVal e ev st te
               case x of
                Left e -> return $ Left e
                Right (v, st') -> let l = Env.next st' in
                    let fev' = Env.addVariable nm l fev
                        st'' = Env.addValue l v st' in
                        paramsToEnv ps es fev' ev st'' te
        Env.Ref nm -> case e of
            (ExprVar var) -> 
                do x <- varToLoc var ev st te
                   case x of
                    Left e -> return $ Left e
                    Right (l, st') -> let fev' = Env.addVariable nm l fev in
                        paramsToEnv ps es fev' ev st' te

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
            do putStrLn "type check was succesful!"
               runProgram p Env.emptyEnvironment Env.emptyState Env.emptyTypeEnv
               
                
--            Just e -> show e
        Just e -> print e


