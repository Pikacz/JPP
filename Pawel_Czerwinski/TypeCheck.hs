module TypeCheck where
-- TODO Call!
import qualified Absabc as Abs
import qualified Environment as Env
import qualified Data.Map as Map


exprToType :: Abs.Expr -> VariableType -> Env.TypeEnv -> Either TypeError Env.Type
exprToType (Abs.ExprVal v) _  _ = Right $ valToType v
exprToType (Abs.ExprVar v) vt te = varToType v vt te
-- Arithmetic
exprToType (Abs.ExprAdd e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TInt
exprToType (Abs.ExprSub e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TInt
exprToType (Abs.ExprMod e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TInt
exprToType (Abs.ExprMul e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TInt
exprToType (Abs.ExprDiv e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TInt
-- Bool expressions
exprToType (Abs.ExprAnd e1 e2) vt te = check2Types e1 e2 vt te Env.TBool Env.TBool
exprToType (Abs.ExprOr e1 e2) vt te = check2Types e1 e2 vt te Env.TBool Env.TBool
exprToType (Abs.ExprNot e) vt te = check1Type e vt te Env.TBool Env.TBool
-- Compare
exprToType (Abs.ExprLt e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TBool
exprToType (Abs.ExprLte e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TBool
exprToType (Abs.ExprEq e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TBool
exprToType (Abs.ExprNEq e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TBool
exprToType (Abs.ExprGte e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TBool
exprToType (Abs.ExprGt e1 e2) vt te = check2Types e1 e2 vt te Env.TInt Env.TBool
-- association
exprToType (Abs.ExprAss var expr) vt te = checkAssociation var expr vt te
exprToType (Abs.ExprAssO var _ expr) vt te = checkAssociationO var expr vt te
-- ++ / --
exprToType (Abs.ExprIR var) vt te = checkInc var vt te
exprToType (Abs.ExprIL var) vt te = checkInc var vt te
exprToType (Abs.ExprDR var) vt te = checkInc var vt te
exprToType (Abs.ExprDL var) vt te = checkInc var vt te
-- call
exprToType (Abs.ExprCall var exprs) vt te = case varToType var vt te of
                    Left e -> Left e
                    Right (Env.TFunc params rt ) -> case checkParams exprs params vt te of
                        Nothing -> Right rt
                        Just e -> Left e



checkInc :: Abs.Var -> VariableType -> Env.TypeEnv -> Either TypeError Env.Type
checkInc var vt te = case varToType var vt te of
        Right Env.TInt -> Right Env.TInt
        Right t -> Left $ WrongType { expected = Env.TInt, actual = t }
        Left e -> Left e


checkAssociationO :: Abs.Var -> Abs.Expr -> VariableType -> Env.TypeEnv -> Either TypeError Env.Type
checkAssociationO var expr vt te = case varToType var vt te of
                        Right Env.TInt -> check1Type expr vt te Env.TInt Env.TInt
                        Right t -> Left WrongType { expected = Env.TInt, actual = t }
                        Left e -> Left e


checkAssociation :: Abs.Var -> Abs.Expr -> VariableType -> Env.TypeEnv -> Either TypeError Env.Type
checkAssociation var expr vt te = case varToType var vt te of
                        Right t -> check1Type expr vt te t t
                        Left e -> Left e


varType :: Abs.Expr -> VariableType -> Env.TypeEnv -> Either TypeError Env.Type
varType (Abs.ExprVar v) vt te = varToType v vt te
varType e _ _ = Left $ ExceptedVariable e

check1Type :: Abs.Expr -> VariableType -> Env.TypeEnv -> Env.Type -> Env.Type -> Either TypeError Env.Type
check1Type e vt te t1 t2 = case isType e t1 vt te of
                    Nothing -> Right t2
                    Just er -> Left er


check2Types :: Abs.Expr -> Abs.Expr -> VariableType -> Env.TypeEnv -> Env.Type -> Env.Type -> Either TypeError Env.Type
check2Types e1 e2 vt te t1 t2 = case bothType e1 e2 t1 vt te of
                    Nothing -> Right t2
                    Just er -> Left er


isType :: Abs.Expr -> Env.Type -> VariableType -> Env.TypeEnv -> Maybe TypeError
isType e t vt te = case exprToType e vt te of
                    Right t' -> if t == t' then Nothing
                        else Just $ WrongType { expected = t, actual = t'}
                    Left er -> Just er



bothType :: Abs.Expr -> Abs.Expr -> Env.Type -> VariableType -> Env.TypeEnv -> Maybe TypeError
bothType e1 e2 t vt te = case isType e1 t vt te of
                    Nothing -> isType e2 t vt te
                    Just er -> Just er



-- Functions
checkParams :: [Abs.Expr] -> [(Env.ParamName, Env.ParamType)] -> VariableType -> Env.TypeEnv -> Maybe TypeError
checkParams [] [] vt te = Nothing
checkParams _ [] vt te = Just WrongNumberOfParameters
checkParams [] _ vt te = Just WrongNumberOfParameters
checkParams (e : es) ((pn, pt) : ps) vt te = case pt of
        Env.PRef t -> case isVariable e vt te of
            Left e -> Just e
            Right t' -> if t == t' then checkParams es ps vt te else Just $ WrongType {expected=t, actual=t'}
        Env.PVal t -> case exprToType e vt te of
            Left e -> Just e
            Right t' -> if t == t' then checkParams es ps vt te else Just $ WrongType {expected=t, actual=t'}



isVariable :: Abs.Expr -> VariableType -> Env.TypeEnv -> Either TypeError Env.Type
isVariable (Abs.ExprVar var) vt te = varToType var vt te
isVariable exp _ _ = Left $ ExceptedVariable exp



-- Variablse
varToType :: Abs.Var -> VariableType -> Env.TypeEnv -> Either TypeError Env.Type
varToType (Abs.VarVar  nm) vt te = getVariable nm vt
varToType (Abs.VarRec var (Abs.Ident nm)) vt te = case varToType var vt te of
                    Right (Env.TStruct structVT _ _ _) -> getVariable (Abs.Ident nm) structVT
                    Right t -> Left $ ExceptedStruct t nm
                    Left e -> Left e
varToType (Abs.VarArr var expr) vt te = case exprToType expr vt te of
                    Right Env.TInt -> case varToType var vt te of
                                        Right (Env.TArray t _) -> Right t
                                        Right (Env.TStr) -> Right Env.TChar
                                        Left t -> Left t
                                        Right _ -> Left $ ExceptedArray (Abs.VarArr var expr)
                    Right t -> Left WrongType { expected = Env.TInt, actual = t }
                    Left e -> Left e


-- Values
valToType :: Abs.Val -> Env.Type
valToType (Abs.ValInt _)  = Env.TInt
valToType (Abs.ValChar _) = Env.TChar
valToType (Abs.ValStr _)  = Env.TArray Env.TChar 0
valToType Abs.ValTrue     = Env.TBool
valToType Abs.ValFalse    = Env.TBool


-- VariableType
type VariableType = Env.TypeEnv
type VariableName = Env.TypeName


emptyVariableType::VariableType
emptyVariableType = Env.TypeEnv{ Env.env = Map.empty }


insertVariable :: Abs.Ident -> Env.Type -> VariableType -> VariableType
insertVariable (Abs.Ident nm) t vt = vt { Env.env = Map.insert nm t $ Env.env vt }


getVariable :: Abs.Ident -> VariableType -> Either TypeError Env.Type
getVariable (Abs.Ident nm) vt = case Map.lookup nm (Env.env vt) of
                                    Nothing -> Left $ VariableDoNotExist nm vt
                                    Just t  -> Right t


-- Declarations



parseDecs :: [Abs.Dec] -> VariableType -> Env.TypeEnv -> Env.TypeEnv -> Either TypeError Env.TypeEnv
parseDecs [] vt te acc = Right acc
parseDecs (d : ds) vt te acc = case parseDec d vt te of
        Left e -> Left e
        Right (Left (nm, t)) -> let vt' = insertVariable nm t vt
                                    acc' = insertVariable nm t acc
                                in parseDecs ds vt' te acc'
        Right (Right (nm, t)) -> let te' = (Env.insertType nm t te)
                                in parseDecs ds vt te' acc


-- Right Left var; Right Right type
parseDec :: Abs.Dec -> VariableType -> Env.TypeEnv -> Either TypeError (Either (Abs.Ident, Env.Type) (Env.TypeName, Env.Type))
parseDec (Abs.DVar t nm) vt te = case Env.getTypeAbs t te of
        Left er -> Left  (EnvError er)
        Right tp -> Right $ Left (nm, tp)
parseDec (Abs.DAuto nm expr) vt te = case exprToType expr vt te of
        Left err -> Left err
        Right tp -> Right $ Left (nm, tp)
parseDec (Abs.DInit t nm expr) vt te = case Env.getTypeAbs t te of
        Left er -> Left  (EnvError er)
        Right tp -> case exprToType expr vt te of
            Left err -> Left err
            Right tp' -> if tp == tp' then Right $ Left (nm, tp)
                else Left $ WrongType { expected = tp, actual = tp' }
parseDec (Abs.DArr t nm expr) vt te = case Env.getTypeAbs t te of
        Left er -> Left  (EnvError er)
        Right tp -> case exprToType expr vt te of
            Left er -> Left er
            Right Env.TInt -> Right $ Left (nm, Env.TArray tp 0)
            Right t -> Left $ WrongType { expected = Env.TInt, actual = t }
parseDec (Abs.DRec (Abs.Ident nm) decs) vt te = case parseDecs decs vt te Env.emptyTypeEnv of
        Left er -> Left er
        Right te -> let t = Env.TStruct te Env.emptySE [] Env.emptyEnvironment
                    in Right $ Right (nm, t)
parseDec (Abs.DFunc t nm params stm) vt te = case parseParams params vt te [] of
        Left er -> Left er
        Right (vt', fpr) -> case Env.getTypeAbs t te of
            Left e -> Left $ EnvError e
            Right t' -> let vt''' = insertVariable nm (Env.TFunc fpr t' ) vt' in case parseStm stm vt''' te t' of
                Left e -> Left e
                Right (vt'', te'', t'') -> if t' /= t'' then Left ( FunctionWrongRet nm t' t'' ) else
                        Right $ Left $ (nm, (Env.TFunc fpr t' ))



identToParamName :: Abs.Ident -> Env.ParamName
identToParamName (Abs.Ident nm) = nm


parseParams :: [Abs.Param] -> VariableType -> Env.TypeEnv -> [(Env.ParamName, Env.ParamType)] ->
        Either TypeError (VariableType, [(Env.ParamName, Env.ParamType)])
parseParams [] vt te acc = Right (vt, reverse acc)
parseParams (p : ps) vt te acc = case p of
        Abs.PVal t nm -> let pn = identToParamName nm
                             mt' = Env.getTypeAbs t te in case mt' of
            Left e -> Left $ EnvError e
            Right t' -> let vt'= insertVariable nm t' vt
                            acc' = (pn, Env.PVal t') : acc in
                        parseParams ps vt' te acc'
        Abs.PVar t nm -> let pn = identToParamName nm
                             mt' = Env.getTypeAbs t te in case mt' of
            Left e -> Left $ EnvError e
            Right t' -> let vt'= insertVariable nm t' vt
                            acc' = (pn, Env.PRef t') : acc in
                        parseParams ps vt' te acc'


parseStmBloc :: [Abs.Stm] -> VariableType -> Env.TypeEnv -> Env.Type -> (VariableType, Env.TypeEnv, Env.Type) ->
        Either TypeError (VariableType, Env.TypeEnv, Env.Type)
parseStmBloc [] vt te t acc = Right acc
parseStmBloc (s : ss) vt te t (vt'', te'', t'') = case parseStm s vt te t of
        Left e -> Left e
        Right (vt', te', t') -> if t' /= Env.TVoid then
                                    parseStmBloc ss vt' te' t (vt'', te'', t')
                                else parseStmBloc ss vt' te' t (vt'', te'', t'')


-- stm -> variableEnv -> typeEnv -> expectedType -> (variableEnv, TypeEnv, returnedType)
parseStm :: Abs.Stm -> VariableType -> Env.TypeEnv -> Env.Type -> Either TypeError (VariableType, Env.TypeEnv, Env.Type)
parseStm (Abs.StmExpr expr) vt te _ = case exprToType expr vt te of
        Left e -> Left e
        Right _ -> Right (vt, te, Env.TVoid)
parseStm (Abs.StmDec dec) vt te _ = case parseDec dec vt te of
        Left e -> Left e
        Right (Left (nm, t)) -> let vt' = insertVariable nm t vt
                                in Right (vt', te, Env.TVoid)
        Right (Right (nm, t)) -> let te' = Env.insertType nm t te
                                 in Right (vt, te', Env.TVoid)
parseStm (Abs.StmBloc sts) vt te t = parseStmBloc sts vt te t (vt, te, Env.TVoid)
parseStm (Abs.StmWhile expr stm) vt te t = case isType expr Env.TBool vt te of
        Nothing -> parseStm (Abs.StmBloc [stm]) vt te t
        Just e -> Left e
parseStm (Abs.StmIf expr stm) vt te t = case isType expr Env.TBool vt te of
        Nothing -> case parseStm (Abs.StmBloc [stm]) vt te t of
            Left e -> Left e
            Right (vt', te', _) -> Right (vt, te, Env.TVoid)
        Just e -> Left e
parseStm (Abs.StmIfE expr stm1 stm2) vt te t = case isType expr Env.TBool vt te of
        Just e -> Left e
        Nothing -> case parseStm (Abs.StmBloc [stm1]) vt te t of
            Left e -> Left e
            Right (_, _, t') -> case parseStm (Abs.StmBloc [stm2]) vt te t of
                Left e -> Left e
                Right (_, _, t'') -> if t' == t'' then
                                        Right (vt, te, t')
                                     else Right (vt, te, Env.TVoid)
parseStm (Abs.StmFor dec expr stm1 stm2) vt te t = case parseDec dec vt te of
        Left e -> Left e
        Right (Left (nm, t)) -> let vt' = insertVariable nm t vt in
            case parseStm (Abs.StmWhile expr (Abs.StmBloc [stm2, stm1])) vt' te t of
                Left e -> Left e
                Right (_, _, t') -> Right (vt, te, t')
        Right (Right (nm, t)) -> let te' = Env.insertType nm t te in
            case parseStm (Abs.StmWhile expr (Abs.StmBloc [stm2, stm1])) vt te' t of
                Left e -> Left e
                Right (_, _, t') -> Right (vt, te, t')
parseStm (Abs.StmPrint expr) vt te t = case exprToType expr vt te of
        Left e -> Left e
        Right _ -> Right (vt, te, Env.TVoid)
parseStm (Abs.StmPrintLn expr) vt te t = parseStm (Abs.StmPrint expr) vt te t
parseStm (Abs.StmRead var) vt te t = case varToType var vt te of
        Left e -> Left e
        Right _ -> Right (vt, te, Env.TVoid)
parseStm Abs.StmRet vt te t = if (t == Env.TVoid) then
                                Right (vt, te, Env.TVoid)
                              else Left $ WrongTypeReturn t Env.TVoid
parseStm (Abs.StmRetV expr) vt te t = case exprToType expr vt te of
        Left e -> Left e
        Right t' -> if (t == t') then
                        Right (vt, te, t')
                    else Left $ WrongTypeReturn t t'



parseProg :: Abs.Program -> VariableType -> Env.TypeEnv -> Maybe TypeError
parseProg (Abs.Prog []) _ _ = Nothing
parseProg (Abs.Prog (st : sts)) vt te = case parseStm st vt te Env.TVoid of
        Right (vt', te', _) -> parseProg (Abs.Prog sts) vt' te'
        Left e -> Just e


-- Errors
data TypeError =
      WrongType { expected :: Env.Type, actual :: Env.Type }
    | VariableDoNotExist VariableName VariableType
    | EnvError Env.EnvError
    | ExceptedStruct Env.Type VariableName
    | ExceptedArray Abs.Var
    | ExceptedVariable Abs.Expr
    | VoidVariable
    | IncorrectArrayDec
    | NotImplemented String
    | WrongTypeReturn Env.Type Env.Type
    | FunctionWrongRet Abs.Ident Env.Type Env.Type
    | WrongNumberOfParameters

instance Show TypeError where
    show (WrongType { expected = t1, actual = t2} ) =
        "Can't bind actual type " ++ (show t2) ++ " with expected " ++ (show t1)
    show (EnvError e) = show e
    show (VariableDoNotExist nm vt) =
        "Variable " ++ (show nm) ++ " do not exist " ++ (show vt)
    show (ExceptedStruct t nm) =
        (show nm) ++ " should be a struct type not " ++ (show t)
    show (ExceptedArray var) =
        (show var) ++ " do not refer to array type :c"
    show (ExceptedVariable expr) =
        (show expr) ++ " is not variable"
    show (VoidVariable) =
        "void can't be type of variable"
    show (IncorrectArrayDec) =
        "type[] variable is incorrect declaration use type variable[ size ] instead"
    show (NotImplemented s) =
        "TypeCheck: " ++ s ++ " is not implemented!"
    show (WrongTypeReturn t1 t2) =
        "Expected return type " ++ (show t1) ++ " got " ++ (show t2)
    show (FunctionWrongRet (Abs.Ident nm) t1 t2) =
        "function " ++ nm ++ " should return " ++ (show t1) ++ " not " ++ (show t2)
    show WrongNumberOfParameters =
        "Wrong number of parameters in function call"
