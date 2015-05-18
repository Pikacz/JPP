module Environment where

import qualified Data.Map as Map
import qualified Absabc as Abs
import qualified Data.Maybe as Mb

data Type =
      TInt
    | TBool
    | TChar
    | TStr
    | TVoid
    | TArray Type Int
    | TStruct TypeEnv StructEnv
    | TFunc [(ParamName, ParamType)] ReturnType
        deriving (Show, Eq)

structFromList:: [ (TypeName, Type) ] -> Type
structFromList l = TStruct (typeEnvFromList l) emptySE


type TypeName = String


data TypeEnv =
    TypeEnv { env :: Map.Map TypeName Type }
        deriving (Show, Eq)


data StructEnv = StructEnv (Map.Map VariableName Value)
        deriving (Show, Eq)

emptySE :: StructEnv
emptySE = StructEnv $ Map.empty

addToSE :: Abs.Ident -> Value -> StructEnv -> StructEnv
addToSE (Abs.Ident nm) val (StructEnv se) = StructEnv $ Map.insert nm val se 

basicTypes :: [ (TypeName, Type) ]
basicTypes = [ ("int", TInt)
             , ("bool", TBool)
             , ("char", TChar)
             , ("string", TStr)
             , ("void", TVoid) ]


typeEnvFromList :: [ (TypeName, Type) ] -> TypeEnv
typeEnvFromList l = TypeEnv { env = Map.fromList l}


emptyTypeEnv :: TypeEnv
emptyTypeEnv = TypeEnv { env = Map.fromList basicTypes }


insertType :: TypeName -> Type -> TypeEnv -> TypeEnv
insertType nm t tenv = tenv { env = Map.insert nm t $ env tenv }


getType :: TypeName -> TypeEnv -> Either EnvError Type 
getType nm tenv = case Map.lookup nm (env tenv) of
                    Nothing -> Left $ TypeDoNotExist nm tenv
                    Just t  -> Right t


-- Functions
type ParamName = TypeName


data ParamType =
      PVal Type
    | PRef Type
        deriving (Show, Eq)


type ReturnType = Type


getTypeAbs :: Abs.Type -> TypeEnv -> Either EnvError Type
getTypeAbs Abs.TInt _ = Right TInt
getTypeAbs Abs.TBool _ = Right TBool
getTypeAbs Abs.TChar _ = Right TChar
getTypeAbs Abs.TStr _ = Right TStr
getTypeAbs Abs.TVoid _ = Right TVoid
getTypeAbs (Abs.TArr t) tv = case getTypeAbs t tv of
            Right t -> Right $ TArray t 0
            Left e -> Left e
getTypeAbs (Abs.TCust (Abs.Ident nm)) tv = getType nm tv



--Values

data Value = 
      VInt Int
    | VBool Bool
    | VChar Char
    | VString String
    | VArray [Loc]
    | VStruct Environment
    | VFunc [Param] Abs.Stm Environment
    | VVoid
    | VNothing
    deriving (Eq)

instance Show Value where
    show (VInt i) = show i
    show (VBool b) = show b
    show (VChar c) = show c
    show (VString s) = s
    show (VArray locs) = "Array"
    show (VStruct _) = "Struct"
    show (VFunc _ _ _) = "Function"

data Param = Ref Abs.Ident | Val Abs.Ident deriving (Show, Eq)

defValue :: Type -> State -> Environment -> (Value, State)
defValue TInt st _ = (VInt 0, st)
defValue TChar st _ = (VChar 'c', st)
defValue TStr st _ = (VString "", st)
defValue TBool st _ = (VBool False, st)
defValue (TArray t i) st ev = arrDef t st ev i []
defValue (TStruct _ (StructEnv ev)) st e = let atrs = Map.toList ev in
            structDef atrs st e emptyEnvironment



structDef :: [(VariableName, Value)] -> State -> Environment -> Environment-> (Value, State)
structDef [] st ev acc = (VStruct acc, st)
structDef ((nm, v) : atrs) st ev acc = 
        let l = next st in
            let st' = addValue l v st in
                let acc' = addVariable (Abs.Ident nm) l acc 
                    ev' = addVariable (Abs.Ident nm) l ev in
                    structDef atrs st' ev' acc'

arrDef :: Type -> State -> Environment -> Int -> [Loc] -> (Value, State)
arrDef _ st ev 0 acc = (VArray acc, st)
arrDef t st ev i acc = let (v, st') = defValue t st ev in
        let l = next st' in
            let st'' = addValue l v st' in
                arrDef t st'' ev (i - 1) (l : acc)


tParamsToVParams :: [Abs.Param] -> [Param] -> [Param]
tParamsToVParams [] acc = reverse acc
tParamsToVParams (p : rest) acc = case p of
        Abs.PVal t nm -> let acc' = (Val nm) : acc in
            tParamsToVParams rest acc'
        Abs.PVar t nm -> let acc' = (Ref nm) : acc in
            tParamsToVParams rest acc'
                

getValFromArray:: Value -> Value -> Either EnvError Loc
getValFromArray (VInt i) (VArray ls) = if i >= length ls then Left ArrayOutOfBound 
        else let l = ls !! i in
            Right $ l


type Loc = Int
type VariableName = TypeName

data Environment = Environment (Map.Map TypeName Loc) deriving (Show, Eq) 

addVariable :: Abs.Ident -> Loc -> Environment -> Environment
addVariable (Abs.Ident nm) l (Environment env) = Environment $ Map.insert nm l env

getVariable :: Abs.Ident -> Environment -> Loc -- typecheck guarantes that variable exists
getVariable (Abs.Ident nm) (Environment env) = Mb.fromJust $ Map.lookup nm env

emptyEnvironment :: Environment
emptyEnvironment = Environment $ Map.empty


data State = State (Map.Map Loc Value) Loc

addValue :: Loc -> Value -> State -> State
addValue l val (State st sl) = let st' = Map.insert l val st in 
        if l >= sl then State st' l else State st' sl


getValue :: Loc -> State -> Value -- it should always return value!
getValue l (State st sl) = Mb.fromJust $ Map.lookup l st


next :: State -> Loc
next (State st sl) = sl + 1


emptyState :: State
emptyState = State (Map.empty) 1

-- Errors
data EnvError = 
      TypeDoNotExist TypeName TypeEnv
    | ArrayOutOfBound


instance Show EnvError where
    show (TypeDoNotExist nm tenv) = "Type " ++ (show nm) ++ " do not exist!\n" ++ (show tenv)
    show (ArrayOutOfBound) = "index out of array bounds"
