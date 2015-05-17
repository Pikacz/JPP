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
    | TStruct TypeEnv
    | TFunc [(ParamName, ParamType)] ReturnType 
        deriving (Show, Eq)

structFromList:: [ (TypeName, Type) ] -> Type
structFromList l = TStruct $ typeEnvFromList l


type TypeName = String


data TypeEnv =
    TypeEnv { env :: Map.Map TypeName Type }
        deriving (Show, Eq)


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
    | VArray [Value]
    | VStruct Environment
    | VFunc -- ??
    | VVoid


defValue :: Type -> State -> (Value, State)
defValue TInt st = (VInt 0, st)
defValue TChar st = (VChar 'c', st)
defValue TStr st = (VString "", st)
defValue TBool st = (VBool False, st)
defValue (TArray t i) st = arrDef t st i []
defValue (TStruct te) st = let ev = env te in
         let atrs = Map.toList ev in
            structDef atrs st emptyEnvironment


structDef :: [(TypeName, Type)] -> State -> Environment -> (Value, State)
structDef [] st acc = (VStruct acc, st)
structDef ((nm, t) : atrs) st acc = let (v, st') = defValue t st in
        let l = next st' in
            let st'' = addValue l v st' in
                let acc' = addVariable (Abs.Ident nm) l acc in
                    structDef atrs st'' acc'

arrDef :: Type -> State -> Int -> [Value] -> (Value, State)
arrDef _ st 0 acc = (VArray acc, st)
arrDef t st i acc = let (v, st') = defValue t st in
        arrDef t st' (i - 1) (v : acc)

getValFromArray:: Value -> Value -> Value
getValFromArray (VInt i) (VArray l) = l !! i 


type Loc = Int
type VariableName = TypeName

data Environment = Environment (Map.Map TypeName Loc) 

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


instance Show EnvError where
    show (TypeDoNotExist nm tenv) = "Type " ++ (show nm) ++ " do not exist!\n" ++ (show tenv)

