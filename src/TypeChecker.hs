module TypeChecker where

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import System.IO
import qualified Data.Map as Map
import Data.List
import qualified AbsLatte as L

type Pos = L.BNFC'Position

posShow :: Pos -> String
posShow Nothing = ""
posShow (Just (line, col)) = show line ++ ":" ++ show col

formatError :: Pos -> String -> TypeCheckerMonad a
formatError pos err = throwError (errMessage pos err)

errMessage :: Pos -> String -> String
errMessage pos err = posShow pos ++ ": " ++ err


lStrType :: L.Type -> String
lStrType (L.Int _) = "int"
lStrType (L.Str _) = "string"
lStrType (L.Bool _) = "boolean"
lStrType (L.Class _ (L.Ident c)) = c
lStrType (L.Void _ ) = "void"
lStrType (L.Fun _ retType args) = "fun <" ++ lStrType retType ++ "> (" ++ (intercalate ", " $ map lStrType args) ++ ")"

data RetState = RetOk
              | RetBad
              | RetTBD
              deriving (Eq, Ord)

update :: RetState -> RetState -> RetState
update RetOk _ = RetOk
update RetBad _ = RetBad
update RetTBD ret = ret

isFuncType :: String -> Bool
isFuncType f = head f == '#'

getRetType :: String -> String
getRetType f =
    case isFuncType f of
        False -> "#error"
        True -> fromSquareBrackets f False where
            fromSquareBrackets :: String -> Bool -> String
            fromSquareBrackets ('<' : rest) False = fromSquareBrackets rest True
            fromSquareBrackets (_ : rest) False = fromSquareBrackets rest False
            fromSquareBrackets ('>' : _) True = []
            fromSquareBrackets (c : rest) True = c : fromSquareBrackets rest True

getArgsTypes :: String -> [String]
getArgsTypes f = 
    case isFuncType f of
        False -> ["#error"]
        True -> fromRoundBrackets f False [] [] where
            fromRoundBrackets :: String -> Bool -> String -> [String] -> [String]
            fromRoundBrackets ('(' : rest) False _ _ = fromRoundBrackets rest True [] []
            fromRoundBrackets (_ : rest) False _ _ = fromRoundBrackets rest False [] []
            fromRoundBrackets (')' : _) True word res = if word == [] then res else res ++ [word]
            fromRoundBrackets (',' : (' ' : rest)) True word res = fromRoundBrackets rest True [] (res ++ [word])
            fromRoundBrackets (c : rest) True word res = fromRoundBrackets rest True (word ++ [c]) res

fromArg :: L.Arg -> Type
fromArg (L.Arg _ t _) = lStrType t

type Type = String
type TypeEnv = Map.Map String (Type, Depth)
type TypeStore = Map.Map String (Maybe Type)
type ClassMap = Map.Map String ([(Type, String)], [(Type, String)]) -- left attributes, right methods
type Depth = Int

data TCState = TCState {curFunRetType :: Type, typeStore :: TypeStore, pos :: Pos, classMap :: ClassMap}
initTCState :: Type -> TypeStore -> Pos -> ClassMap -> TCState
initTCState t st p cm = TCState {curFunRetType = t, typeStore = st, pos = p, classMap = cm}

isValidTypeM :: String -> TypeCheckerMonad Bool
isValidTypeM t = do
    st <- gets typeStore
    case Map.lookup t st of
        Nothing -> return False
        Just _ -> return True

isClassType :: String -> TypeCheckerMonad Bool
isClassType t = do
    valid <- isValidTypeM t
    if valid == False then do
        return False
    else do
        case t of
            "int" -> return False
            "boolean" -> return False
            "string" -> return False
            _ -> return True

exprToIdent :: L.Expr -> TypeCheckerMonad String
exprToIdent (L.EVar _ (L.Ident ident)) = return ident
exprToIdent (L.EAttr _ exp (L.Ident ident)) = do
    str <- exprToIdent exp
    return $ str ++ "." ++ ident
exprToIdent exp = formatError (L.hasPosition exp) "Left side of assignment should be lvalue"

type TypeCheckerMonad a = StateT TCState (ReaderT TypeEnv (Except String)) a
runTypeCheckerMonad :: TCState -> TypeEnv -> TypeCheckerMonad a -> Either String (a, TCState)
runTypeCheckerMonad st env ev = runExcept (runReaderT (runStateT ev st) env)

updateEnv :: TypeEnv -> Type -> String -> [(Type, String)] -> Depth -> TypeEnv
updateEnv env t ident [] depth = Map.insert ident (t, depth) env
updateEnv env t ident ((typ, str) : rest) depth = Map.insert (ident ++ "." ++ str) (typ, depth) (updateEnv env t ident rest depth)

isSubClass :: Type -> Type -> TypeCheckerMonad Bool
isSubClass sub super = do
    if sub == super then
        return True
    else do
        st <- gets typeStore
        case Map.lookup sub st of
            Nothing -> return False
            Just Nothing -> return False
            Just (Just f) -> isSubClass f super

areSubClasses :: [Type] -> [Type] -> TypeCheckerMonad Bool
areSubClasses [] [] = return True
areSubClasses [] _ = return False
areSubClasses _ [] = return False
areSubClasses (garg : restg) (farg : restf) = do
    subclass <- isSubClass garg farg
    case subclass of
        False -> return False
        True -> areSubClasses restg restf
    

checkStmt :: [L.Stmt] -> RetState -> Depth -> TypeCheckerMonad RetState
checkStmt [] retst _ = return retst
checkStmt (L.Empty _ : rest) retst depth = checkStmt rest retst depth
checkStmt (L.BStmt _ (L.Block _ stmts) : rest) retst depth = do
    ret1 <- checkStmt stmts retst (depth + 1)
    checkStmt rest (update retst ret1) depth
checkStmt (L.Decl _ _ [] : rest) retst depth = checkStmt rest retst depth
checkStmt (L.Decl pos typ ((L.NoInit posi (L.Ident ident)) : items) : rest) retst depth = do
    let t = lStrType typ
    valid <- isValidTypeM t

    case valid of
        True -> do
            env <- ask
            case Map.lookup ident env of
                Just (_, 0) -> formatError pos $ "Cannot name a variable with the same indetificator '" ++ ident ++ "' as defined function"
                Just (_, dep) | dep == depth -> formatError pos $ "Redefinition of variable '" ++ ident ++ "' in the block"
                _ -> do 
                    classt <- isClassType t
                    case classt of
                        False -> local (Map.insert ident (t, depth)) (checkStmt (L.Decl pos typ items : rest) retst depth)
                        True -> do
                            cm <- gets classMap
                            case Map.lookup t cm of
                                Nothing -> formatError pos $ "Type '" ++ show t ++ "' is not declared as class"
                                Just (attrs, methods) -> do
                                    env <- ask
                                    let newEnv = updateEnv env t ident (attrs ++ methods) depth
                                    local (\_ -> newEnv) (checkStmt (L.Decl pos typ items : rest) retst depth)
        False -> formatError pos $ "Cannot declare a variable with type " ++ show t
checkStmt (L.Decl pos typ (L.Init posi (L.Ident ident) expr : items) : rest) retst depth = do
    let t = lStrType typ
    valid <- isValidTypeM t

    case valid of
        True -> do
            env <- ask
            case Map.lookup ident env of
                Just (_, 0) -> formatError pos $ "Cannot name a variable with the same indetificator '" ++ ident ++ "' as defined function"
                Just (_, dep) | dep == depth -> formatError pos $ "Redefinition of variable '" ++ ident ++ "' in the block"
                _ -> do
                    st <- get
                    let expt = checkExprM st env expr
                    case expt of
                        Right exprType -> do
                            subclass <- isSubClass exprType t
                            if subclass then do
                                classt <- isClassType t
                                case classt of
                                    False -> local (Map.insert ident (t, depth)) (checkStmt (L.Decl pos typ items : rest) retst depth)
                                    True -> do
                                        cm <- gets classMap
                                        case Map.lookup t cm of
                                            Nothing -> formatError pos $ "Type '" ++ show t ++ "' is not declared as class"
                                            Just (attrs, methods) -> do
                                                env <- ask
                                                let newEnv = updateEnv env t ident (attrs ++methods) depth
                                                --formatError pos $ show newEnv
                                                local (\_ -> newEnv) (checkStmt (L.Decl pos typ items : rest) retst depth)
                            else
                                formatError posi $ "Variable '" ++ ident ++ "' initialized with different type: expected " ++ show t ++ ", received " ++ show exprType
                        Left err -> formatError pos err
        False -> formatError pos $ "Trying to declare variable with non-valid type"
checkStmt (L.Ass pos (L.Ident ident) expr : rest) retst depth = do
    env <- ask
    case Map.lookup ident env of
        Just (t, _) -> do
            st <- get
            let expt = checkExprM st env expr
            case expt of
                Right exprType -> do
                    subclass <- isSubClass exprType t
                    if subclass then do
                        classt <- isClassType t
                        case classt of
                            False -> checkStmt rest retst depth
                            True -> do
                                cm <- gets classMap
                                case Map.lookup t cm of
                                    Nothing -> formatError pos $ "Type '" ++ show t ++ "' is not declared as class (bug)"
                                    Just (attrs, methods) -> do
                                        env <- ask
                                        let newEnv = updateEnv env t ident (attrs ++ methods) depth
                                        local (\_ -> newEnv) (checkStmt rest retst depth)
                    else
                        formatError pos $ "Assignment to variable of type " ++ show t ++ " with value of type " ++ show exprType
                Left err -> formatError pos err
        Nothing -> formatError pos $ "Assignment to undefined variable '" ++ ident ++ "'"
checkStmt (L.Ass2 pos exprleft (L.Ident i) exprright : rest) retst depth = do
    str <- exprToIdent exprleft
    let ident = str ++ "." ++ i
    env <- ask
    case Map.lookup ident env of
        Just (t, _) -> do
            st <- get
            let expt = checkExprM st env exprright
            case expt of
                Right exprType -> do
                    subclass <- isSubClass exprType t
                    if subclass then do
                        classt <- isClassType t
                        case classt of
                            False -> checkStmt rest retst depth
                            True -> do
                                cm <- gets classMap
                                case Map.lookup t cm of
                                    Nothing -> formatError pos $ "Type '" ++ show t ++ "' is not declared as class (bug)"
                                    Just (attrs, methods) -> do
                                        env <- ask
                                        let newEnv = updateEnv env t ident (attrs ++ methods) depth
                                        local (\_ -> newEnv) (checkStmt rest retst depth)
                    else
                        formatError pos $ "Assignment to variable of type " ++ show t ++ " with value of type " ++ show exprType
                Left err -> formatError pos err
        Nothing -> formatError pos $ "Assignment to undefined variable '" ++ ident ++ "'"
checkStmt (L.Incr pos (L.Ident ident) : rest) retst depth = do
    env <- ask
    case Map.lookup ident env of
        Nothing -> formatError pos $ "Increment of undefined variable '" ++ ident ++ "'"
        Just ("int", _) -> checkStmt rest retst depth
        Just (t, _) -> formatError pos $ "Increment of variable of type " ++ show t ++ ", type int expected"
checkStmt (L.Incr2 pos expr (L.Ident i) : rest) retst depth = do
    str <- exprToIdent expr
    let ident = str ++ "." ++ i
    env <- ask
    case Map.lookup ident env of
        Nothing -> formatError pos $ "Increment of undefined variable '" ++ ident ++ "'"
        Just ("int", _) -> checkStmt rest retst depth
        Just (t, _) -> formatError pos $ "Increment of variable of type " ++ show t ++ ", type int expected"
checkStmt (L.Decr pos (L.Ident ident) : rest) retst depth = do
    env <- ask
    case Map.lookup ident env of
        Nothing -> formatError pos $ "Decrement of undefined variable '" ++ ident ++ "'"
        Just ("int", _) -> checkStmt rest retst depth
        Just (t, _) -> formatError pos $ "Decrement of variable of type " ++ show t ++ ", type int expected"
checkStmt (L.Decr2 pos expr (L.Ident i) : rest) retst depth = do
    str <- exprToIdent expr
    let ident = str ++ "." ++ i
    env <- ask
    case Map.lookup ident env of
        Nothing -> formatError pos $ "Decrement of undefined variable '" ++ ident ++ "'"
        Just ("int", _) -> checkStmt rest retst depth
        Just (t, _) -> formatError pos $ "Decrement of variable of type " ++ show t ++ ", type int expected"
checkStmt (L.Ret pos expr : rest) retst depth = do
    env <- ask
    st <- get
    let expt = checkExprM st env expr
    case expt of
        Right exprType -> do
            case Map.lookup exprType (typeStore st) of
                Nothing -> formatError pos $ "Invalid type of return expression"
                Just _ -> do
                    subclass <- isSubClass exprType (curFunRetType st)
                    case subclass of
                        True -> checkStmt rest (update retst RetOk) depth
                        False -> formatError pos $ "Function of type " ++ show (curFunRetType st) ++ " cannot return type " ++ show exprType
        Left err -> formatError pos err
checkStmt (L.VRet pos : rest) retst depth = do
    env <- ask
    st <- gets curFunRetType
    if st == "void" then
        checkStmt rest (update retst RetOk) depth
    else
        formatError pos $ "Cannot return non-void (" ++ show st ++ ") value from void function"
checkStmt (L.Cond pos expr stmt : rest) retst depth = do
    env <- ask
    st <- get
    let expt = checkExprM st env expr
    case expt of
        Right exprType -> do
            case exprType of
                "boolean" -> do
                    case expr of
                        L.ELitTrue _ -> do
                            ret1 <- checkStmt [stmt] RetTBD (depth + 1)
                            checkStmt rest (update retst ret1) depth
                        _ -> do
                            _ <- checkStmt [stmt] retst (depth + 1)
                            checkStmt rest retst depth
                t -> formatError pos $ "If-condition has to be boolean type, received " ++ show t
        Left err -> formatError pos err
checkStmt (L.CondElse pos expr stmt1 stmt2 : rest) retst depth = do
    env <- ask
    st <- get
    let expt = checkExprM st env expr
    case expt of
        Right exprType -> do
            case exprType of
                "boolean" -> do
                    case expr of
                        L.ELitTrue _ -> do
                            ret1 <- checkStmt [stmt1] RetTBD (depth + 1)
                            _ <- checkStmt [stmt2] retst (depth + 1)
                            checkStmt rest (update retst ret1) depth
                        L.ELitFalse _ -> do
                            _ <- checkStmt [stmt1] retst (depth + 1)
                            ret2 <- checkStmt [stmt2] RetTBD (depth + 1)
                            checkStmt rest (update retst ret2) depth
                        _ -> do
                            ret1 <- checkStmt [stmt1] RetTBD (depth + 1)
                            ret2 <- checkStmt [stmt2] RetTBD (depth + 1)
                            if ret1 == ret2 then
                                checkStmt rest (update retst ret1) depth
                            else
                                checkStmt rest retst depth
                t -> formatError pos $ "If-else-condition has to be boolean type, received " ++ show t   
        Left err -> formatError pos err
checkStmt (L.While pos expr stmt : rest) retst depth = do
    env <- ask
    st <- get
    let expt = checkExprM st env expr
    case expt of
        Right exprType -> do
            case exprType of
                "boolean" -> do
                    case expr of
                        L.ELitTrue _ -> do
                            ret1 <- checkStmt [stmt] RetTBD (depth + 1)
                            if ret1 == RetOk then
                                checkStmt rest (update retst RetOk) depth
                            else
                                checkStmt rest (update retst RetBad) depth
                        L.ELitFalse _ -> do
                            _ <- checkStmt [stmt] retst (depth + 1)
                            checkStmt rest retst depth
                        _ -> do
                            _ <- checkStmt [stmt] retst (depth + 1)
                            checkStmt rest retst depth
                t -> formatError pos $ "While-condition has to be boolean type, received " ++ show t
        Left err -> formatError pos err
checkStmt (L.SExp pos expr : rest) retst depth = do
    env <- ask
    st <- get
    let expt = checkExprM st env expr
    case expt of
        Right exprType -> checkStmt rest retst depth
        Left err -> formatError pos err

checkExprM :: TCState -> TypeEnv -> L.Expr -> Either String Type
checkExprM st env expr = case runTypeCheckerMonad st env (checkExpr expr) of
    Left err -> Left err
    Right (t, _) -> Right t
    
checkExprL :: [L.Expr] -> TypeEnv -> TypeCheckerMonad [Type]
checkExprL [] env = return []
checkExprL (expr : rest) env = do
    exprH <- checkExpr expr
    exprL <- checkExprL rest env
    return $ exprH : exprL

checkExpr :: L.Expr -> TypeCheckerMonad Type
checkExpr (L.EVar pos (L.Ident ident)) = do
    env <- ask
    case Map.lookup ident env of
        Nothing -> formatError pos $ "Uninitialized variable '" ++ ident ++ "'"
        Just (t, _) -> return t
checkExpr (L.ELitInt pos n) = do
    if n > 2147483648 - 1 then
        formatError pos $ "Number has to be in range of int"
    else
        return "int"
checkExpr (L.ELitTrue _) = return "boolean"
checkExpr (L.ELitFalse _) = return "boolean"
checkExpr (L.EApp pos (L.Ident ident) args) = do
    if ident == "main" then do
        formatError pos $ "Cannot call main function"
    else do
        env <- ask
        case Map.lookup ident env of
            Nothing -> formatError pos $ "Uninitialized function '" ++ ident ++ "' called"
            Just (t, _) -> do
                let retType = getRetType t
                let fArgs = getArgsTypes t
                gArgs <- checkExprL args env
                subclasses <- areSubClasses gArgs fArgs
                if subclasses then
                    return retType
                else
                    formatError pos $ "Function '" ++ ident ++ "' takes " ++ show fArgs ++ " as parameters, but received " ++ show gArgs
checkExpr (L.EMethod pos expr (L.Ident ident) args) = do
    env <- ask
    st <- get
    let expt = checkExprM st env expr
    case expt of
        Right exprType -> do
            case Map.lookup exprType (typeStore st) of
                Nothing -> formatError pos $ "Invalid type of object expression"
                Just _ -> do
                t <- findMethodType exprType ident pos
                let retType = getRetType t
                let fArgs = getArgsTypes t
                gArgs <- checkExprL args env
                subclasses <- areSubClasses gArgs fArgs
                if subclasses then
                    return retType
                else
                    formatError pos $ "Method '" ++ ident ++ "' takes " ++ show fArgs ++ " as parameters, but received " ++ show gArgs
        Left err -> formatError pos err
checkExpr (L.EAttr pos expr (L.Ident ident)) = do
    env <- ask
    st <- get
    let expt = checkExprM st env expr
    case expt of
        Right exprType -> do
            case Map.lookup exprType (typeStore st) of
                Nothing -> formatError pos $ "Invalid type of object expression"
                Just _ -> do
                    t <- findAttrType exprType ident pos
                    return t
        Left err -> formatError pos err
checkExpr (L.EString _ _) = return "string"
checkExpr (L.ENull _ t) = return $ lStrType t
checkExpr (L.ENewClass _ t) = return $ lStrType t
checkExpr (L.Neg pos expr) = do
    exprType <- checkExpr expr
    checkAndReturn exprType "int" "int" pos ("Cannot negate " ++ show exprType ++ ", expected int")
checkExpr (L.Not pos expr) = do
    exprType <- checkExpr expr
    checkAndReturn exprType "boolean" "boolean" pos ("Cannot invert " ++ show exprType ++ ", expected boolean")
checkExpr (L.EMul pos expr1 _ expr2) = do
    exprType1 <- checkExpr expr1
    exprType2 <- checkExpr expr2
    checkAndReturn2 exprType1 exprType2 "int" "int" pos ("Cannot multiply " ++ show exprType1 ++ " and " ++ show exprType2 ++ ", 2 ints required")
checkExpr (L.EAdd pos expr1 addOp expr2) = do
    exprType1 <- checkExpr expr1
    exprType2 <- checkExpr expr2

    case (addOp, exprType1) of
        (L.Plus _, "string") -> checkAndReturn2 exprType1 exprType2 "string" "string" pos ("Cannot concat " ++ show exprType1 ++ " with " ++ show exprType2 ++ ", 2 strings required")
        _ -> checkAndReturn2 exprType1 exprType2 "int" "int" pos ("Cannot add " ++ show exprType1 ++ " to " ++ show exprType2 ++ ", 2 ints required")
checkExpr (L.ERel pos expr1 relOp expr2) = do
    exprType1 <- checkExpr expr1
    exprType2 <- checkExpr expr2

    let option1 = checkAndReturn2 exprType1 exprType2 exprType1 "boolean" pos ("Cannot compare " ++ show exprType1 ++ " and " ++ show exprType2 ++ " with equality operator, required 2 ints, 2 strings or 2 classes")
    let option2 = checkAndReturn2 exprType1 exprType2 "int" "boolean" pos ("Cannot compare " ++ show exprType1 ++ " and " ++ show exprType2 ++ " with inequality operator, 2 ints required")

    valid <- isValidTypeM exprType1

    if valid == True then
        case relOp of
            L.EQU _ -> option1
            L.NE _ -> option1
            _ -> option2
    else
        option2
checkExpr (L.EAnd pos expr1 expr2) = do
    exprType1 <- checkExpr expr1
    exprType2 <- checkExpr expr2
    checkAndReturn2 exprType1 exprType2 "boolean" "boolean" pos ("Cannot use binary operator AND on " ++ show exprType1 ++ " and " ++ show exprType2 ++ ", 2 booleans required")
checkExpr (L.EOr pos expr1 expr2) = do
    exprType1 <- checkExpr expr1
    exprType2 <- checkExpr expr2
    checkAndReturn2 exprType1 exprType2 "boolean" "boolean" pos ("Cannot use binary operator OR on " ++ show exprType1 ++ " and " ++ show exprType2 ++ ", 2 booleans required")

findAttrType :: Type -> String -> Pos -> TypeCheckerMonad Type
findAttrType typ str pos = do
    cm <- gets classMap
    case Map.lookup typ cm of
        Nothing -> formatError pos $ "Type '" ++ typ ++ "' is not a class type"
        Just (attrs, _) -> do
            case findInList True str attrs of
                Left err -> formatError pos err
                Right t -> return t

findMethodType :: Type -> String -> Pos -> TypeCheckerMonad Type
findMethodType typ str pos = do
    cm <- gets classMap
    case Map.lookup typ cm of
        Nothing -> formatError pos $ "Type '" ++ typ ++ "' is not a class type"
        Just (_, methods) -> do
            case findInList False str methods of
                Left err -> formatError pos err
                Right t -> return t

findInList :: Bool -> String -> [(Type, String)] -> Either String Type
findInList b str [] = Left $ "Could not find " ++ if b == True then "attribute" else "method" ++ " with name " ++ str
findInList b str ((typ, s) : rest) = 
    case str == s of
        True -> Right typ
        False -> findInList b str rest

checkAndReturn :: Type -> Type -> Type -> Pos -> String -> TypeCheckerMonad Type
checkAndReturn input expected ret pos err = 
    if input == expected then
        return ret
    else
        formatError pos err
checkAndReturn2 :: Type -> Type -> Type -> Type -> Pos -> String -> TypeCheckerMonad Type
checkAndReturn2 input1 input2 expected ret pos err = do
    subclass11 <- isSubClass input1 input1
    subclass21 <- isSubClass input2 input1
    subclass12 <- isSubClass input1 input2
    subclass22 <- isSubClass input2 input2
    if (subclass11 && subclass21) || (subclass12 && subclass22) then
        return ret
    else
        formatError pos err

getArgType :: L.Arg -> L.Type
getArgType (L.Arg _ t _) = t

modifiedClassEnv :: String -> TypeEnv -> [(Type, String)] -> Int -> Either String TypeEnv
modifiedClassEnv ident env [] _ = Right env
modifiedClassEnv ident env ((typ, str) : rest) n = modifiedClassEnv ident (Map.insert (ident ++ "." ++ str) (typ, n) env) rest n

addClassParam :: String -> Type -> TypeEnv -> ClassMap -> Int -> Pos -> Either String TypeEnv
addClassParam ident t env cm n pos = 
    case Map.lookup t cm of
        Nothing -> Left $ errMessage pos $ "Class name '" ++ t ++ "' is not defined"
        Just (attrs, methods) -> modifiedClassEnv ident env (attrs ++ methods) n

modifiedEnv :: TypeEnv -> [L.Arg] -> ClassMap -> Int -> Either String TypeEnv
modifiedEnv env [] _ _ = Right env
modifiedEnv env (L.Arg pos typ (L.Ident ident) : rest) cm n = do
    case modifiedEnv env rest cm n of
        Left err -> Left err
        Right modEnv -> do
            let t = lStrType typ
            case Map.lookup ident modEnv of
                Nothing -> do
                    case Map.lookup t cm of
                        Nothing -> Right $ Map.insert ident (t, n) modEnv
                        Just _ -> addClassParam ident t (Map.insert ident (t, n) modEnv) cm n pos
                Just (_, 0) -> Left $ errMessage pos $ "Name '" ++ ident ++ "' is already taken by a function"
                Just (_, n) -> Left $ errMessage pos $ "Parameter '" ++ ident ++ "' is already defined as argument of this function"

addAttrsToEnv :: TypeEnv -> [(Type, String)] -> TypeEnv
addAttrsToEnv env [] = env
addAttrsToEnv env ((typ, str) : rest) = addAttrsToEnv (Map.insert str (typ, 1) env) rest

checkBlocks :: [L.TopDef] -> TypeEnv -> TypeStore -> ClassMap -> Either String ()
checkBlocks [] _ _ _ = return ()
checkBlocks (L.FnDef pos retType (L.Ident ident) args block : rest) env st cm =
    case modifiedEnv env (reverse args) cm 1 of
        Left err -> Left err
        Right newEnv ->
            case runTypeCheckerMonad (initTCState (lStrType retType) st pos cm) newEnv (checkStmt [(L.BStmt pos block)] RetTBD 0) of
                Left err -> Left err
                Right (retState, _) ->
                    if retState == RetOk || (retState == RetTBD && lStrType retType == "void") then
                        checkBlocks rest env st cm
                    else
                        Left $ errMessage pos $ "Function '" ++ ident ++ "' is not always returning with type " ++ show (lStrType retType)
checkBlocks (L.ClassDef _ (L.Ident ident) (L.CBlock _ stmts) : rest) env st cm =
    case Map.lookup ident cm of
        Just (attrs, methods) ->
            let newEnv = addAttrsToEnv env attrs in
                case checkMethods ident stmts env st cm of
                    Left err -> Left err
                    Right _ -> checkBlocks rest env st cm
checkBlocks (L.CDefExt _ (L.Ident ident) _ (L.CBlock _ stmts) : rest) env st cm =
    case Map.lookup ident cm of
        Just (attrs, methods) ->
            let newEnv = addAttrsToEnv env attrs in
                case checkMethods ident stmts env st cm of
                    Left err -> Left err
                    Right _ -> checkBlocks rest env st cm

modifiedThis :: Type -> TypeEnv -> [L.Arg] -> ClassMap -> Either String TypeEnv
modifiedThis ctype env args cm = 
    case Map.lookup ctype cm of
        Just (attrs, _) ->
            let modEnv = addAttrsToEnv env attrs in
                case modifiedEnv modEnv (reverse args) cm 2 of
                    Left err -> Left err
                    Right newEnv -> Right newEnv

checkMethods :: Type -> [L.CStmt] -> TypeEnv -> TypeStore -> ClassMap -> Either String ()
checkMethods _ [] _ _ _ = return ()
checkMethods ctype (L.CMethod pos retType (L.Ident ident) args block : rest) env st cm =
    case modifiedThis ctype env (L.Arg Nothing (L.Class Nothing (L.Ident ctype)) (L.Ident "self") : args) cm of
        Left err -> Left err
        Right newEnv ->
            case runTypeCheckerMonad (initTCState (lStrType retType) st pos cm) newEnv (checkStmt [(L.BStmt pos block)] RetTBD 1) of
                Left err -> Left err
                Right (retState, _) ->
                    if retState == RetOk || (retState == RetTBD && lStrType retType == "void") then
                        checkMethods ctype rest env st cm
                    else
                        Left $ errMessage pos $ "Method '" ++ ident ++ "' is not always returning with type " ++ show (lStrType retType)
checkMethods ctype (_ : rest) env st cm = checkMethods ctype rest env st cm

predefinedTypes :: [(Pos, Type, Maybe Type)]
predefinedTypes = [(Nothing, "int", Nothing), (Nothing, "boolean", Nothing), (Nothing, "string", Nothing)]

getTypes :: [L.TopDef] -> [(Pos, Type, Maybe Type)]
getTypes [] = predefinedTypes
getTypes (L.ClassDef pos (L.Ident ident) _ : rest) = (pos, ident, Nothing) : getTypes rest
getTypes (L.CDefExt pos (L.Ident ident1) (L.Ident ident2) _ : rest) = (pos, ident1, Just ident2) : getTypes rest
getTypes (_ : rest) = getTypes rest

checkClasses :: [(Pos, Type, Maybe Type)] -> Int -> TypeStore -> Either String TypeStore
checkClasses [] _ st = Right st
checkClasses ((pos, t, Nothing) : rest) _ st = 
    case Map.lookup t st of
        Just _ -> Left $ errMessage pos $ "There is a type or class with the same name as this one '" ++ t ++ "'"
        Nothing -> checkClasses rest 0 (Map.insert t Nothing st)
checkClasses list@(cur@(pos, t, Just f) : rest) n st = 
    if n > length list then
        Left $ errMessage pos $ "Class '" ++ t ++ "' tries to extend undeclared class '" ++ f ++ "'"
    else
        case Map.lookup t st of
            Just _ -> Left $ errMessage pos $ "There is a type or class with the same name as this one '" ++ t ++ "'"
            Nothing ->
                case Map.lookup f st of
                    Nothing -> checkClasses (rest ++ [cur]) (n + 1) st
                    Just _ -> checkClasses rest 0 (Map.insert t (Just f) st)

checkClassStmt :: [L.CStmt] -> [(Type, String)] -> [(Type, String)] -> TypeCheckerMonad ([(Type, String)], [(Type, String)])
checkClassStmt [] attrs methods = return (attrs, methods)
checkClassStmt (L.CEmpty _ : rest) attrs methods = checkClassStmt rest attrs methods
checkClassStmt (L.CDecl _ _ [] : rest) attrs methods = checkClassStmt rest attrs methods
checkClassStmt (L.CDecl pos t ((L.CItem pos2 (L.Ident ident)) : items) : rest) attrs methods = do
    let declType = lStrType t
    valid <- isValidTypeM declType

    case valid of
        False -> formatError pos $ "Declaration of attributes with non-valid type '" ++ declType ++ "'"
        True -> do
            env <- ask
            case Map.lookup ident env of
                Nothing -> local (Map.insert ident (declType, 1)) (checkClassStmt (L.CDecl pos t items : rest) (attrs ++ [(declType, ident)]) methods)
                _ -> formatError pos $ "Redeclaration of attribute with name '" ++ ident ++ "' in this class"
checkClassStmt (L.CMethod pos typ (L.Ident ident) args block : rest) attrs methods = do
    env <- ask
    case Map.lookup ident env of
        Just (_, 1) -> formatError pos $ "Declaration of method with a name used previously for an attribute of another method"
        Nothing -> do
            let t = ("#fun <" ++ lStrType typ ++ "> (" ++ (intercalate ", " $ map fromArg args) ++ ")")
            let retType = lStrType typ
            let argsTypes = getArgsTypes t
            st <- gets typeStore
            case isValidType retType st True of
                False -> formatError pos $ "Return type of method '" ++ ident ++ "' is not a valid type (built-in type or class name), found " ++ retType ++ " instead"
                True ->
                    case and (mapTypes argsTypes st) of
                        False -> formatError pos $ "One of arguments types of method '" ++ ident ++ "' is not a valid type (built-in type or class name)"
                        True -> local (Map.insert ident (t, 1)) (checkClassStmt rest attrs (methods ++ [(t, ident)]))

getClassMap :: TypeStore -> [L.TopDef] -> ClassMap -> Either String ClassMap
getClassMap _ [] cm = Right cm
getClassMap st (L.ClassDef pos (L.Ident ident) (L.CBlock _ stmts) : rest) cm = 
    case runTypeCheckerMonad (initTCState "XD" st pos Map.empty) Map.empty (checkClassStmt stmts [] []) of
        Left err -> Left err
        Right (lists, _) -> getClassMap st rest (Map.insert ident lists cm)
getClassMap st (cur@(L.CDefExt pos (L.Ident ident1) (L.Ident ident2) (L.CBlock _ stmts)) : rest) cm = 
    case Map.lookup ident2 cm of
        Nothing -> getClassMap st (rest ++ [cur]) cm
        Just (fattrs, fmethods) ->
            case runTypeCheckerMonad (initTCState "XD" st pos Map.empty) Map.empty (checkClassStmt stmts [] []) of
                Left err -> Left err
                Right ((tattrs, tmethods), _) -> 
                    case findRepeatedName (map snd fattrs) (map snd tattrs) of
                        Just name -> Left $ errMessage pos $ "Attribute '" ++ name ++ "' is already declared in some superclass"
                        Nothing -> 
                            let methodslist = removeEarlierMethods fmethods tmethods in
                                case methodslist of
                                    Left err -> Left $ errMessage pos $ "Method '" ++ err ++ "' of class '" ++ ident1 ++ "' has different type to method with the same name of some superclass"
                                    Right res -> getClassMap st rest (Map.insert ident1 (fattrs ++ tattrs, res) cm)
getClassMap st (_ : rest) cm = getClassMap st rest cm

removeEarlierMethods :: [(Type, String)] -> [(Type, String)] -> Either String [(Type, String)]
removeEarlierMethods [] [] = Right []
removeEarlierMethods f [] = Right f
removeEarlierMethods [] t = Right t
removeEarlierMethods (fm@(typ, fstr) : restf) tmethods =
    let check = searchMethods fm tmethods in
        case check of
            Left err -> Left err
            Right False -> 
                case removeEarlierMethods restf tmethods of
                    Left err -> Left err
                    Right res -> Right $ fm : res
            Right True -> removeEarlierMethods restf tmethods

searchMethods :: (Type, String) -> [(Type, String)] -> Either String Bool
searchMethods _ [] = Right False
searchMethods (typ, str) ((tt, ts) : rest) = 
    if str == ts then
        if typ == tt then
            Right True
        else
            Left ts
    else
        searchMethods (typ, str) rest

findRepeatedName :: [String] -> [String] -> Maybe String
findRepeatedName [] _ = Nothing
findRepeatedName _ [] = Nothing
findRepeatedName (x : xs) ys = 
    case elem x ys of
        False -> findRepeatedName xs ys
        True -> Just x


predefinedFuncs :: [(Pos, String, Type)]
predefinedFuncs = [(Nothing, "printInt", "#fun <void> (int)"),
                   (Nothing, "printString", "#fun <void> (string)"),
                   (Nothing, "error", "#fun <void> ()"),
                   (Nothing, "readInt", "#fun <int> ()"),
                   (Nothing, "readString", "#fun <string> ()")]

getFuncs :: TypeStore -> [L.TopDef] -> [(Pos, String, Type)]
getFuncs _ [] = predefinedFuncs
getFuncs st (L.FnDef pos retType (L.Ident ident) args _ : rest) = (pos, ident, "#fun <" ++ lStrType retType ++ "> (" ++ (intercalate ", " $ map fromArg args) ++ ")") : getFuncs st rest
getFuncs st (_ : rest) = getFuncs st rest

isValidType :: Type -> TypeStore -> Bool -> Bool
isValidType t st void = case Map.lookup t st of
    Nothing -> if void == True && t == "void" then True else False
    Just _ -> True

mapTypes :: [Type] -> TypeStore -> [Bool]
mapTypes [] _ = []
mapTypes (t : rest) st = (isValidType t st False : mapTypes rest st)

checkFuncs :: TypeStore -> [(Pos, String, Type)] -> Either String TypeEnv
checkFuncs _ [] = Right Map.empty
checkFuncs st ((pos, name, t) : rest) = 
    case checkFuncs st rest of
        Left err -> Left err
        Right env ->
            case Map.lookup name env of
                Just (t, 0) -> Left $ errMessage pos $ "Redefinition of a function with name '" ++ name ++ "'"
                Nothing ->
                    let retType = getRetType t in
                        let argsTypes = getArgsTypes t in
                            if name == "main" && (isNotInt retType || length argsTypes > 0) then
                                Left $ errMessage pos $ "Main function has to return int and take no arguments"
                            else 
                                case isValidType retType st True of
                                    False -> Left $ errMessage pos $ "Return type of function '" ++ name ++ "' is not a valid type (built-in type or class name), found " ++ retType ++ " instead"
                                    True ->
                                        case and (mapTypes argsTypes st) of
                                            False -> Left $ errMessage pos $ "One of arguments types of function '" ++ name ++ "' is not a valid type (built-in type or class name)"
                                            True -> Right $ Map.insert name (t, 0) env

isNotInt :: String -> Bool
isNotInt "int" = False
isNotInt _ = True

runProgram :: L.Program -> IO (Either String ())
runProgram (L.Program _ fns) = do
    let classes = getTypes fns
    case checkClasses classes 0 Map.empty of
        Left err -> return $ Left err
        Right st -> do
            --hPutStrLn stderr $ "TYPESTORE = " ++ show st
            case getClassMap st fns Map.empty of
                Left err -> return $ Left err
                Right cm -> do
                    --hPutStrLn stderr $ "CLASSMAP = " ++ show cm
                    let funcs = getFuncs st fns
                    case checkFuncs st funcs of
                        Left err -> return $ Left err
                        Right env -> do
                            --hPutStrLn stderr $ "ENV = " ++ show env
                            return $ checkBlocks fns env st cm