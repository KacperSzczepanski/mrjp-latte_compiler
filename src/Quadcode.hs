module Quadcode where

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import System.IO
import Data.Maybe
import qualified Data.Map as Map
import Data.Bits
import Data.Char
import qualified Data.List as List
import qualified AbsLatte as L

debug :: Show a => String -> a -> QuadMonad ()
debug msg a = do
    liftIO $ hPutStrLn stderr $ "DEBUG: " ++ msg ++ show a
    return ()

type Offset = Int
data ClassInfo = ClassInfo {totalSize :: Int, offset :: Map.Map String Offset, vtableOffset :: Map.Map String Offset, listOfAttrs :: [(Type, String)], listOfMethods :: [(Type, String, L.CStmt)]} deriving (Show, Eq)
type ClassInfoMap = Map.Map Type ClassInfo

listToExpr :: [String] -> L.Expr
listToExpr [str] = L.EVar Nothing (L.Ident str)
listToExpr list = do
    let rest = init list
    L.EAttr Nothing (listToExpr rest) (L.Ident (last list))

exprToIdent :: L.Expr -> String
exprToIdent (L.EVar _ (L.Ident ident)) = ident
exprToIdent (L.EAttr _ exp (L.Ident ident)) = exprToIdent exp ++ "." ++ ident

type Type = String
lStrType :: L.Type -> String
lStrType (L.Int _) = "int"
lStrType (L.Str _) = "string"
lStrType (L.Bool _) = "boolean"
lStrType (L.Class _ (L.Ident c)) = c
lStrType (L.Void _ ) = "void"
lStrType (L.Fun _ retType args) = "fun <" ++ lStrType retType ++ "> (" ++ (List.intercalate ", " $ map lStrType args) ++ ")"

type Pos = L.BNFC'Position
posShow :: Pos -> String
posShow Nothing = ""
posShow (Just (line, col)) = show line ++ ":" ++ show col
errMessage :: Pos -> String -> String
errMessage pos err = posShow pos ++ ": " ++ err
formatErrorQ :: Pos -> String -> QuadMonad a
formatErrorQ pos err = throwError (errMessage pos err)

tab :: String
tab = "    "

fromStrType :: Type -> VarType
fromStrType "int" = IntVar
fromStrType "string" = StrVar
fromStrType "boolean" = BoolVar
fromStrType "void" = VoidVar
fromStrType c = ClassVar c

data VarType = IntVar | StrVar | BoolVar | VoidVar | ClassVar Type deriving (Eq)
instance Show VarType where
    show IntVar = "Int"
    show StrVar = "Str"
    show BoolVar = "Bool"
    show VoidVar = "Void"
    show (ClassVar t) = "Class<" ++ t ++ ">"
fromLType :: L.Type -> VarType
fromLType (L.Int _) = IntVar
fromLType (L.Bool _) = BoolVar
fromLType (L.Str _) = StrVar
fromLType (L.Void _) = VoidVar
fromLType t@(L.Class _ _) = ClassVar (lStrType t)
data Var = VLocal String VarType
         | VParam String VarType
         | VNothing
         deriving (Eq)
fromVarType :: VarType -> Type
fromVarType IntVar = "int"
fromVarType StrVar = "string"
fromVarType BoolVar = "boolean"
fromVarType VoidVar = "void"
fromVarType (ClassVar t) = t
instance Show Var where
    show (VLocal s t) = "(l!_" ++ s ++ " <" ++ show t ++ ">)"
    show (VParam s t) = "(p!_" ++ s ++ " <" ++ show t ++ ">)"
    show (VNothing) = "(_)"
fromVar :: Var -> String
fromVar (VLocal s _) = s
fromVar (VParam s _) = s
data Class = Content [(String, Val)] | Null deriving (Eq)
data Val = IntVal Int
         | StrVal String
         | BoolVal Bool
         | ClassVal Type Class
         | ParVal String VarType
         | LocVal String VarType
         deriving (Eq)
fromVal :: Val -> Type
fromVal (IntVal _) = "int"
fromVal (StrVal _) = "string"
fromVal (BoolVal _) = "boolean"
fromVal (ClassVal t _) = t
fromVal (ParVal _ vartype) = fromVarType vartype
fromVal (LocVal _ vartype) = fromVarType vartype
instance Show Val where
    show (IntVal i)  = show i
    show (StrVal s)  = show s
    show (BoolVal b) = show b
    show (ParVal s t)  = "(p!_" ++ s ++ " <" ++ show t ++ ">)"
    show (LocVal s t)  = "(l!_" ++ s ++ " <" ++ show t ++ ">)"
    show (ClassVal t Null) = "class<" ++ t ++ ">NULL"
    show (ClassVal t (Content list)) = "class<" ++ t ++ ">(" ++ show list ++ ")"
data QuadInstr = QLabel String
               | QAss Var Val
               | QAdd Var Val Val
               | QAddStr Var Val Val
               | QSub Var Val Val
               | QMul Var Val Val
               | QDiv Var Val Val
               | QMod Var Val Val
               | QAttr Var Val String
               | QNeg Var Val
               | QAnd Var Val Val
               | QOr Var Val Val
               | QNot Var Val
               | QCmpEq Var Val Val
               | QCmpLth Var Val Val
               | QIf Val String
               | QParam Val
               | QCall Var String Int
               | QCallM Var Val String Int
               | QVRet
               | QRet Val
               | QFunc Bool String [L.Arg] QuadCode
               | QGoto String
instance Show QuadInstr where
    showList is s                = unlines (map show is) ++ s
    show (QLabel l)              = l ++ ":"
    show (QAss var val)          = tab ++ show var ++ " := " ++ show val
    show (QAdd var val1 val2)    = tab ++ show var ++ " := " ++ show val1 ++ " + " ++ show val2
    show (QAddStr var val1 val2) = tab ++ show var ++ " := " ++ show val1 ++ " + " ++ show val2
    show (QSub var val1 val2)    = tab ++ show var ++ " := " ++ show val1 ++ " - " ++ show val2
    show (QMul var val1 val2)    = tab ++ show var ++ " := " ++ show val1 ++ " * " ++ show val2
    show (QDiv var val1 val2)    = tab ++ show var ++ " := " ++ show val1 ++ " / " ++ show val2
    show (QMod var val1 val2)    = tab ++ show var ++ " := " ++ show val1 ++ " % " ++ show val2
    show (QAttr var val attr)    = tab ++ show var ++ " := " ++ show val ++ "." ++ attr
    show (QNeg var val)          = tab ++ show var ++ " := - " ++ show val
    show (QAnd var val1 val2)    = tab ++ show var ++ " := " ++ show val1 ++ " && " ++ show val2
    show (QOr var val1 val2)     = tab ++ show var ++ " := " ++ show val1 ++ " || " ++ show val2
    show (QNot var val)          = tab ++ show var ++ " := not " ++ show val
    show (QCmpEq var val1 val2)  = tab ++ show var ++ " := " ++ show val1 ++ " == " ++ show val2
    show (QCmpLth var val1 val2) = tab ++ show var ++ " := " ++ show val1 ++ " < " ++ show val2
    show (QIf var l)             = tab ++ "if " ++ show var ++ " goto " ++ l
    show (QGoto l)               = tab ++ "goto " ++ l
    show (QParam val)            = tab ++ "param " ++ show val
    show (QCall var f n)         = tab ++ show var ++ " := call " ++ f ++ ", " ++ show n
    show (QCallM var val met n)  = tab ++ show var ++ " := callM " ++ show val ++ "." ++ met ++ ", " ++ show n
    show (QVRet)                 = tab ++ "return"
    show (QRet val)              = tab ++ "return " ++ show val
    show (QFunc g f args code)   = "//function " ++ f ++ " <" ++ List.intercalate "," (map showA args) ++ ">:\n" ++ show code
showA :: L.Arg -> String
showA (L.Arg _ t (L.Ident ident)) = showT t ++ " " ++ ident
showT :: L.Type -> String
showT (L.Int _ ) = "int"
showT (L.Str _ ) = "string"
showT (L.Bool _) = "bool"
showT (L.Void _) = "void"
showT (L.Class _ (L.Ident t)) = "class <" ++ t ++ ">"
type QuadCode = [QuadInstr]
data QState = QState {usedNames :: Map.Map Loc Int, usedSpecialNames :: Map.Map String Int, labelCnt :: Int, store :: QStore, lastLoc :: Loc, funTypeMap :: Map.Map String VarType, classInfoMap :: ClassInfoMap, varTypeMap :: Map.Map String Type, curFunName :: String}

initQState :: [L.TopDef] -> ClassInfoMap -> QState
initQState [] cim = QState {usedNames = Map.empty, usedSpecialNames = Map.empty, labelCnt = 1, store = Map.empty, lastLoc = 0, funTypeMap = predefinedFuncs, classInfoMap = cim, varTypeMap = Map.empty, curFunName = ""} where
    predefinedFuncs :: Map.Map String VarType
    predefinedFuncs = load [("printInt", VoidVar), ("printString", VoidVar), ("error", VoidVar), ("readInt", IntVar), ("readString", StrVar), ("concatStrings", StrVar), ("compareStrings", StrVar)]
    load :: [(String, VarType)] -> Map.Map String VarType
    load [] = Map.empty
    load ((name, typ) : rest) = Map.insert name typ (load rest)
initQState (L.FnDef _ t (L.Ident ident) _ _ : rest) cim = QState {usedNames = un, usedSpecialNames = usn, labelCnt = lcnt, store = st, lastLoc = ll, funTypeMap = map, classInfoMap = cim, varTypeMap = Map.empty, curFunName = ""} where
    res = initQState rest cim
    un = usedNames res
    usn = usedSpecialNames res
    lcnt = labelCnt res
    st = store res
    ll = lastLoc res
    oldMap = funTypeMap res
    map = Map.insert ident (fromLType t) oldMap
initQState (_ : rest) cim = initQState rest cim

clearStore :: QuadMonad ()
clearStore = modify (\st -> st {store = Map.empty, lastLoc = 0})

setStore :: Loc -> QStore -> QuadMonad ()
setStore loc newStore = modify (\st -> st {store = newStore, lastLoc = loc})

qinsert :: Loc -> Var -> QuadMonad ()
qinsert loc var = modify (\st -> st {store = Map.insert loc var (store st)})

alloc :: QuadMonad Loc
alloc = state (\st -> (lastLoc st + 1, st {lastLoc = lastLoc st + 1}))

allocMore :: Int -> QuadMonad Loc
allocMore n = state (\st -> (lastLoc st + 1, st {lastLoc = lastLoc st + n}))

qquery :: Loc -> QuadMonad (Maybe Var)
qquery loc = do
    st <- gets store
    return $ Map.lookup loc st

qask :: String -> QuadMonad (Maybe Var)
qask ident = do
    env <- ask
    case Map.lookup ident env of
        Nothing -> return Nothing
        Just loc -> do
            res <- qquery loc
            return res

newId :: String -> QuadMonad Int
newId name = do
    st <- gets usedNames
    env <- ask
    case Map.lookup name env of
        Nothing -> return 0
        Just loc -> case Map.lookup loc st of
            Nothing -> return 0
            Just n -> return $ n + 1

curId :: String -> QuadMonad Int
curId name = do
    st <- gets usedNames
    env <- ask
    case Map.lookup name env of
        Nothing -> return 0
        Just loc -> case Map.lookup loc st of
            Nothing -> return 0
            Just n -> return $ n

newSpecialId :: String -> QuadMonad Int
newSpecialId name = do
    st <- gets usedSpecialNames
    case Map.lookup name st of
        Nothing -> return 0
        Just n -> return $ n + 1

getName :: String -> QuadMonad String
getName name = do
    number <- newSpecialId name
    state (\st -> (name ++ "#_" ++ show number, st {usedSpecialNames = Map.insert name number (usedSpecialNames st)}))

newName :: Maybe Var -> String -> Bool -> Loc -> Bool -> QuadMonad String
newName Nothing name force loc isLocal = do
    let ssa = False
    case ssa of
        True -> getName name
        False -> do
            case name of
                "tmp#" -> getName name
                "if#" -> getName name
                "ifelse#" -> getName name
                "while#" -> getName name
                _ -> case force of
                    True -> do
                        number <- newId name
                        env <- ask
                        state (\st -> (name ++ "#_" ++ show number, st {usedNames = Map.insert loc number (usedNames st)}))
                    False -> do --assignment
                        case isLocal of
                            False -> do
                                funName <- gets curFunName
                                return $ name ++ "#" ++ funName
                            True -> do
                                number <- curId name
                                return $ name ++ "#_" ++ show number
newName (Just var) _ _ _ _ = return $ fromVar var

ifLabels :: QuadMonad (String, String)
ifLabels = state (\st -> (("$ITrue" ++ show (labelCnt st),
                           "$IContinue" ++ show (labelCnt st)),
                           st {labelCnt = labelCnt st + 1}))
ifElseLabels :: QuadMonad (String, String, String)
ifElseLabels = state (\st -> (("$ETrue" ++ show (labelCnt st),
                               "$EFalse" ++ show (labelCnt st),
                               "$EContinue" ++ show (labelCnt st)),
                               st {labelCnt = labelCnt st + 1}))
whileLabels :: QuadMonad (String, String, String)
whileLabels = state (\st -> (("$WBody" ++ show (labelCnt st),
                              "$WCond" ++ show (labelCnt st),
                              "$WContinue" ++ show (labelCnt st)),
                              st {labelCnt = labelCnt st + 1}))

type Loc = Int
type QEnv = Map.Map String Loc
type QStore = Map.Map Loc Var

type QuadMonad a = StateT QState (ReaderT QEnv (ExceptT String (WriterT QuadCode IO))) a
runQuadMonad :: QEnv -> QState -> QuadMonad a -> IO (Either String (a, QState), QuadCode)
runQuadMonad env st ev = runWriterT (runExceptT (runReaderT (runStateT ev st) env))

lhsIsRhs :: String -> Val -> Bool
lhsIsRhs name (LocVal s _) = name == s
lhsIsRhs name (ParVal s _) = name == s
lhsIsRhs _ _ = False

typeOfVal :: Val -> VarType
typeOfVal (IntVal _) = IntVar
typeOfVal (StrVal _) = StrVar
typeOfVal (BoolVal _) = BoolVar
typeOfVal (ParVal _ t) = t
typeOfVal (LocVal _ t) = t
typeOfVal (ClassVal t i) = ClassVar t


isClassType :: Type -> QuadMonad Bool
isClassType t = do
    cimap <- gets classInfoMap
    case Map.lookup t cimap of
        Nothing -> return False
        Just _ -> return True

extendLocs :: Loc -> Int -> [Loc]
extendLocs loc 0 = []
extendLocs loc n = loc : extendLocs (loc + 1) (n - 1)

modifyEnv :: QEnv -> [Loc] -> String -> [(Type, String)] -> QEnv
modifyEnv env [] _ [] = env
modifyEnv env (loc : restl) ident ((_, str) : resta) = Map.insert (ident ++ "." ++ str) loc (modifyEnv env restl ident resta)

insertManyDecl :: [Loc] -> String -> [(Type, String)] -> QuadMonad ()
insertManyDecl [] _ [] = return ()
insertManyDecl (loc : restl) ident ((typ, str) : resta) = do
    name <- newName Nothing (ident ++ "." ++ str) True loc False
    qinsert loc (VLocal name (fromStrType typ))
    insertManyDecl restl ident resta

insertManyP :: String -> [(Type, String)] -> QuadMonad (QuadCode) -> QuadMonad (QuadCode)
insertManyP _ [] after = after
insertManyP ident ((typ, str) : rest) after = do
    name <- newName Nothing (ident ++ "." ++ str) False 0 False
    env <- ask
    case Map.lookup (ident ++ "." ++ str) env of
        Just loc -> do
            qinsert loc (VParam name (fromStrType typ))
            insertManyL ident rest after
        Nothing -> do
            loc <- alloc 
            qinsert loc (VParam name (fromStrType typ))
            local (Map.insert (ident ++ "." ++ str) loc) (insertManyL ident rest after)

insertManyAssP :: String -> Type -> QuadMonad (QuadCode) -> QuadMonad (QuadCode)
insertManyAssP ident typ after = do
    map <- gets classInfoMap
    case Map.lookup typ map of
        Just info -> do
            let attrlist = listOfAttrs info
            insertManyP ident attrlist after

insertManyL :: String -> [(Type, String)] -> QuadMonad (QuadCode) -> QuadMonad (QuadCode)
insertManyL _ [] after = after
insertManyL ident ((typ, str) : rest) after = do
    name <- newName Nothing (ident ++ "." ++ str) False 0 True
    env <- ask
    case Map.lookup (ident ++ "." ++ str) env of
        Just loc -> do
            qinsert loc (VLocal name (fromStrType typ))
            insertManyL ident rest after
        Nothing -> do
            loc <- alloc 
            qinsert loc (VLocal name (fromStrType typ))
            local (Map.insert (ident ++ "." ++ str) loc) (insertManyL ident rest after)

insertManyAssL :: String -> Type -> QuadMonad (QuadCode) -> QuadMonad (QuadCode)
insertManyAssL ident typ after = do
    map <- gets classInfoMap
    case Map.lookup typ map of
        Just info -> do
            let attrlist = listOfAttrs info
            insertManyL ident attrlist after

updateVarTypeMap :: String -> Type -> QuadMonad ()
updateVarTypeMap var typ = modify (\st -> st {varTypeMap = Map.insert var typ (varTypeMap st)})

genStmt :: [L.Stmt] -> QuadCode -> QuadMonad (QuadCode)
genStmt [] code = return code
genStmt (L.Empty _ : rest) code = genStmt rest code
genStmt (L.BStmt _ (L.Block _ stmts) : rest) code = do
    code1 <- genStmt stmts []
    genStmt rest (code ++ code1)
genStmt (L.Decl _ _ [] : rest) code = genStmt rest code
genStmt (L.Decl p t (L.NoInit p2 ident : items) : rest) code = do
    case t of
        L.Int _ -> genStmt (L.Decl p t (L.Init p2 ident (L.ELitInt Nothing 0) : items) : rest) code
        L.Str _ -> genStmt (L.Decl p t (L.Init p2 ident (L.EString Nothing "") : items) : rest) code 
        L.Bool _ -> genStmt (L.Decl p t (L.Init p2 ident (L.ELitFalse Nothing) : items) : rest) code
        typ@(L.Class _ _) -> genStmt (L.Decl p t (L.Init p2 ident (L.ENull Nothing typ) : items) : rest) code
genStmt (L.Decl p t (L.Init p2 (L.Ident ident) exp : items) : rest) code = do
    loc <- alloc
    name <- newName Nothing ident True loc False
    updateVarTypeMap name (lStrType t)
    (val, newCode, _) <- genExp exp (Just (VLocal name (fromLType t)))

    qinsert loc (VLocal name (fromLType t))

    let newCode2 = if lhsIsRhs name val then [] else [QAss (VLocal name (fromLType t)) val]

    classtype <- isClassType (lStrType t)
    case classtype of
        False -> local (Map.insert ident loc) (genStmt (L.Decl p t items : rest) (code ++ newCode ++ newCode2))
        True -> do
            map <- gets classInfoMap
            case Map.lookup (lStrType t) map of
                Just info -> do
                    let attrlist = listOfAttrs info
                    aloc <- allocMore (length attrlist)

                    insertManyDecl (extendLocs aloc (length attrlist)) ident attrlist

                    env <- ask
                    let newEnv = modifyEnv env (extendLocs aloc (length attrlist)) ident attrlist
                    local (\_ -> Map.insert ident loc newEnv) (genStmt (L.Decl p t items : rest) (code ++ newCode ++ newCode2))
genStmt (L.Ass pos (L.Ident ident) exp : rest) code = do
    var <- qask ident
    case var of
        Just (VParam _ _) -> do
            name <- newName Nothing ident False 0 False
            (val, newCode, _) <- genExp exp (Just (VParam name IntVar))
            env <- ask
            case Map.lookup ident env of
                Nothing -> formatErrorQ pos $ "(Param) Bug in assignment: '" ++ ident ++ "' not found" 
                Just loc -> do
                    qinsert loc (VParam name (typeOfVal val))
                    let newCode2 = if lhsIsRhs name val then [] else [QAss (VParam name (typeOfVal val)) val]

                    case typeOfVal val of
                        ClassVar t -> do
                            insertManyAssP ident t (genStmt rest (code ++ newCode ++ newCode2))
                        _ -> genStmt rest (code ++ newCode ++ newCode2)
        _ -> do
            name <- newName Nothing ident False 0 True
            (val, newCode, _) <- genExp exp (Just (VLocal name IntVar))

            env <- ask
            case Map.lookup ident env of
                Nothing -> genStmt (L.Ass2 pos (L.EVar Nothing (L.Ident "self")) (L.Ident ident) exp : rest) code
                    --formatErrorQ pos $ "Bug in assignment: '" ++ ident ++ "' not found" 
                Just loc -> do
                    qinsert loc (VLocal name (typeOfVal val))
                    let newCode2 = if lhsIsRhs name val then [] else [QAss (VLocal name (typeOfVal val)) val]
                    case typeOfVal val of
                        ClassVar t -> do
                            insertManyAssL ident t (genStmt rest (code ++ newCode ++ newCode2))
                        _ -> genStmt rest (code ++ newCode ++ newCode2)
genStmt (L.Ass2 pos expl (L.Ident i) exp : rest) code = do
    let ident = exprToIdent expl ++ "." ++ i
    var <- qask ident
    case var of
        Just (VParam _ _) -> do
            name <- newName Nothing ident False 0 False
            (val, newCode, _) <- genExp exp (Just (VParam name IntVar))
            env <- ask
            case Map.lookup ident env of
                Nothing -> formatErrorQ pos $ "(Param) Bug in assignment: '" ++ ident ++ "' not found" 
                Just loc -> do
                    qinsert loc (VParam name (typeOfVal val))
                    let newCode2 = if lhsIsRhs name val then [] else [QAss (VParam name (typeOfVal val)) val]

                    case typeOfVal val of
                        ClassVar t -> do
                            insertManyAssP ident t (genStmt rest (code ++ newCode ++ newCode2))
                        _ -> genStmt rest (code ++ newCode ++ newCode2)
        _ -> do
            name <- newName Nothing ident False 0 True
            (val, newCode, _) <- genExp exp (Just (VLocal name IntVar))

            env <- ask
            case Map.lookup ident env of
                Nothing -> formatErrorQ pos $ "Bug in assignment: '" ++ ident ++ "' not found" 
                Just loc -> do
                    qinsert loc (VLocal name (typeOfVal val))
                    let newCode2 = if lhsIsRhs name val then [] else [QAss (VLocal name (typeOfVal val)) val]
                    case typeOfVal val of
                        ClassVar t -> do
                            insertManyAssL ident t (genStmt rest (code ++ newCode ++ newCode2))
                        _ -> genStmt rest (code ++ newCode ++ newCode2)
genStmt (L.Incr p ident : rest) code = genStmt (L.Ass p ident (L.EAdd Nothing (L.EVar Nothing ident) (L.Plus Nothing) (L.ELitInt Nothing 1)) : rest) code
genStmt (L.Incr2 p expr ident : rest) code = genStmt (L.Ass2 p expr ident (L.EAdd Nothing (L.EAttr Nothing expr ident) (L.Plus Nothing) (L.ELitInt Nothing 1)) : rest) code
genStmt (L.Decr p ident : rest) code = genStmt (L.Ass p ident (L.EAdd Nothing (L.EVar Nothing ident) (L.Minus Nothing) (L.ELitInt Nothing 1)) : rest) code
genStmt (L.Decr2 p expr ident : rest) code = genStmt (L.Ass2 p expr ident (L.EAdd Nothing (L.EAttr Nothing expr ident) (L.Minus Nothing) (L.ELitInt Nothing 1)) : rest) code
genStmt (L.Ret _ exp : rest) code = do
    (val, newCode, _) <- genExp exp Nothing
    genStmt [] (code ++ newCode ++ [QRet val])
genStmt (L.VRet _ : rest) code = do
    genStmt [] (code ++ [QVRet])
genStmt (L.Cond _ exp stmt : rest) code = do
    name <- newName Nothing "if#" False 0 False
    (val1, code1, _) <- genExp exp (Just (VLocal name BoolVar))
    newCode <- genStmt [stmt] []

    (labeltrue, labelcont) <- ifLabels

    let ifCode = code1 ++ [QIf val1 labeltrue, QGoto labelcont, QLabel labeltrue] ++ newCode ++ [QLabel labelcont]

    genStmt rest (code ++ ifCode)
genStmt (L.CondElse _ exp stmt1 stmt2 : rest) code = do
    name <- newName Nothing "ifelse#" False 0 False
    (val1, code1, _) <- genExp exp (Just (VLocal name BoolVar))
    newCode1 <- genStmt [stmt1] []
    newCode2 <- genStmt [stmt2] []

    (labeltrue, labelfalse, labelcont) <- ifElseLabels

    let ifElseCode = code1 ++ [QIf val1 labeltrue, QGoto labelfalse, QLabel labelfalse] ++ newCode2 ++ [QGoto labelcont, QLabel labeltrue] ++ newCode1 ++ [QLabel labelcont]

    genStmt rest (code ++ ifElseCode)
genStmt (L.While _ exp stmt : rest) code = do
    name <- newName Nothing "while#" False 0 False

    newCode <- genStmt [stmt] []
    (val1, code1, _) <- genExp exp (Just (VLocal name BoolVar))

    (labelwhile, labelcond, labelcont) <- whileLabels

    let whileCode = [QGoto labelcond, QLabel labelwhile] ++ newCode ++ [QLabel labelcond] ++ code1 ++ [QIf val1 labelwhile, QLabel labelcont]

    genStmt rest (code ++ whileCode)
genStmt (L.SExp _ exp : rest) code = do
    (val, newCode, _) <- genExp exp Nothing
    genStmt rest (code ++ newCode)

getTypeFromList :: String -> [(Type, String, L.CStmt)] -> Type
getTypeFromList name ((typ, str, _) : rest) =
    case name == str of
        True -> typ
        False -> getTypeFromList name rest

returnTypeOf :: String -> String -> QuadMonad Type
returnTypeOf base method = do
    var <- qask base

    let basetype = do
        case var of
            Just (VLocal _ (ClassVar t)) -> t
            Just (VParam _ (ClassVar t)) -> t

    cim <- gets classInfoMap
    case Map.lookup basetype cim of
        Nothing -> throwError $ "BUGGGGG " ++ basetype
        Just info -> do
            let methods = listOfMethods info
            return $ getTypeFromList method methods

type Depth = Int
genExp :: L.Expr -> Maybe Var -> QuadMonad (Val, QuadCode, Depth)
genExp (L.EVar pos (L.Ident ident)) _ = do
    var <- qask ident


    case var of
        Nothing -> genExp (L.EAttr Nothing (L.EVar pos (L.Ident "self")) (L.Ident ident)) Nothing
            --formatErrorQ pos $ "Variable '" ++ ident ++ "' not defined (bug)"
        Just (VLocal name t) -> do
            return ((LocVal name t), [], 0)
        Just (VParam name t) -> return ((ParVal name t), [], 0)
genExp (L.ELitInt _ i) _ = return (IntVal (fromInteger i), [], 1)
genExp (L.ELitTrue _) _ = return (BoolVal True, [], 1)
genExp (L.ELitFalse _) _ = return (BoolVal False, [], 1)
genExp (L.EApp _ (L.Ident ident) exps) preName = do
    let genExp2 exp = genExp exp Nothing
    list <- mapM genExp2 exps

    res <- newName preName "tmp#" False 0 False

    let (vals, codes, depths) = unzip3 (list) where
        sortGT (a1, b1, c1) (a2, b2, c2)
            | c2 > c1 = LT
            | otherwise = GT

    funMap <- gets funTypeMap
    let (Just t) = Map.lookup ident funMap
    
    case preName of
        Just (VParam _ _) -> do
            let qcall = [QCall (VParam res t) ident (length list)]
            let code = concat codes ++ reverse (foldr (\val acc -> QParam val : acc) [] vals) ++ qcall
            return (ParVal res t, code, maximum (sumLists depths (take (length list) [1, 2..]))) where
                sumLists :: [Int] -> [Int] -> [Int]
                sumLists [] [] = []
                sumLists (a : as) (b : bs) = (a + b) : sumLists as bs
        _ -> do
            let qcall = [QCall (VLocal res t) ident (length list)]
            let code = concat codes ++ reverse (foldr (\val acc -> QParam val : acc) [] vals) ++ qcall
            return (LocVal res t, code, maximum (sumLists depths (take (length list) [1, 2..]))) where
                sumLists :: [Int] -> [Int] -> [Int]
                sumLists [] [] = []
                sumLists (a : as) (b : bs) = (a + b) : sumLists as bs
genExp (L.EMethod _ exp1 (L.Ident ident) exps) preName = do
    let genExp2 exp = genExp exp Nothing
    list <- mapM genExp2 exps
    let (vals, codes, depths) = unzip3 list
    (val1, code1, depth1) <- genExp exp1 Nothing

    res <- newName preName "tmp#" False 0 False

    env <- ask
    st <- gets store
    
    let typ = fromVal val1
    metType <- findMethodType typ ident

    let hiddenparam = [QParam val1]

    case preName of
        Just (VParam _ _) -> do
            let qcall = [QCallM (VParam res (fromStrType metType)) val1 ident (length list + 1)]
            let code = code1 ++ concat codes ++ reverse (foldr (\val acc -> QParam val : acc) [] vals) ++ hiddenparam ++ qcall
            return (ParVal res (fromStrType metType), code, maximum (sumLists depths (take (length list) [1, 2..]))) where
                sumLists :: [Int] -> [Int] -> [Int]
                sumLists [] [] = []
                sumLists (a : as) (b : bs) = (a + b) : sumLists as bs
        _ -> do
            let qcall = [QCallM (VLocal res (fromStrType metType)) val1 ident (length list + 1)]
            let code = code1 ++ concat codes ++ reverse (foldr (\val acc -> QParam val : acc) [] vals) ++ hiddenparam ++ qcall
            return (LocVal res (fromStrType metType), code, maximum (sumLists depths (take (length list) [1, 2..]))) where
                sumLists :: [Int] -> [Int] -> [Int]
                sumLists [] [] = []
                sumLists (a : as) (b : bs) = (a + b) : sumLists as bs
genExp (L.EAttr _ exp (L.Ident ident)) preName = do
    (val1, code1, depth1) <- genExp exp Nothing
    res <- newName preName "tmp#" False 0 False
    let typ = fromVal val1
    
    attrType <- findAttrType typ ident

    case preName of
        Just (VParam _ _) -> do
            let code = code1 ++ [QAttr (VParam res (fromStrType attrType)) val1 ident]
            return (ParVal res (fromStrType attrType), code, depth1)
        _ -> do
            let code = code1 ++ [QAttr (VLocal res (fromStrType attrType)) val1 ident]
            return (LocVal res (fromStrType attrType), code, depth1)
genExp (L.EString _ str) preName = return (StrVal str, [], 1)
genExp (L.ENull _ t) _ = return (ClassVal (lStrType t) Null, [], 1)
genExp (L.ENewClass _ t) _ = do
    map <- gets classInfoMap
    case Map.lookup (lStrType t) map of
        Just info -> do
            let attrlist = listOfAttrs info
            let classlist = initClassList attrlist where
                initClassList :: [(Type, String)] -> [(String, Val)]
                initClassList [] = []
                initClassList ((typ, str) : rest) = case typ of
                    "int" -> (str, IntVal 0) : initClassList rest
                    "boolean" -> (str, BoolVal False) : initClassList rest
                    "string" -> (str, StrVal "") : initClassList rest
                    c -> (str, ClassVal c Null) : initClassList rest
            return (ClassVal (lStrType t) (Content classlist), [], 1)
genExp (L.Neg _ exp) preName = do
    (val1, code1, depth1) <- genExp exp Nothing
    res <- newName preName "tmp#" False 0 False
    case preName of
        Just (VParam _ _) -> do
            let code = code1 ++ [QNeg (VParam res IntVar) val1]
            return (ParVal res IntVar, code, depth1)
        _ -> do
            let code = code1 ++ [QNeg (VLocal res IntVar) val1]
            return (LocVal res IntVar, code, depth1)
genExp (L.Not _ exp) preName = do
    (val1, code1, depth1) <- genExp exp Nothing
    res <- newName preName "tmp#" False 0 False
    
    case preName of
        Just (VParam _ _) -> do
            let code = code1 ++ [QNot (VParam res BoolVar) val1]
            return (ParVal res BoolVar, code, depth1)
        _ -> do
            let code = code1 ++ [QNot (VLocal res BoolVar) val1]
            return (LocVal res BoolVar, code, depth1)
genExp (L.EMul _ exp1 (L.Times _) exp2) preName = do
    (val1, code1, depth1) <- genExp exp1 Nothing
    (val2, code2, depth2) <- genExp exp2 Nothing
    res <- newName preName "tmp#" False 0 False
    
    case preName of
        Just (VParam _ _) -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QMul (VParam res IntVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QMul (VParam res IntVar) val1 val2])
            return (ParVal res IntVar, code, (min depth1 depth2) + 1)
        _ -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QMul (VLocal res IntVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QMul (VLocal res IntVar) val1 val2])
            return (LocVal res IntVar, code, (min depth1 depth2) + 1)
genExp (L.EMul _ exp1 (L.Div _) exp2) preName = do
    (val1, code1, depth1) <- genExp exp1 Nothing
    (val2, code2, depth2) <- genExp exp2 Nothing
    res <- newName preName "tmp#" False 0 False

    case preName of
        Just (VParam _ _) -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QDiv (VParam res IntVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QDiv (VParam res IntVar) val1 val2])
            return (ParVal res IntVar, code, (min depth1 depth2) + 1)
        _ -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QDiv (VLocal res IntVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QDiv (VLocal res IntVar) val1 val2])
            return (LocVal res IntVar, code, (min depth1 depth2) + 1)
genExp (L.EMul _ exp1 (L.Mod _) exp2) preName = do
    (val1, code1, depth1) <- genExp exp1 Nothing
    (val2, code2, depth2) <- genExp exp2 Nothing
    res <- newName preName "tmp#" False 0 False
    
    case preName of
        Just (VParam _ _) -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QMod (VParam res IntVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QMod (VParam res IntVar) val1 val2])
            return (ParVal res IntVar, code, (min depth1 depth2) + 1)
        _ -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QMod (VLocal res IntVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QMod (VLocal res IntVar) val1 val2])
            return (LocVal res IntVar, code, (min depth1 depth2) + 1)
genExp (L.EAdd _ exp1 (L.Plus _) exp2) preName = do --poprawic
    (val1, code1, depth1) <- genExp exp1 Nothing
    (val2, code2, depth2) <- genExp exp2 Nothing
    res <- newName preName "tmp#" False 0 False
    let resType = checkType val1

    case preName of
        Just (VParam _ _) -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QAdd (VParam res resType) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QAdd (VParam res resType) val1 val2])
            return (ParVal res resType, code, (min depth1 depth2) + 1)
        _ -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QAdd (VLocal res resType) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QAdd (VLocal res resType) val1 val2])
            return (LocVal res resType, code, (min depth1 depth2) + 1)
genExp (L.EAdd _ exp1 (L.Minus _) exp2) preName = do
    (val1, code1, depth1) <- genExp exp1 Nothing
    (val2, code2, depth2) <- genExp exp2 Nothing
    res <- newName preName "tmp#" False 0 False
    
    case preName of
        Just (VParam _ _) -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QSub (VParam res IntVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QSub (VParam res IntVar) val1 val2])
            return (ParVal res IntVar, code, (min depth1 depth2) + 1)
        _ -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QSub (VLocal res IntVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QSub (VLocal res IntVar) val1 val2])
            return (LocVal res IntVar, code, (min depth1 depth2) + 1)
genExp (L.EAnd _ exp1 exp2) preName = do
    (val1, code1, depth1) <- genExp (L.Not Nothing exp1) Nothing
    (val2, code2, depth2) <- genExp (L.Not Nothing exp2) Nothing
    res <- newName preName "tmp#" False 0 False

    (labelfalse, labelcont) <- ifLabels
    
    case preName of
        Just (VParam _ _) -> do
            let code = code1 ++ [QIf val1 labelfalse] ++ code2 ++ [QIf val2 labelfalse] ++ [QAss (VParam res BoolVar) (BoolVal True), QGoto labelcont, QLabel labelfalse, QAss (VParam res BoolVar) (BoolVal False), QLabel labelcont]
            return (ParVal res BoolVar, code, (min depth1 (depth2 + 1)))
        _ -> do
            let code = code1 ++ [QIf val1 labelfalse] ++ code2 ++ [QIf val2 labelfalse] ++ [QAss (VLocal res BoolVar) (BoolVal True), QGoto labelcont, QLabel labelfalse, QAss (VLocal res BoolVar) (BoolVal False), QLabel labelcont]
            return (LocVal res BoolVar, code, (min depth1 (depth2 + 1)))
genExp (L.EOr _ exp1 exp2) preName = do
    (val1, code1, depth1) <- genExp exp1 Nothing
    (val2, code2, depth2) <- genExp exp2 Nothing
    res <- newName preName "tmp#" False 0 False

    (labeltrue, labelcont) <- ifLabels

    case preName of
        Just (VParam _ _) -> do
            let code = code1 ++ [QIf val1 labeltrue] ++ code2 ++ [QIf val2 labeltrue] ++ [QAss (VParam res BoolVar) (BoolVal False), QGoto labelcont, QLabel labeltrue, QAss (VParam res BoolVar) (BoolVal True), QLabel labelcont]
            return (ParVal res BoolVar, code, (min depth1 (depth2 + 1)))
        _ -> do
            let code = code1 ++ [QIf val1 labeltrue] ++ code2 ++ [QIf val2 labeltrue] ++ [QAss (VLocal res BoolVar) (BoolVal False), QGoto labelcont, QLabel labeltrue, QAss (VLocal res BoolVar) (BoolVal True), QLabel labelcont]
            return (LocVal res BoolVar, code, (min depth1 (depth2 + 1)))
genExp (L.ERel _ exp1 (L.EQU _) exp2) preName = do --poprawic
    (val1, code1, depth1) <- genExp exp1 Nothing
    (val2, code2, depth2) <- genExp exp2 Nothing
    res <- newName preName "tmp#" False 0 False
    
    case preName of
        Just (VParam _ _) -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QCmpEq (VParam res BoolVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QCmpEq (VParam res BoolVar) val1 val2])
            return (LocVal res BoolVar, code, (min depth1 depth2) + 1)
        _ -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QCmpEq (VLocal res BoolVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QCmpEq (VLocal res BoolVar) val1 val2])
            return (LocVal res BoolVar, code, (min depth1 depth2) + 1)
genExp (L.ERel p1 exp1 (L.NE p2) exp2) preName = genExp (L.Not p1 (L.ERel p1 exp1 (L.EQU p2) exp2)) preName
genExp (L.ERel _ exp1 (L.LTH _) exp2) preName = do
    (val1, code1, depth1) <- genExp exp1 Nothing
    (val2, code2, depth2) <- genExp exp2 Nothing
    res <- newName preName "tmp#" False 0 False
    let code | depth2 > depth1 = (code2 ++ code1 ++ [QCmpLth (VLocal res BoolVar) val1 val2])
             | otherwise = (code1 ++ code2 ++ [QCmpLth (VLocal res BoolVar) val1 val2])
    case preName of
        Just (VParam _ _) -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QCmpLth (VParam res BoolVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QCmpLth (VParam res BoolVar) val1 val2])
            return (LocVal res BoolVar, code, (min depth1 depth2) + 1)
        _ -> do
            let code | depth2 > depth1 = (code2 ++ code1 ++ [QCmpLth (VLocal res BoolVar) val1 val2])
                     | otherwise = (code1 ++ code2 ++ [QCmpLth (VLocal res BoolVar) val1 val2])
            return (LocVal res BoolVar, code, (min depth1 depth2) + 1)
genExp (L.ERel p1 exp1 (L.LE p2) exp2) preName = genExp (L.EOr p1 (L.ERel p1 exp1 (L.LTH p2) exp2) (L.ERel p1 exp1 (L.EQU p2) exp2)) preName
genExp (L.ERel p1 exp1 (L.GTH p2) exp2) preName = genExp (L.ERel p1 exp2 (L.LTH p2) exp1) preName
genExp (L.ERel p1 exp1 (L.GE p2) exp2) preName = genExp (L.EOr p1 (L.ERel p1 exp1 (L.GTH p2) exp2) (L.ERel p1 exp1 (L.EQU p2) exp2)) preName

findAttrType :: Type -> String -> QuadMonad Type
findAttrType typ str = do
    cm <- gets classInfoMap
    case Map.lookup typ cm of
        Just info -> do
            let attrs = listOfAttrs info
            case findInList True str attrs of
                Right t -> return t

findMethodType :: Type -> String -> QuadMonad Type
findMethodType typ str = do
    cm <- gets classInfoMap
    
    case Map.lookup typ cm of
        Just info -> do
            let methods = listOfMethods info
            case findInList False str (map hlp12 methods) of
                Right t -> return t

hlp12 :: (a, b, c) -> (a, b)
hlp12 (a, b, c) = (a, b)

hlp2 :: (a, b, c) -> b
hlp2 (a, b, c) = b

hlp3 :: (a, b, c) -> c
hlp3 (a, b, c) = c

findInList :: Bool -> String -> [(Type, String)] -> Either String Type
findInList b str [] = Left $ "Could not find " ++ if b == True then "attribute" else "method" ++ " with name " ++ str
findInList b str ((typ, s) : rest) = 
    case str == s of
        True -> Right typ
        False -> findInList b str rest

checkType :: Val -> VarType
checkType (IntVal _) = IntVar
checkType (StrVal _) = StrVar
checkType (LocVal _ t) = t
checkType (ParVal _ t) = t

preprocessParamAttrs :: String -> Loc -> [(Type, String)] -> QEnv -> QStore -> String -> QuadMonad(Loc, QEnv, QStore)
preprocessParamAttrs _ loc [] env store _ = return (loc, env, store)
preprocessParamAttrs ident loc ((typ, str) : rest) env store funname = do
    preprocessParamAttrs ident (loc + 1) rest (Map.insert (ident ++ "." ++ str) (loc + 1) env) (Map.insert (loc + 1) (VParam (ident ++ "." ++ str ++ "#" ++ funname) (fromStrType typ)) store) funname

preprocessFunction :: [L.Arg] -> String -> QuadMonad (Loc, QEnv, QStore)
preprocessFunction [] funname = return (0, Map.empty, Map.empty)
preprocessFunction (L.Arg _ t (L.Ident ident) : args) funname = do
    (locs, env, store) <- preprocessFunction args funname
    case fromLType t of
        ClassVar typ -> do
            map <- gets classInfoMap
            case Map.lookup typ map of
                Just info -> do
                    let attrlist = listOfAttrs info
                    updateVarTypeMap (ident ++ "#" ++ funname) (lStrType t)
                    preprocessParamAttrs ident (locs + 1) attrlist (Map.insert ident (locs + 1) env) (Map.insert (locs + 1) (VParam (ident ++ "#" ++ funname) (fromLType t)) store) funname
        _ -> return (locs + 1, Map.insert ident (locs + 1) env, Map.insert (locs + 1) (VParam (ident ++ "#" ++ funname) (fromLType t)) store)

genQuadCode :: [L.TopDef] -> QuadMonad ()
genQuadCode [] = return ()
genQuadCode (L.FnDef _ t (L.Ident ident) args (L.Block _ stmts) : rest) = do

    (locs, env, store) <- preprocessFunction args ident
    modify (\st -> st {curFunName = ident})
    setStore locs store
    code <- local (\_ -> env) (genStmt (stmts) [])
    clearStore

    let newCode = code ++ neededRet where
        neededRet = case t of
            L.Void _ -> [QVRet]
            _ -> []

    tell $ [QFunc True ident args (QLabel ident : newCode)]
    genQuadCode rest
genQuadCode (L.ClassDef _ (L.Ident ident) (L.CBlock _ stmts) : rest) = do
    cim <- gets classInfoMap
    case Map.lookup ident cim of
        Just info -> do
            genClass ident list where
                list2 = unzip3 (listOfMethods info)
                list = hlp3 list2

    genQuadCode rest
genQuadCode (L.CDefExt pos ident _ block : rest) = genQuadCode (L.ClassDef pos ident block : rest)

genClass :: Type -> [L.CStmt] -> QuadMonad ()
genClass _ [] = return ()
genClass typ (L.CEmpty _ : rest) = genClass typ rest
genClass typ (L.CDecl _ _ _ : rest) = genClass typ rest
genClass typ (L.CMethod _ retType (L.Ident ident) args (L.Block _ stmts) : rest) = do
    let funname = ("." ++ typ ++ "$" ++ ident)
    (locs, env, store) <- preprocessFunction (L.Arg Nothing (L.Class Nothing (L.Ident typ)) (L.Ident "self") : args) funname
    modify (\st -> st {curFunName = funname})
    setStore locs store
    code <- local (\_ -> env) (genStmt stmts [])
    clearStore

    let newCode = code ++ neededRet where
        neededRet = case retType of
            L.Void _ -> [QVRet]
            _ -> []

    tell $ [QFunc False funname (L.Arg Nothing (L.Class Nothing (L.Ident typ)) (L.Ident "self") : args) (QLabel funname : newCode)]
    genClass typ rest