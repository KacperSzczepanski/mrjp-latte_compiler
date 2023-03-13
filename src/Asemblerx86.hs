module Asemblerx86 where

import Quadcode

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

debugx :: Show a => String -> a -> X86Monad ()
debugx msg a = do
    liftIO $ hPutStrLn stderr $ "DEBUG: " ++ msg ++ show a
    return ()

formatError :: Pos -> String -> X86Monad a
formatError pos err = throwError (errMessage pos err)

vtreg :: String
vtreg = "esi"

data Instructionx86 = XPush String
                    | XPush2 String
                    | XPop String
                    | XMov String String
                    | XCall String
                    | XLea String String
                    | XAdd String String
                    | XSub String String
                    | XMul String String
                    | XDiv String
                    | XNot String
                    | XOr String String
                    | XAnd String String
                    | XXor String String
                    | XRet
                    | XLabel String
                    | XLeave
                    | XIntelSyntax
                    | XGlobal String
                    | XExtern String
                    | XEmpty
                    | XEntry
                    | XJump String
                    | XReset String
                    | XCmp String String
                    | XSete String
                    | XSeto String
                    | XSets String
                    | XJmp String
                    | XJne String
                    | XComment String
                    | XString String

instance Show Instructionx86 where
    showList is s       = unlines (map show is) ++ s
    show (XPush r)      = tab ++ "push    " ++ r
    show (XPush2 r)     = tab ++ "push    " ++ r ++ "\n" ++
                          tab ++ show (XPop "edi") ++ "\n" ++
                          tab ++ show (XPop "eax") ++ "\n" ++
                          tab ++ show (XPush "edi") ++ "\n" ++
                          tab ++ show (XPush "eax")
    show (XPop r)       = tab ++ "pop     " ++ r
    show (XMov r1 r2)   = tab ++ "mov     " ++ r1 ++ ", " ++ r2
    show (XCall f)      = tab ++ "call    " ++ f
    show (XLea r a)     = tab ++ "lea     " ++ r ++ ", " ++ a
    show (XAdd r1 r2)   = tab ++ "add     " ++ r1 ++ ", " ++ r2
    show (XSub r1 r2)   = tab ++ "sub     " ++ r1 ++ ", " ++ r2
    show (XMul r1 r2)   = tab ++ "imul    " ++ r1 ++ ", " ++ r2
    show (XDiv r1)      = tab ++ "cdq\n" ++ tab ++ "idiv    " ++ r1
    show (XNot r)       = tab ++ "not     " ++ r
    show (XOr r1 r2)    = tab ++ "or      " ++ r1 ++ ", " ++ r2
    show (XAnd r1 r2)   = tab ++ "and     " ++ r1 ++ ", " ++ r2
    show (XXor r1 r2)   = tab ++ "xor     " ++ r1 ++ ", " ++ r2
    show XRet           = tab ++ "ret"
    show (XLabel l)     = l ++ ":"
    show XLeave         = tab ++ "leave"
    show XIntelSyntax   = tab ++ ".intel_syntax noprefix"
    show (XGlobal f)    = tab ++ ".globl " ++ f
    show (XExtern f)    = tab ++ ".extern " ++ f
    show (XEmpty)       = ""
    show (XEntry)       = show (XPush "ebp") ++ "\n" ++ show (XMov "ebp" "esp")
    show (XJump l)      = tab ++ "jmp     " ++ l
    show (XReset r)     = tab ++ "mov     " ++ r ++ ", 0"
    show (XCmp r1 r2)   = tab ++ "cmp     " ++ r1 ++ ", " ++ r2
    show (XSete r)      = tab ++ "sete    " ++ r
    show (XSeto r)      = tab ++ "seto    " ++ r
    show (XSets r)      = tab ++ "sets    " ++ r
    show (XJmp l)       = tab ++ "jmp     " ++ l
    show (XJne l)       = tab ++ "jne     " ++ l
    show (XComment c)   = "# " ++ c
    show (XString s)    = tab ++ ".string " ++ show s

addToReg :: String -> Int -> String
addToReg reg n | n > 0  = reg ++ " + " ++ show n
               | n == 0 = reg
               | n < 0  = reg ++ " - " ++ show (-n)

inBracket :: String -> String
inBracket reg = "[" ++ reg ++ "]"

memShift :: String -> Int -> String
memShift reg n | n > 0  = "[" ++ reg ++ " + " ++ show n ++ "]"
               | n == 0 = "[" ++ reg ++ "]"
               | n < 0  = "[" ++ reg ++ " - " ++ show (-n) ++ "]"

stackShift :: Int -> String
stackShift n | n > 0  = "[ebp + " ++ show (n * 4) ++ "]"
             | n == 0 = "[ebp]"
             | n < 0  = "[ebp - " ++ show ((-n) * 4) ++ "]"

paramNum :: Int -> Int
paramNum n = n + 1

localNum :: Int -> Int
localNum n = (-n)

paramShift :: Int -> String
paramShift n = stackShift (n + 1)
localShift :: Int -> String
localShift n = stackShift (-n)

global_ :: String -> [Instructionx86]
global_ name =
    [(XGlobal name)]

type X86code = [Instructionx86]

type Env = Map.Map String (VarKind Int)
data VarKind a = VarParam a | VarLocal a

data XState = XState {locals :: Int, localsUsed :: Int, strJump :: Int, classMap :: ClassInfoMap, firstLevelType :: Map.Map String Type, vtable :: Map.Map Type Offset}
initXState :: ClassInfoMap -> Map.Map String Type -> XState
initXState cim map = XState {locals = 0, localsUsed = 0, strJump = 1, classMap = cim, firstLevelType = map, vtable = Map.empty}

strLabel :: X86Monad (String, String)
strLabel = state (\st -> ((".jump" ++ show (strJump st), ".str" ++ show (strJump st)), st {strJump = strJump st + 1}))
updateLocals :: Int -> X86Monad ()
updateLocals n = modify (\st -> st {locals = n})
updateUsed :: String -> X86Monad ()
updateUsed s = do
    env <- ask
    case Map.lookup s env of
        Nothing -> modify (\st -> st {localsUsed = localsUsed st + 1})
        _ -> return ()
resetUsed :: X86Monad ()
resetUsed = modify (\st -> st {localsUsed = 0})

type X86Monad a = StateT XState (ReaderT Env (ExceptT String (WriterT X86code IO))) a
runX86Monad :: Env -> XState -> X86Monad a -> IO (Either String (a, XState), X86code)
runX86Monad env st ev = runWriterT (runExceptT (runReaderT (runStateT ev st) env))

getVarNum :: String -> X86Monad (Int)
getVarNum s = do
    let ident = getMainVar s
    env <- ask
    case Map.lookup ident env of
        Nothing -> throwError $ " Variable '" ++ ident ++ "' not defined (bug)"
        Just (VarParam p) -> return p
        Just (VarLocal l) -> return l

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s = 
    case dropWhile p s of
        "" -> []
        s' -> w : wordsWhen p s'' where
            (w, s'') = break p s'

splitByFirstHash :: String -> [String]
splitByFirstHash [] = ["", ""]
splitByFirstHash ('#' : rest) = ["", ('#' : rest)]
splitByFirstHash (c : rest) = [c : first] ++ second where
    res = splitByFirstHash rest
    first = head res
    second = tail res

getAttrsNames :: String -> [String]
getAttrsNames str = list where
    splitted = splitByFirstHash str
    mainPart = head splitted
    list = wordsWhen (== '.') mainPart

getMainVar :: String -> String
getMainVar str = mainIdent ++ hashWord where
    splitted = splitByFirstHash str
    mainPart = head splitted
    splitCommas = wordsWhen (== '.') mainPart
    mainIdent = head splitCommas
    [hashWord] = tail splitted

askNumber :: String -> X86Monad (Int)
askNumber str = do
    let ident = getMainVar str
    env <- ask
    case Map.lookup ident env of
        Nothing -> do
            updateUsed ident
            number <- gets localsUsed
            return number
        Just (VarParam number) -> return number
        Just (VarLocal number) -> return number

initAttrsFromList :: String -> [(String, Offset)] -> X86Monad (X86code)
initAttrsFromList _ [] = return []
initAttrsFromList reg ((_, offset) : rest) = do
    let code = [XMov "ecx" "0", XMov (memShift reg offset) "ecx"]
    res <- initAttrsFromList reg rest
    return $ code ++ res

initAttrs :: Type -> String -> Map.Map String Offset -> X86Monad (X86code)
initAttrs typ reg map = do
    vt <- gets vtable
    let (Just n) = Map.lookup typ vt
    let code = [XMov "ecx" "eax", XPush (show n), XCall ".$get_vtable_reference", XAdd "esp" "4", XMov (memShift "ecx" 0) "eax", XMov "eax" "ecx"]
    nextCode <- initAttrsFromList reg (Map.toList map)
    return $ code ++ nextCode

getNextType :: [(Type, String)] -> String -> Type
getNextType ((typ, str) : rest) name =
    if str == name then
        typ
    else
        getNextType rest name

getOffsetsFromList :: [String] -> Type -> X86Monad ([Int])
getOffsetsFromList [] _ = return []
getOffsetsFromList (attr : rest) typ = do
    map <- gets classMap
    case Map.lookup typ map of
        Just info -> do
            let attrlist = listOfAttrs info
            let nextType = getNextType attrlist attr
            case Map.lookup attr (offset info) of
                Nothing -> throwError "BUG"
                Just n -> do
                    res <- getOffsetsFromList rest nextType
                    return (n : res)

getOffsets :: String -> Type -> X86Monad ([Int])
getOffsets ident typ = do
    let attrs = getAttrsNames ident
    getOffsetsFromList (tail attrs) typ

insertValue :: String -> String -> String -> [Offset] -> X86Monad ()
insertValue resReg _ curReg [offset] = do
    tell $ [XMov (inBracket (addToReg curReg offset)) resReg]
    return ()
insertValue resReg tmpReg curReg offsets@(offset : rest) = do
    tell $ [XMov tmpReg (inBracket (addToReg curReg offset))]
    insertValue resReg tmpReg tmpReg rest

extractValue :: String -> String -> String -> [Offset] -> X86Monad ()
extractValue resReg _ curReg [offset] = do
    tell $ [XMov resReg (inBracket (addToReg curReg offset))]
    return ()
extractValue resReg tmpReg curReg offsets@(offset : rest) = do
    tell $ [XMov tmpReg (inBracket (addToReg curReg offset))]
    extractValue resReg tmpReg tmpReg rest

getFirstLevelType :: String -> Type -> X86Monad (Type)
getFirstLevelType name typ = do
    let ident = getMainVar name
    firstTypeMap <- gets firstLevelType
    case Map.lookup ident firstTypeMap of
        Nothing -> return typ
        Just t -> return t

getTypeOf :: Type -> [String] -> X86Monad Type
getTypeOf typ [] = return typ
getTypeOf typ (attr : rest) = do
    cm <- gets classMap
    case Map.lookup typ cm of
        Just info -> do
            let attrlist = listOfAttrs info
            let nextType = getNextType attrlist attr
            getTypeOf nextType rest
    

getMethodAddress :: String -> String -> String -> String -> String -> X86Monad ()
getMethodAddress var method resReg tmpReg curReg = do
    let mainvar = getMainVar var
    firstType <- getFirstLevelType mainvar "BLAD"
    offsets <- getOffsets var firstType

    env <- ask
    case Map.lookup mainvar env of
        Just (VarParam p) -> do
            extractValue resReg tmpReg curReg (4 * paramNum p : offsets)
        Just (VarLocal l) -> do
            extractValue resReg tmpReg curReg (4 * localNum l : offsets)
    tell $ [XMov resReg (inBracket resReg)] --[eax + nr methody * 4]
    typ <- getTypeOf firstType (tail $ getAttrsNames var)
    cm <- gets classMap
    case Map.lookup typ cm of
        Just info -> do
            let vtablemap = vtableOffset info
            case Map.lookup method vtablemap of
                Just n -> do
                    tell $ [XMov resReg (inBracket (addToReg resReg n))]

get1offset :: Map.Map String Offset -> String -> Offset
get1offset map str = 
    case Map.lookup str map of
        Nothing -> 0
        Just n -> n

translateTox86 :: QuadCode -> X86Monad ()
translateTox86 [] = return ()
translateTox86 (QLabel l : rest) = do
    tell $ [XLabel l]
    translateTox86 rest
translateTox86 (QAss var val : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val]

    number <- askNumber (fromVar var)
    case val of
        IntVal n -> do
            tell $ [XMov "eax" (show n)]
        BoolVal b -> do
            tell $ [XMov "eax" (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)
        StrVal s -> do
            (jump, str) <- strLabel
            tell $ [XJmp jump, XLabel str, XString s, XLabel jump, XLea "eax" ("[" ++ str ++ "]")]
        ClassVal t Null -> do
            tell $ [XMov "eax" (show 0)]
        ClassVal t (Content _) -> do
            map <- gets classMap
            case Map.lookup t map of
                Just info -> do
                    let size = totalSize info
                    tell $ [XPush (show (size * 4)), XCall "malloc", XAdd "esp" "4"]
                    code <- initAttrs t "eax" (offset info)
                    tell code
    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QAdd var val1 val2 : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val1 ++ " + " ++ show val2]
    
    number <- askNumber (fromVar var)

    case val1 of
        IntVal n -> do
            tell $ [XMov "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)
        StrVal s -> do
            (jump, str) <- strLabel
            tell $ [XJmp jump, XLabel str, XString s, XLabel jump, XLea "eax" ("[" ++ str ++ "]")]

    case val2 of
        IntVal n -> do
            tell $ [XAdd "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            case t of
                IntVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
                    tell $ [XAdd "eax" "edi"]
                StrVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
                    tell $ [XPush "edi", XPush "eax", XCall "concatStrings"]
        ParVal s t -> do
            p <- getVarNum s
            case t of
                IntVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
                    tell $ [XAdd "eax" "edi"]
                StrVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
                    tell $ [XPush "edi", XPush "eax", XCall "concatStrings"]
        StrVal s -> do
            (jump, str) <- strLabel
            tell $ [XJmp jump, XLabel str, XString s, XLabel jump, XLea "edi" ("[" ++ str ++ "]"), XPush "edi", XPush "eax", XCall "concatStrings"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QSub var val1 val2 : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val1 ++ " - " ++ show val2]
    
    number <- askNumber (fromVar var)

    case val1 of
        IntVal n -> do
            tell $ [XMov "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)

    case val2 of
        IntVal n -> do
            tell $ [XSub "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
            tell $ [XSub "eax" "edi"]
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
            tell $ [XSub "eax" "edi"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QMul var val1 val2 : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val1 ++ " * " ++ show val2]
    
    number <- askNumber (fromVar var)

    case val1 of
        IntVal n -> do
            tell $ [XMov "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)

    case val2 of
        IntVal n -> do
            tell $ [XMul "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
            tell $ [XMul "eax" "edi"]
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
            tell $ [XMul "eax" "edi"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QDiv var val1 val2 : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val1 ++ " / " ++ show val2]
    
    number <- askNumber (fromVar var)

    tell $ [XReset "eax"]

    case val1 of
        IntVal n -> do
            tell $ [XMov "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)

    case val2 of
        IntVal n -> do
            tell $ [XMov "edi" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)

    tell $ [XReset "edx", XDiv "edi"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QMod var val1 val2 : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val1 ++ " % " ++ show val2]
    
    number <- askNumber (fromVar var)

    tell $ [XReset "edx"]

    case val1 of
        IntVal n -> do
            tell $ [XMov "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)

    case val2 of
        IntVal n -> do
            tell $ [XMov "edi" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)

    tell $ [XReset "edx", XDiv "edi"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "edx" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "edx" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QNeg var val : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = -" ++ show val]

    
    number <- askNumber (fromVar var)

    case val of
        IntVal n -> do
            tell $ [XMov "edi" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)

    tell $ [XReset "eax", XSub "eax" "edi"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QAnd var val1 val2 : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val1 ++ " and " ++ show val2]
    
    number <- askNumber (fromVar var)

    case val1 of
        BoolVal b -> do
            tell $ [XMov "eax" (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)

    case val2 of
        BoolVal b -> do
            tell $ [XAnd "eax" (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
            tell $ [XAnd "eax" "edi"]
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
            tell $ [XAnd "eax" "edi"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QOr var val1 val2 : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val1 ++ " or " ++ show val2]
    
    number <- askNumber (fromVar var)

    case val1 of
        BoolVal b -> do
            tell $ [XMov "eax" (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)

    case val2 of
        BoolVal b -> do
            tell $ [XOr "eax" (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
            tell $ [XOr "eax" "edi"]
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
            tell $ [XOr "eax" "edi"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QNot var val : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = not " ++ show val]
    
    number <- askNumber (fromVar var)

    tell $ [XReset "eax"]

    case val of
        BoolVal b -> do
            tell $ [XMov "eax" (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)
    
    tell $ [XXor "al" "1"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QCmpEq var val1 val2 : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val1 ++ " == " ++ show val2]
    
    number <- askNumber (fromVar var)

    case val1 of
        IntVal n -> do
            tell $ [XMov "eax" (show n)]
        BoolVal b -> do
            tell $ [XMov "eax" (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)
        StrVal s -> do
            (jump, str) <- strLabel
            tell $ [XJmp jump, XLabel str, XString s, XLabel jump, XLea "eax" ("[" ++ str ++ "]")]
        ClassVal t Null -> do
            tell $ [XMov "eax" "0"]
        ClassVal t (Content _) -> do
            map <- gets classMap
            case Map.lookup t map of
                Just info -> do
                    let size = totalSize info
                    tell $ [XPush (show (size * 4)), XCall "malloc", XAdd "esp" "4"]
                    code <- initAttrs t "eax" (offset info)
                    tell code


    case val2 of
        IntVal n -> do
            tell $ [XCmp "eax" (show n), XReset "eax", XSete "al"]
        BoolVal b -> do
            tell $ [XCmp "eax" (show (fromEnum b)), XReset "eax", XSete "al"]
        LocVal s t -> do
            l <- getVarNum s
            case t of
                IntVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
                    tell $ [XCmp "eax" "edi", XReset "eax", XSete "al"]
                BoolVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
                    tell $ [XCmp "eax" "edi", XReset "eax", XSete "al"]
                StrVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
                    tell $ [XPush "eax", XPush "edi", XCall "compareStrings"]
                ClassVar typ -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
                    tell $ [XCmp "eax" "edi", XReset "eax", XSete "al"]
        ParVal s t -> do
            p <- getVarNum s
            case t of
                IntVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
                    tell $ [XCmp "eax" "edi", XReset "eax", XSete "al"]
                BoolVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
                    tell $ [XCmp "eax" "edi", XReset "eax", XSete "al"]
                StrVar -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
                    tell $ [XPush "eax", XPush "edi", XCall "compareStrings"]
                ClassVar typ -> do
                    firstType <- getFirstLevelType s (fromVarType t)
                    offsets <- getOffsets s firstType
                    extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
                    tell $ [XCmp "eax" "edi", XReset "eax", XSete "al"]
        StrVal s -> do
            (jump, str) <- strLabel
            tell $ [XPush "eax", XJmp jump, XLabel str, XString s, XLabel jump, XLea "edi" ("[" ++ str ++ "]"), XPush "edi", XCall "compareStrings"]
        ClassVal t Null -> do
            tell $ [XCmp "eax" "0", XReset "eax", XSete "al"]
        ClassVal t (Content _) -> do
            map <- gets classMap
            case Map.lookup t map of
                Just info -> do
                    let size = totalSize info
                    tell $ [XMov "edx" "eax", XPush (show (size * 4)), XCall "malloc", XAdd "esp" "4"]
                    code <- initAttrs t "eax" (offset info)
                    tell code
            tell $ [XCmp "edx" "eax", XReset "eax", XSete "al"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QCmpLth var val1 val2 : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = " ++ show val1 ++ " < " ++ show val2]
    
    number <- askNumber (fromVar var)

    case val1 of
        IntVal n -> do
            tell $ [XMov "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)

    case val2 of
        IntVal n -> do
            tell $ [XCmp "eax" (show n)]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * localNum l : offsets)
            tell $ [XCmp "eax" "edi"]
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "edi" "edx" "ebp" (4 * paramNum p : offsets)
            tell $ [XCmp "eax" "edi"]

    tell $ [XReset "eax", XSets "al", XReset "ecx", XSeto "cl", XCmp "eax" "ecx", XReset "eax", XSete "al", XXor "al" "1"]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QIf val l : rest) = do
    tell $ [XComment $ "if " ++ show val ++ " then goto " ++ l]
    case val of
        BoolVal b -> do
            tell $ [XMov "eax" (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)
    
    tell $ [XCmp "eax" (show 0), XJne l]
    translateTox86 rest
translateTox86 (QParam p : rest) = do
    tell $ [XComment $ "load parameter " ++ show p]
    case p of
        IntVal n -> do
            tell $ [XPush (show n)]
        BoolVal b -> do
            tell $ [XPush (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
            tell $ [XPush "eax"]
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)
            tell $ [XPush "eax"]
        StrVal s -> do
            (jump, str) <- strLabel
            tell $ [XJmp jump, XLabel str, XString s, XLabel jump, XLea "eax" ("[" ++ str ++ "]"), XPush "eax"]
        ClassVal t Null -> do
            tell $ [XMov "eax" "0", XPush "eax"]
        ClassVal t (Content _) -> do
            map <- gets classMap
            case Map.lookup t map of
                Just info -> do
                    let size = totalSize info
                    tell $ [XPush (show (size * 4)), XCall "malloc", XAdd "esp" "4"]
                    code <- initAttrs t "eax" (offset info)
                    tell code
                    tell $ [XPush "eax"]

    translateTox86 rest
translateTox86 (QCall var f n : rest) = do
    case var of
        VLocal ident t -> do
            if t == VoidVar then do
                tell $ [XComment $ "call " ++ f]
            else do
                tell $ [XComment $ (fromVar var) ++ " = call " ++ f]
        VParam ident t -> do
            if t == VoidVar then do
                tell $ [XComment $ "call " ++ f]
            else do
                tell $ [XComment $ (fromVar var) ++ " = call " ++ f]

    
    number <- askNumber (fromVar var)

    if n == 0 then
        tell $ [XCall f]
    else
        tell $ [XCall f, XAdd "esp" (show (n * 4))]

    case var of
        VLocal ident typ -> do
            if typ == VoidVar then do
                tell $ []
            else do
                firstType <- getFirstLevelType ident (fromVarType typ)
                offsets <- getOffsets ident firstType
                insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            if typ == VoidVar then do
                tell $ []
            else do
                firstType <- getFirstLevelType ident (fromVarType typ)
                offsets <- getOffsets ident firstType
                insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QAttr var val str : rest) = do
    tell $ [XComment $ (fromVar var) ++ " = (" ++ show val ++ ")." ++ str]

    number <- askNumber (fromVar var)

    case val of
        LocVal s t -> do
            l <- getVarNum s
            map <- gets classMap
            case Map.lookup (fromVarType t) map of
                Just info -> do
                    let os = get1offset (offset info) str
                    extractValue "eax" "edi" "ebp" (4 * localNum l : [os])
        ParVal s t -> do
            p <- getVarNum s
            map <- gets classMap
            case Map.lookup (fromVarType t) map of
                Just info -> do
                    let os = get1offset (offset info) str
                    extractValue "eax" "edi" "ebp" (4 * paramNum p : [os])
        ClassVal t Null -> do
            map <- gets classMap
            case Map.lookup t map of
                Just info -> do
                    tell $ [XMov "eax" "0"]
                    let os = get1offset (offset info) str
                    extractValue "eax" "edi" "eax" [os]
        ClassVal t (Content _) -> do
            map <- gets classMap
            case Map.lookup t map of
                Just info -> do
                    let size = totalSize info
                    tell $ [XPush (show (size * 4)), XCall "malloc", XAdd "esp" "4"]
                    code <- initAttrs t "eax" (offset info)
                    tell code
                    let os = get1offset (offset info) str
                    extractValue "eax" "edi" "eax" [os]

    case var of
        VLocal ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            firstType <- getFirstLevelType ident (fromVarType typ)
            offsets <- getOffsets ident firstType
            insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QCallM var val f n : rest) = do
    case var of
        VLocal ident t -> do
            if t == VoidVar then do
                tell $ [XComment $ "callM " ++ f]
            else do
                tell $ [XComment $ (fromVar var) ++ " = callM " ++ f]
        VParam ident t -> do
            if t == VoidVar then do
                tell $ [XComment $ "callM " ++ f]
            else do
                tell $ [XComment $ (fromVar var) ++ " = callM " ++ f]

    number <- askNumber (fromVar var)

    case val of
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)

            map <- gets classMap
            case Map.lookup (fromVarType t) map of
                Just info -> do
                    let os = get1offset (vtableOffset info) f
                    extractValue "eax" "edi" "eax" ([0, os])
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)

            map <- gets classMap
            case Map.lookup (fromVarType t) map of
                Just info -> do
                    let os = get1offset (vtableOffset info) f
                    extractValue "eax" "edi" "eax" ([0, os])
        ClassVal t (Content _) -> do
            map <- gets classMap
            case Map.lookup t map of
                Just info -> do
                    let size = totalSize info
                    tell $ [XPush (show (size * 4)), XCall "malloc", XAdd "esp" "4"]
                    code <- initAttrs t "eax" (offset info)
                    tell code
                    let os = get1offset (vtableOffset info) f
                    extractValue "eax" "edi" "eax" [0, os]
        ClassVal t Null -> do
            map <- gets classMap
            case Map.lookup t map of
                Just info -> do
                    tell $ [XMov "eax" "0"]
                    let os = get1offset (vtableOffset info) f
                    extractValue "eax" "edi" "eax" [0, os]
                    
    if n == 0 then
        tell $ [XCall "eax"]
    else
        tell $ [XCall "eax", XAdd "esp" (show (n * 4))]

    case var of
        VLocal ident typ -> do
            if typ == VoidVar then do
                tell $ []
            else do
                firstType <- getFirstLevelType ident (fromVarType typ)
                offsets <- getOffsets ident firstType
                insertValue "eax" "edi" "ebp" (4 * localNum number : offsets)
            local (Map.insert ident (VarLocal number)) (translateTox86 rest)
        VParam ident typ -> do
            if typ == VoidVar then do
                tell $ []
            else do
                firstType <- getFirstLevelType ident (fromVarType typ)
                offsets <- getOffsets ident firstType
                insertValue "eax" "edi" "ebp" (4 * paramNum number : offsets)
            local (Map.insert ident (VarParam number)) (translateTox86 rest)
translateTox86 (QVRet : rest) = do
    tell $ [XComment "return"]
    locals <- gets locals
    if locals == 0 then do
        tell $ [XLeave, XRet]
    else do
        tell $ [XAdd "esp" (show (locals * 4)), XLeave, XRet]

    translateTox86 rest
translateTox86 (QRet val : rest) = do
    tell $ [XComment "return with value"]

    locals <- gets locals
    
    case val of
        IntVal n -> do
            tell $ [XMov "eax" (show n)]
        BoolVal b -> do
            tell $ [XMov "eax" (show (fromEnum b))]
        LocVal s t -> do
            l <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * localNum l : offsets)
        ParVal s t -> do
            p <- getVarNum s
            firstType <- getFirstLevelType s (fromVarType t)
            offsets <- getOffsets s firstType
            extractValue "eax" "edi" "ebp" (4 * paramNum p : offsets)
        StrVal s -> do
            (jump, str) <- strLabel
            tell $ [XJmp jump, XLabel str, XString s, XLabel jump, XLea "eax" ("[" ++ str ++ "]")]
        ClassVal t Null -> do
            tell $ [XMov "eax" "0"]
        ClassVal t (Content _) -> do
            map <- gets classMap
            case Map.lookup t map of
                Just info -> do
                    let size = totalSize info
                    tell $ [XPush (show (size * 4)), XCall "malloc", XAdd "esp" "4"]
                    code <- initAttrs t "eax" (offset info)
                    tell code

    if locals == 0 then do
        tell $ []
    else do 
        tell $ [XAdd "esp" (show (locals * 4))]

    tell $ [XLeave, XRet]
    translateTox86 rest
translateTox86 (QGoto l : rest) = do
    tell $ [XJmp l]
    translateTox86 rest

getVarAndMethod :: String -> (String, String)
getVarAndMethod str = splitLastDot str []

splitLastDot :: String -> String -> (String, String)
splitLastDot str met =
    case List.last str of
        '.' -> (init str, met)
        c -> splitLastDot (init str) (c : met)

isNotInMap :: String -> Map.Map String Bool -> Int
isNotInMap s map = case Map.lookup s map of
    Nothing -> 1
    _ -> 0

getNumberOfLocals :: QuadCode -> Map.Map String Bool -> Int
getNumberOfLocals [] _ = 0
getNumberOfLocals (QAss (VLocal ident _) _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QAdd (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QAddStr (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QSub (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QMul (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QDiv (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QMod (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QNeg (VLocal ident _) _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QAnd (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QOr (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QNot (VLocal ident _) _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QCmpEq (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QCmpLth (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QCall (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QCallM (VLocal ident _) _ _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (QAttr (VLocal ident _) _ _ : rest) map = (isNotInMap ident map) + getNumberOfLocals rest (Map.insert ident True map)
getNumberOfLocals (_ : rest) map = getNumberOfLocals rest map

modifyEnvX :: [L.Arg] -> Int -> String -> X86Monad Env
modifyEnvX [] _ _ = return Map.empty
modifyEnvX (L.Arg _ t (L.Ident ident) : args) number funname = do
    env <- modifyEnvX args (number + 1) funname
    return (Map.insert (ident ++ "#" ++ funname) (VarParam number) env)

translateFunctions :: QuadCode -> X86Monad ()
translateFunctions [] = return ()
translateFunctions ((QFunc g name args (_ : body)) : rest) = do
    let locals = getNumberOfLocals body Map.empty
    updateLocals locals
    resetUsed

    if g == True then
        tell $ global_ name
    else
        tell $ []

    if locals == 0 then do
        tell $ [XLabel name, XEntry]
    else do
        tell $ [XLabel name, XEntry, XSub "esp" (show (locals * 4))]

    if name == "main" then
        tell $ [XCall ".$make_vtable_reference"]
    else
        tell $ []

    tell $ [XComment "function body"]

    env <- modifyEnvX args 1 name
    local (\_ -> env) (translateTox86 body)
    tell $ [XEmpty]
    translateFunctions rest

makeVTables :: [L.TopDef] -> X86Monad ()
makeVTables [] = return ()
makeVTables (L.ClassDef _ (L.Ident ident) block : rest) = do
    cm <- gets classMap
    case Map.lookup ident cm of
        Just info -> do
            let vtable = vtableOffset info
            let methods = listOfMethods info
            tell $ [XLabel (".$make_" ++ ident ++ "_vtable"), XEntry]
            if length methods == 0 then
                tell $ [XMov "eax" "0"]
            else do
                code <- makeVTable ident methods vtable
                tell $ [XPush (show (4 * length methods)), XCall "malloc", XAdd "esp" "4"] ++ code
            tell $ [XLeave, XRet]
    makeVTables rest
makeVTables (L.CDefExt pos ident _ block : rest) = makeVTables (L.ClassDef pos ident block : rest)
makeVTables (_ : rest) = makeVTables rest

makeVTFunction :: [L.TopDef] -> Int -> X86Monad()
makeVTFunction [] _ = return ()
makeVTFunction (L.ClassDef _ (L.Ident ident) block : rest) n = do
    modify (\st -> st {vtable = Map.insert ident n (vtable st)})
    tell $ [XCall (".$make_" ++ ident ++ "_vtable"), XMov (inBracket (addToReg vtreg (4 * n))) "eax"]
    makeVTFunction rest (n + 1)
makeVTFunction (L.CDefExt pos ident _ block : rest) n = makeVTFunction (L.ClassDef pos ident block : rest) n
makeVTFunction (_ : rest) n = makeVTFunction rest n

makeVTable :: Type -> [(Type, String, L.CStmt)] -> Map.Map String Offset -> X86Monad X86code
makeVTable typ [] map = return []
makeVTable typ ((_, str, _) : rest) map = do
    let (Just n) = Map.lookup str map
    let code = [XLea "edi" (inBracket $ "." ++ typ ++ "$" ++ str), XMov (inBracket (addToReg "eax" n)) "edi"]

    nextCode <- makeVTable typ rest map
    return $ code ++ nextCode

getVTReference :: X86Monad ()
getVTReference = do
    tell $ [XMov "eax" "[ebp + 8]"]
    tell $ [XMul "eax" "4"]
    tell $ [XMov "eax" ("[" ++ vtreg ++ " + eax]")]


translate :: [L.TopDef] -> QuadCode -> X86Monad ()
translate fns code = do
    tell $
        [ XIntelSyntax
        , XExtern "printInt"
        , XExtern "printString"
        , XExtern "error"
        , XExtern "readInt"
        , XExtern "readString"
        , XExtern "concatStrings"
        , XExtern "malloc"
        , XEmpty]
    
    makeVTables fns
    tell $ [XEmpty]

    tell $ [XLabel ".$make_vtable_reference", XEntry]
    cm <- gets classMap
    tell $ [XPush (show $ 4 * Map.size cm), XCall "malloc", XAdd "esp" "4", XMov vtreg "eax"]
    makeVTFunction fns 0
    tell $ [XLeave, XRet, XEmpty]

    tell $ [XLabel ".$get_vtable_reference", XEntry]
    getVTReference
    tell $ [XLeave, XRet, XEmpty]

    translateFunctions code