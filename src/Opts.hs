module Opts where

import Quadcode
import qualified Data.Map as Map
import Data.Bits
import Data.Char
import qualified Data.List as List
import qualified AbsLatte as L

import System.IO
import Control.Monad.State

debugO :: String -> LcseMonad ()
debugO str = liftIO $ hPutStrLn stderr $ str

type LcseMonad a = StateT LState IO a
runLcseMonad :: LState -> LcseMonad a -> IO (a, LState)
runLcseMonad lst ev = runStateT ev lst

type CopyMonad a = IO a
runCopyMonad :: CopyMonad a -> IO a
runCopyMonad ev = ev

data LState = LState {lcsecounter :: Int}

lcseLabel :: LcseMonad String
lcseLabel = state (\st -> ("lcse##_" ++ show (lcsecounter st), st {lcsecounter = lcsecounter st + 1}))

noDot :: String -> Bool
noDot str = not (elem '.' str)

isNotMemoryAccess :: Val -> Bool
isNotMemoryAccess (IntVal _) = True
isNotMemoryAccess (BoolVal _) = True
isNotMemoryAccess (StrVal _) = False
isNotMemoryAccess (ClassVal _ _) = False
isNotMemoryAccess (ParVal str _) = noDot str
isNotMemoryAccess (LocVal str _) = noDot str

varToVal :: Var -> Val
varToVal (VLocal str t) = LocVal str t
varToVal (VParam str t) = ParVal str t

varOfInstr :: QuadInstr -> Var
varOfInstr (QLabel _) = VNothing
varOfInstr (QAss var _) = var
varOfInstr (QAdd var _ _) = var
varOfInstr (QAddStr var _ _) = var
varOfInstr (QSub var _ _) = var
varOfInstr (QMul var _ _) = var
varOfInstr (QDiv var _ _) = var
varOfInstr (QMod var _ _) = var
varOfInstr (QAttr var _ _) = var
varOfInstr (QNeg var _) = var
varOfInstr (QAnd var _ _) = var
varOfInstr (QOr var _ _) = var
varOfInstr (QNot var _) = var
varOfInstr (QCmpEq var _ _) = var
varOfInstr (QCmpLth var _ _) = var
varOfInstr (QIf _ _) = VNothing
varOfInstr (QParam _) = VNothing
varOfInstr (QCall var _ _) = var
varOfInstr (QCallM var _ _ _) = var
varOfInstr (QVRet) = VNothing
varOfInstr (QRet _) = VNothing
varOfInstr (QFunc _ _ _ _) = VNothing
varOfInstr (QGoto _) = VNothing

valOfInstr1 :: QuadInstr -> Val
valOfInstr1 (QAdd _ val1 _) = val1
valOfInstr1 (QSub _ val1 _) = val1
valOfInstr1 (QMul _ val1 _) = val1
valOfInstr1 (QDiv _ val1 _) = val1
valOfInstr1 (QMod _ val1 _) = val1
valOfInstr1 (QNeg _ val1) = val1
valOfInstr1 (QAnd _ val1 _) = val1
valOfInstr1 (QOr _ val1 _) = val1
valOfInstr1 (QNot _ val1) = val1
valOfInstr1 (QCmpEq _ val1 _) = val1
valOfInstr1 (QCmpLth _ val1 _) = val1

valOfInstr2 :: QuadInstr -> Val
valOfInstr2 (QAdd _ _ val2) = val2
valOfInstr2 (QSub _ _ val2) = val2
valOfInstr2 (QMul _ _ val2) = val2
valOfInstr2 (QDiv _ _ val2) = val2
valOfInstr2 (QMod _ _ val2) = val2
valOfInstr2 (QNeg _ val1) = LocVal "%%%$$$)(*!&@^$" IntVar
valOfInstr2 (QAnd _ _ val2) = val2
valOfInstr2 (QOr _ _ val2) = val2
valOfInstr2 (QNot _ val1) = LocVal "%%%$$$)(*!&@^$" IntVar
valOfInstr2 (QCmpEq _ _ val2) = val2
valOfInstr2 (QCmpLth _ _ val2) = val2

typeOfVar :: Var -> VarType
typeOfVar (VLocal _ t) = t
typeOfVar (VParam _ t) = t

isNotMemoryAccessVar :: Var -> Bool
isNotMemoryAccessVar (VLocal str _) = noDot str
isNotMemoryAccessVar (VParam str _) = noDot str

findRHS :: QuadInstr -> Bool -> Int -> QuadCode -> QuadCode -> QuadCode -> LcseMonad (Int, QuadCode, QuadCode)
findRHS _ b n opt cur [] = return (n, opt, cur)
findRHS og@(QAdd var val1 val2) b n opt cur (stmt@(QAdd varn val1n val2n) : rest) =
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QSub var val1 val2) b n opt cur (stmt@(QSub varn val1n val2n) : rest) =
    if (val1 == val1n && val2 == val2n) then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QMul var val1 val2) b n opt cur (stmt@(QMul varn val1n val2n) : rest) =
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QDiv var val1 val2) b n opt cur (stmt@(QDiv varn val1n val2n) : rest) =
    if (val1 == val1n && val2 == val2n) then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QMod var val1 val2) b n opt cur (stmt@(QMod varn val1n val2n) : rest) =
    if (val1 == val1n && val2 == val2n) then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QNeg var val1) b n opt cur (stmt@(QNeg varn val1n) : rest) =
    if val1 == val1n then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QAnd var val1 val2) b n opt cur (stmt@(QAnd varn val1n val2n) : rest) =
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QOr var val1 val2) b n opt cur (stmt@(QOr varn val1n val2n) : rest) =
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QNot var val1) b n opt cur (stmt@(QNot varn val1n) : rest) =
    if val1 == val1n then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QCmpEq var val1 val2) b n opt cur (stmt@(QCmpEq varn val1n val2n) : rest) =
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS og@(QCmpLth var val1 val2) b n opt cur (stmt@(QCmpLth varn val1n val2n) : rest) =
    if (val1 == val1n && val2 == val2n) then do
        if var == varn then
            findRHS og True n (opt ++ cur ++ [stmt]) [] rest
        else
            findRHS og b (if b == False then n + 1 else n) (opt ++ cur ++ [stmt]) [] rest
    else
        findRHS og b (if b == False then n + 1 else n) opt (cur ++ [stmt]) rest
findRHS stmt1 b n opt cur (stmt2 : rest) = do
    if varOfInstr stmt2 == VNothing then
        findRHS stmt1 b (if b == False then n + 1 else n) opt (cur ++ [stmt2]) rest
    else
        if valOfInstr1 stmt1 == varToVal (varOfInstr stmt2) || (valOfInstr2 stmt1 == varToVal (varOfInstr stmt2)) then
            return (n + 1, opt, cur ++ [stmt2] ++ rest)
        else do
            if varOfInstr stmt1 == varOfInstr stmt2 then
                findRHS stmt1 True n opt (cur ++ [stmt2]) rest
            else
                findRHS stmt1 b (if b == False then n + 1 else n) opt (cur ++ [stmt2]) rest 

replaceInstrucitons :: QuadInstr -> QuadCode -> QuadCode -> Val -> LcseMonad QuadCode
replaceInstrucitons _ [] res _ = return res
replaceInstrucitons og@(QAdd var val1 val2) (stmt@(QAdd varn val1n val2n) : rest) res val = do
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QSub var val1 val2) (stmt@(QSub varn val1n val2n) : rest) res val = do
    if (val1 == val1n && val2 == val2n) then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QMul var val1 val2) (stmt@(QMul varn val1n val2n) : rest) res val = do
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QDiv var val1 val2) (stmt@(QDiv varn val1n val2n) : rest) res val = do
    if (val1 == val1n && val2 == val2n) then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QMod var val1 val2) (stmt@(QMod varn val1n val2n) : rest) res val = do
    if (val1 == val1n && val2 == val2n) then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QNeg var val1) (stmt@(QNeg varn val1n) : rest) res val = do
    if val1 == val1n then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QAnd var val1 val2) (stmt@(QAnd varn val1n val2n) : rest) res val = do
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QOr var val1 val2) (stmt@(QOr varn val1n val2n) : rest) res val = do
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QNot var val1) (stmt@(QNot varn val1n) : rest) res val = do
    if val1 == val1n then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QCmpEq var val1 val2) (stmt@(QCmpEq varn val1n val2n) : rest) res val = do
    if (val1 == val1n && val2 == val2n) || (val1 == val2n && val2 == val1n) then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og@(QCmpLth var val1 val2) (stmt@(QCmpLth varn val1n val2n) : rest) res val = do
    if (val1 == val1n && val2 == val2n) then
        replaceInstrucitons og rest (res ++ [QAss varn val]) val
    else
        replaceInstrucitons og rest (res ++ [stmt]) val
replaceInstrucitons og (stmt : rest) res val = replaceInstrucitons og rest (res ++ [stmt]) val

replaceVar :: QuadInstr -> Var -> QuadInstr
replaceVar (QAdd _ val1 val2) var = QAdd var val1 val2
replaceVar (QSub _ val1 val2) var = QSub var val1 val2
replaceVar (QMul _ val1 val2) var = QMul var val1 val2
replaceVar (QDiv _ val1 val2) var = QDiv var val1 val2
replaceVar (QMod _ val1 val2) var = QMod var val1 val2
replaceVar (QNeg _ val1) var = QNeg var val1
replaceVar (QAnd _ val1 val2) var = QAnd var val1 val2
replaceVar (QOr _ val1 val2) var = QOr var val1 val2
replaceVar (QNot _ val1) var = QNot var val1
replaceVar (QCmpEq _ val1 val2) var = QCmpEq var val1 val2
replaceVar (QCmpLth _ val1 val2) var = QCmpLth var val1 val2

lcseopt2 :: QuadInstr -> QuadCode -> QuadCode -> LcseMonad (QuadCode)
lcseopt2 stmt rest res = do
    let var = varOfInstr stmt
    let val1 = valOfInstr1 stmt
    let val2 = valOfInstr2 stmt
    let acc1 = isNotMemoryAccess val1
    let acc2 = isNotMemoryAccess val2
    case and [acc1, acc2] of
        False -> lcseopt rest (res ++ [stmt])
        True -> do
            (varrange, toOpt, tooFar) <- findRHS stmt False 1 [] [] rest
            if length toOpt == 0 then
                lcseopt rest (res ++ [stmt])
            else do
                if isNotMemoryAccessVar var && varrange > length toOpt then do
                    opted <- replaceInstrucitons stmt toOpt [] (varToVal var)
                    lcseopt (opted ++ tooFar) (res ++ [stmt])
                else do
                    optlabel <- lcseLabel
                    opted <- replaceInstrucitons stmt toOpt [] (LocVal optlabel (typeOfVar var))
                    let newVar = VLocal optlabel (typeOfVar var)
                    lcseopt (opted ++ tooFar) (res ++ [replaceVar stmt newVar, QAss var (LocVal optlabel (typeOfVar var))])

lcseopt :: QuadCode -> QuadCode -> LcseMonad (QuadCode)
lcseopt [] res = return res
lcseopt (stmt@(QAdd var val1 val2) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QSub var val1 val2) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QMul var val1 val2) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QDiv var val1 val2) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QMod var val1 val2) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QNeg var val1) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QAnd var val1 val2) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QOr var val1 val2) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QNot var val1) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QCmpEq var val1 val2) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt@(QCmpLth var val1 val2) : rest) res = lcseopt2 stmt rest res
lcseopt (stmt : rest) res = lcseopt rest (res ++ [stmt])

lcseblock :: QuadCode -> LcseMonad (QuadCode)
lcseblock [] = return []
lcseblock block = do
    res <- lcseopt block []
    return res

lcsefunction :: QuadCode -> QuadCode -> LcseMonad (QuadCode)
lcsefunction [] block = do
    res <- lcseblock block
    return res
lcsefunction (QLabel label : rest) block = do
    res <- lcseblock block
    next <- lcsefunction rest [QLabel label]
    return $ res ++ next
lcsefunction (QGoto label : rest) block = do
    if take 5 label == ".jump" then do
        lcsefunction rest (block ++ [QGoto label])
    else do
        res <- lcseblock (block ++ [QGoto label])
        next <- lcsefunction rest []
        return $ res ++ next
lcsefunction (stmt : rest) block = lcsefunction rest (block ++ [stmt])

lcse :: QuadCode -> LcseMonad (QuadCode)
lcse [] = return []
lcse ((QFunc g name args (a : body)) : rest) = do
    funcode <- lcsefunction body []
    next <- lcse rest
    return $ (QFunc g name args (a : funcode)) : next

optimize :: QuadCode -> IO (QuadCode)
optimize code = do
    (lcsecode, _) <- runLcseMonad (LState {lcsecounter = 0}) (lcse code)
    return lcsecode