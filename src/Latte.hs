module Latte where

import Quadcode
import Asemblerx86
import Opts

import System.IO
import System.Process
import System.Environment
import Data.Maybe
import qualified Data.Map as Map
import Data.Bits
import Data.Char
import qualified Data.List as List
import qualified AbsLatte as L

removeEarlierMethods :: [(Type, String, L.CStmt)] -> [(Type, String, L.CStmt)] -> [(Type, String, L.CStmt)]
removeEarlierMethods [] [] = []
removeEarlierMethods f [] = f
removeEarlierMethods [] t = t
removeEarlierMethods (fm@(_, fstr, _) : restf) tmethods =
    case elem fstr (map hlp2 tmethods) of
        False -> fm : removeEarlierMethods restf tmethods
        True -> removeEarlierMethods restf tmethods

removeLaterMethods :: [(Type, String, L.CStmt)] -> [(Type, String, L.CStmt)] -> [(Type, String, L.CStmt)]
removeLaterMethods [] [] = []
removeLaterMethods f [] = f
removeLaterMethods [] t = t
removeLaterMethods fmethods (tm@(_, tstr, _) : restt) =
    case elem tstr (map hlp2 fmethods) of
        False -> removeLaterMethods fmethods restt ++ [tm]
        True -> removeLaterMethods fmethods restt



makeMapFromList :: [(Type, String)] -> Int -> Map.Map String Offset
makeMapFromList [] _ = Map.empty
makeMapFromList ((typ, str) : rest) off = Map.insert str (off * 4) (makeMapFromList rest (off + 1))

checkClassStmt :: [L.CStmt] -> [(Type, String)] -> [(Type, String, L.CStmt)] -> ([(Type, String)], [(Type, String, L.CStmt)])
checkClassStmt [] attrs methods = (attrs, methods)
checkClassStmt (L.CEmpty _ : rest) attrs methods = checkClassStmt rest attrs methods
checkClassStmt (L.CDecl _ _ [] : rest) attrs methods = checkClassStmt rest attrs methods
checkClassStmt (L.CDecl pos t ((L.CItem pos2 (L.Ident ident)) : items) : rest) attrs methods = checkClassStmt (L.CDecl pos t items : rest) (attrs ++ [(lStrType t, ident)]) methods
checkClassStmt (stmt@(L.CMethod _ t (L.Ident ident) _ _) : rest) attrs methods = checkClassStmt rest attrs (methods ++ [(lStrType t, ident, stmt)])

getClassInfoMap :: [L.TopDef] -> ClassInfoMap -> ClassInfoMap
getClassInfoMap [] map = map
getClassInfoMap (L.ClassDef _ (L.Ident ident) (L.CBlock _ stmts) : rest) cimap = 
    let (attrs, methods) = checkClassStmt stmts [] [] in
        let info = ClassInfo {totalSize = length attrs + 1, offset = makeMapFromList attrs 1, vtableOffset = makeMapFromList (map hlp12 methods) 0, listOfAttrs = attrs, listOfMethods = methods} in
            getClassInfoMap rest (Map.insert ident info cimap)
getClassInfoMap (cur@(L.CDefExt _ (L.Ident ident1) (L.Ident ident2) (L.CBlock _ stmts)) : rest) cimap =
    case Map.lookup ident2 cimap of
        Nothing -> getClassInfoMap (rest ++ [cur]) cimap
        Just infof ->
            let (attrs, methods) = checkClassStmt stmts [] [] in
                let info = ClassInfo {totalSize = length attrs + totalSize infof, offset = makeMapFromList (listOfAttrs infof ++ attrs) 1, vtableOffset = makeMapFromList (map hlp12 (removeLaterMethods (listOfMethods infof) methods)) 0, listOfAttrs = listOfAttrs infof ++ attrs, listOfMethods = removeEarlierMethods (listOfMethods infof) methods} in
                    getClassInfoMap rest (Map.insert ident1 info cimap)
getClassInfoMap (_ : rest) map = getClassInfoMap rest map

runProgram :: L.Program -> String -> IO ()
runProgram (L.Program _ fns) path = do

    let classInfoMap = getClassInfoMap fns Map.empty
    --hPutStrLn stderr $ show classInfoMap

    (quadret, quadcode) <- runQuadMonad Map.empty (initQState fns classInfoMap) (genQuadCode fns)
    case quadret of
        Left err -> do
            hPutStrLn stderr $ "ERROR\nruntime error (quadcode) " ++ path ++ ":" ++ err
        Right (_, st)  -> do
            --hPutStrLn stderr $ "QuadCode:\n" ++ show quadcode

            optCode <- optimize quadcode
            --hPutStrLn stderr $ "Optimized quadcode:\n" ++ show optCode

            (ret, code) <- runX86Monad Map.empty (initXState classInfoMap (varTypeMap st)) (translate fns optCode)
            case ret of
                Left err -> do
                    hPutStrLn stderr $ "ERROR\nruntime error (x86) " ++ path ++ ":" ++ err
                Right _ -> do
                    --hPutStrLn stderr $ "x86 code:\n" ++ show code
                    hPutStrLn stderr $ "OK"
                    let file = take (length path - 4) path
                    let name = afterLastSlash file [] where
                        afterLastSlash :: String -> String -> String
                        afterLastSlash [] acc = acc
                        afterLastSlash ('/' : xs) acc = afterLastSlash xs []
                        afterLastSlash (h : xs) acc = afterLastSlash xs (acc ++ [h])
                    let dir = take (length file - length name) file
                    let dots = file ++ ".s"

                    filepath <- getExecutablePath
                    let runtimepath = take (length filepath - 9) filepath ++ "/lib/runtime.o"

                    writeFile dots (show code)

                    callCommand $ "i686-linux-gnu-gcc -o " ++ file ++ " -m32 -no-pie -g " ++ dots ++  " " ++ runtimepath