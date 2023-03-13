module Main where

import System.IO
import System.Environment
import System.Exit

import LexLatte
import ParLatte
import SkelLatte
import PrintLatte
import AbsLatte as L

import qualified TypeChecker
import qualified Latte

main :: IO ()
main = do
    args <- getArgs
    case args of
        [path] -> readFile path >>= run path
        []     -> putStrLn "Reading from STDIN" >> getContents >>= run ""
        _      -> die "Usage:\nreading from file - ./latte path_to_file\nreading from STDIN - ./latte"

run :: String -> String -> IO ()
run path input = do
    case pProgram $ myLexer input of
        Left err   -> do
            hPutStrLn stderr err
            exitFailure
        Right prog -> do
            ret <- TypeChecker.runProgram prog
            case ret of
                Left errT -> do
                    hPutStrLn stderr $ "ERROR\nType check error " ++ path ++ ":" ++ errT
                    exitFailure
                Right _   -> do
                    Latte.runProgram prog path