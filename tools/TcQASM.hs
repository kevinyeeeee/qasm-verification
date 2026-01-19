module Main (main) where

import System.Environment (getArgs)

import qualified Feynman.Frontend.OpenQASM3.Chatty as QASM3Chatty
import qualified Feynman.Frontend.OpenQASM3.Parser as QASM3Parser
import Feynman.Frontend.OpenQASM3.Core
import Feynman.Frontend.OpenQASM3.TypeCheck
import Feynman.Frontend.OpenQASM3.Simulation
import Feynman.Timing

tcFile :: String -> IO ()
tcFile src = case QASM3Parser.parseString src of
    QASM3Chatty.Failure _ err -> error ("Parse error: " ++ err)
    QASM3Chatty.Value _ qasm -> case translateProg qasm of
      Left error -> printErrors [error]
      Right prog -> case tcQasm prog of
        Left errors -> printErrors errors
        Right prog  -> do
          env <- simProg prog
          return $ env `seq` ()

parseArgs :: [String] -> IO ()
parseArgs (f:[]) | ((drop (length f - 5) f) == ".qasm") = readFile f >>= tcFile
parseArgs _ = putStrLn "Usage: tcqasm <filename>.qasm"

main :: IO ()
main = getArgs >>= parseArgs
