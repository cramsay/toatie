module Idris.Main

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState

import TTImp.Elab.Term

import TTImp.Parser
import TTImp.ProcessDecl
import TTImp.TTImp

import Parser.Source

import System
import Data.List

repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       Core ()
repl = do coreLift $ putStr "> "
          inp <- coreLift getLine
          let Right ttexp = runParser Nothing inp (expr "(input)" init)
              | Left err => do coreLift $ printLn err
                               repl
          (tm, ty) <- checkTerm [] ttexp Nothing
          coreLift $ putStrLn $ "Checked: " ++ show tm
          defs <- get Ctxt
          coreLift $ putStrLn $ "Type: " ++ show !(normalise defs [] !(getTerm ty))
          nf <- normalise defs [] tm
          coreLift $ putStrLn $ "Evaluated: " ++ show nf
          repl

runMain : List ImpDecl -> Core ()
runMain decls
    = do c <- newRef Ctxt !initDefs
         u <- newRef UST initUState
         traverse_ processDecl decls
         repl

banner : String
banner = """
  \n
  "Y888888888888888888888888888888888888888888888888888888888Y"
    "Y88888888888888888888888888888888888888888888888888888Y"
     888                                                 888
     888   888                     888    d8b            888
     888   888                     888    Y8P            888
     888   888                     888                   888
     888   888888 .d88b.   8888b.  888888 888  .d88b.    888
     888   888   d88""88b     "88b 888    888 d8P  Y8b   888
     888   888   888  888 .d888888 888    888 88888888   888
     888   Y88b. Y88..88P 888  888 Y88b.  888 Y8b.       888
   .e888e   "Y888 "Y88P"  "Y888888  "Y888 888  "Y8888   e888e.
  \n
  """

main : IO ()
main = do [_, fname] <- getArgs
              | _ => putStrLn "Usage: tinyidris <filename>"
          Right decls <- parseFile fname (do p <- prog fname; eoi; pure p)
              | Left err => printLn err
          putStrLn banner
          coreRun (runMain decls)
                  (\err => printLn err)
                  pure
