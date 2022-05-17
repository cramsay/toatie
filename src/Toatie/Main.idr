module Toatie.Main

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.CaseTree
import Core.Extraction
import Core.Context
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Netlist

import TTImp.Elab.Term

import TTImp.Parser
import TTImp.ProcessDecl
import TTImp.ProcessData
import TTImp.TTImp
import TTImp.Elab.Check
import Utils.Bits

import Parser.Source

import System
import System.File
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.String

-- Command line options
data FOpt : Type where
  FTypeCheckOnly : FOpt
  FNetlist : String -> FOpt
  FOutDir : String -> FOpt

Eq FOpt where
  FTypeCheckOnly == FTypeCheckOnly = True
  FNetlist n == FNetlist n' = n==n'
  _ == _ = False

parseFOpt : String -> IO FOpt
parseFOpt "-fTypeCheckOnly" = pure FTypeCheckOnly
parseFOpt s = do let False = isPrefixOf "-fNetlist=" s
                       | True => pure $ FNetlist (strSubstr 10 (strLength s) s)
                 let False = isPrefixOf "-fOutDir=" s
                       | True => pure $ FOutDir  (strSubstr 9  (strLength s) s)
                 putStrLn $ "Unrecognised option: " ++ s
                 exitFailure

containsFNetlist : List FOpt -> Maybe String
containsFNetlist ((FNetlist n)::os) = Just n
containsFNetlist (o::os) = containsFNetlist os
containsFNetlist [] = Nothing

containsFOutDir : List FOpt -> Maybe String
containsFOutDir ((FOutDir n)::os) = Just n
containsFOutDir (o::os) = containsFOutDir os
containsFOutDir [] = Nothing

data ReplCmd : Type where
  RC_BitRep : ReplCmd
  RC_CompileDef : ReplCmd
  RC_Netlist : ReplCmd

parseReplCmd : String -> Maybe ReplCmd
parseReplCmd ":BitRep" = Just RC_BitRep
parseReplCmd ":CompileDef"   = Just RC_CompileDef
parseReplCmd ":Netlist" = Just RC_Netlist
parseReplCmd _ = Nothing

repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST UState} ->
       {auto s : Ref Stg Stage} ->
       Core ()
repl = do coreLift $ putStr "> "
          inp <- coreLift getLine
          let (cmd, inp') = break (' '==) inp
          case parseReplCmd cmd of

            Just RC_BitRep =>
              do let Right ttexp = runParser Nothing inp' (expr "(input)" init)
                     | Left err => do coreLift $ printLn err
                                      repl
                 (tm, _) <- checkTerm [] ttexp Nothing
                 defs <- get Ctxt
                 tm <- normalise defs [] tm
                 coreLift $ putStrLn $ "Type : " ++ show tm
                 dcons <- dataConsForType [] tm
                 coreLift $ putStrLn $ "Possible data constructors:\n" ++ unlines (map show dcons)
                 w_tag <- tyTagWidth [] tm
                 coreLift $ putStrLn $ "Tag width: " ++ show w_tag
                 w_field <- tyFieldWidth [] tm
                 coreLift $ putStrLn $ "Field width: " ++ show w_field
                 repl

            Just RC_CompileDef =>
              do let Right (IVar name) = runParser Nothing inp' (expr "(input)" init)
                       | _ => do coreLift $ printLn "Couldn't parse input as a name"
                 defs <- get Ctxt
                 extDefs <- extractCtxt defs
                 put Ctxt extDefs
                 compileAndInline [name]
                 extDefs <- get Ctxt
                 Just gdef <- lookupDef name extDefs
                   | Nothing => coreLift $ putStrLn $ "Couldn't find context entry for " ++ show name
                 let Just comp = compexpr gdef
                       | Nothing => coreLift $ putStrLn $ "Couldn't find compiled expression for " ++ show name
                 coreLift $ putStrLn $ "Compiled to: " ++ show comp
                 put Ctxt defs
                 repl

            Just RC_Netlist =>
              do let Right (IVar name) = runParser Nothing inp' (expr "(input)" init)
                       | _ => do coreLift $ printLn "Couldn't parse input as a name"
                 defs <- get Ctxt
                 extDefs <- extractCtxt defs
                 put Ctxt extDefs
                 compileAndInline [name]
                 extDefs <- get Ctxt
                 Just gdef <- lookupDef name extDefs
                   | Nothing => coreLift $ putStrLn $ "Couldn't find context entry for " ++ show name
                 let Just comp = compexpr gdef
                       | Nothing => coreLift $ putStrLn $ "Couldn't find compiled expression for " ++ show name
                 nl <- genNetlist name
                 coreLift $ putStrLn $ "Compiled to: " ++ show nl
                 put Ctxt defs
                 repl

          -- Not a command, so just interpret it as a term
            Nothing =>
              do let Right ttexp = runParser Nothing inp (expr "(input)" init)
                     | Left err => do coreLift $ printLn err
                                      repl
                 (tm, ty) <- checkTerm [] ttexp Nothing
                 coreLift $ putStrLn $ "Checked: " ++ show tm
                 defs <- get Ctxt
                 coreLift $ putStrLn $ "Type: " ++ show !(normalise defs [] !(getTerm ty))
                 nf <- normalise defs [] tm
                 coreLift $ putStrLn $ "Evaluated: " ++ show nf

                 -- Show extracted versions too
                 coreLift $ putStrLn $ "Extraction Evaluated: " ++ show (extraction nf)

                 repl

runMain : List FOpt -> FileName -> List ImpDecl -> Core ()
runMain fopts fname decls
    = do c <- newRef Ctxt !initDefs
         u <- newRef UST initUState
         s <- newRef Stg (the Stage 0)
         m <- newRef Mods []
         let dirs = defaultModulePaths fname
         traverse_ (processDecl dirs) decls
         checkUndefineds

         let Nothing = containsFNetlist fopts
               | Just funname =>
                   do defs <- get Ctxt
                      extDefs <- extractCtxt defs
                      put Ctxt extDefs
                      compileAndInline [UN funname]
                      nl <- genNetlist $ UN funname
                      let outfile = fromMaybe "" (containsFOutDir fopts) ++ "/" ++ funname ++ ".vhd"
                      res <- coreLift $ writeFile outfile (show nl)
                      case res of
                        Left err => throw $ GenericMsg $ "Failed to write netlist file: " ++ show err
                        Right () => coreLift $ putStrLn $ "Compiled netlist for " ++ show funname

         when (not $ FTypeCheckOnly `elem` fopts)
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
main = do (_ :: args) <- getArgs
             | _ => putStrLn "Usage: tinyidris <filename>"
          let (fname :: args) = reverse args
             | _ => putStrLn "Usage: tinyidris <filename>"

          fopts <- traverse parseFOpt args

          Right decls <- parseFile fname (do p <- prog fname; eoi; pure p)
              | Left err => printLn err
          putStrLn banner
          coreRun (runMain fopts fname decls)
                  (\err => do printLn err
                              exitFailure)
                  pure
