module TTImp.ProcessDecl

import Core.Context
import Core.TT
import Core.UnifyState

import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessType
import TTImp.Elab.Check

import TTImp.TTImp
import TTImp.Parser
import Parser.Source

import Data.Maybe
import Data.String
import Data.List1
import Data.List
import System.File
import System.Directory

export
getBaseDir : FileName -> DirName
getBaseDir fname = foldl dirconcat "" (init $ split (=='/') fname)
  where dirconcat : String -> String -> String
        dirconcat a e = a ++ e ++ "/"

export
checkUndefineds : {auto c : Ref Ctxt Defs} ->
                 Core ()
checkUndefineds
  = do defs <- get Ctxt
       traverseDefs_ defs (\(n,gdef) => case gdef of
                                      (MkGlobalDef type (PMDef args treeCT _ _))     => pure ()
                                      (MkGlobalDef type (DCon tag arity))        => pure ()
                                      (MkGlobalDef type (TCon x tag arity cons)) => pure ()
                                      (MkGlobalDef type _) => throw $ GenericMsg $ "Entry in context doesn't have a definition: " ++ show n
                          )

export
defaultModulePaths : FileName -> List ModName
defaultModulePaths fname
 = nub [ ""               -- Current dir
       , getBaseDir fname -- Dir of our source file
       ] -- ^ Should eventually include a builtin lib dir too

getImportFName : ModName -> DirName -> FileName
getImportFName mname dir
  = dir ++ mhead
  where replace : Char -> Char -> String -> String
        replace old new = pack . map (\c=>if c==old then new else c) . unpack
        mhead : String
        mhead = replace '.' '/' mname ++ ".tt"

findModule : List DirName -> ModName -> Core FileName
findModule dirs mname
  = do let fnames = map (getImportFName mname) (dirs)
       [fname] <- filterM (coreLift . exists) fnames
         | [] => throw $ GenericMsg $ "No module found for " ++ mname
         | xs => throw $ GenericMsg $ "Multiple modules found for " ++ mname ++ "; " ++ show xs
       pure fname

mutual
  processImport : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {auto s : Ref Stg Stage} ->
                  {auto m : Ref Mods (List ModName)} ->
                  List DirName -> ModName -> Core ()
  processImport dirs mname
    = do processedMods <- get Mods
         -- Have we already processed this module?
         let False = elem mname processedMods
               | _ => pure ()
         put Mods $ mname :: processedMods

         -- Search for module's unique file name
         fname' <- findModule dirs mname
         coreLift $ putStrLn $ "Parsing import of " ++ show fname'

         -- Try processing module
         Right decls <- coreLift $ parseFile fname' (do p <- prog fname'; eoi; pure p)
           | Left err => coreLift $ printLn err
         traverse_ (process dirs) decls
         checkUndefineds

         coreLift $ putStrLn $ "Returning to importer"

  -- Implements process, declared in TTImp.Elab.Check
  process : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Stg Stage} ->
                {auto m : Ref Mods (List ModName)} ->
                List DirName -> ImpDecl -> Core ()
  process _ (IClaim (MkImpTy n ty)) = processType n ty
  process _ (IData ddef) = processData ddef
  process _ (IDef x xs) = processDef x xs
  process dirs (IImport n) = processImport dirs n

TTImp.Elab.Check.processDecl = process
