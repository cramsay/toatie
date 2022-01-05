module TTImp.ProcessDecl

import Core.Context
import Core.TT
import Core.UnifyState

import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessType

import TTImp.TTImp
import TTImp.Parser
import Parser.Source

import Data.Maybe
import Data.String
import Data.List1
import System.File
import System.Directory

export
data Mods : Type where

public export
DirName : Type
DirName = FileName

public export
ModName : Type
ModName = FileName

export
getBaseDir : FileName -> DirName
getBaseDir fname = foldl dirconcat "" (init $ split (=='/') fname)
  where dirconcat : String -> String -> String
        dirconcat a e = a ++ e ++ "/"

export
defaultModulePaths : FileName -> Core (List ModName)
defaultModulePaths fname
 = do cwd <- coreLift $ currentDir
      let workingDirs = fromMaybe [] (map (\s => (s++"/")::[]) cwd)
      let dirs = workingDirs ++
                 [getBaseDir fname]
                 -- ^ Should eventually include a builtin lib dir too
      pure dirs

getImportFName : ModName -> DirName -> FileName
getImportFName mname dir
  = dir ++ mhead
  where replace : Char -> Char -> String -> String
        replace old new = pack . map (\c=>if c==old then new else c) . unpack
        mhead : String
        mhead = replace '.' '/' mname ++ ".tidr"

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
         traverse_ (processDecl dirs) decls

         coreLift $ putStrLn $ "Returning to importer"

  export
  processDecl : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Stg Stage} ->
                {auto m : Ref Mods (List ModName)} ->
                List DirName -> ImpDecl -> Core ()
  processDecl _ (IClaim (MkImpTy n ty)) = processType n ty
  processDecl _ (IData ddef) = processData ddef
  processDecl _ (IDef x xs) = processDef x xs
  processDecl dirs (IImport n) = processImport dirs n
