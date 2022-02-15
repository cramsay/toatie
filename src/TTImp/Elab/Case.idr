module TTImp.Elab.Case

import Core.CaseTree
import Core.Context
import Core.Coverage
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value
import Core.Unify

import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.Impossible
import TTImp.ProcessDef

import Data.Either
import Data.Maybe
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String
import Debug.Trace

lowerFirst : String -> Bool
lowerFirst "" = False
lowerFirst str = isLower $ assert_total $ prim__strHead str

getUnique : List String -> String -> String
getUnique xs x = if x `elem` xs then getUnique xs (x ++ "'") else x

findBindableNames : (arg : Bool) -> List Name -> (used : List String) ->
                    RawImp -> List (String, String)
findBindableNames True env used (IVar nm@(UN n))   --TODO how about MN for implicits etc?
  = if not (nm `elem` env) && lowerFirst n
       then [(n, getUnique used n)]
       else []
findBindableNames arg env used (IPi i mn argTy retTy)
  = let env' = case mn of
                 Nothing => env
                 Just n => n :: env in
    findBindableNames True env used argTy ++
    findBindableNames True env' used retTy
findBindableNames arg env used (ILam i mn argTy scope)
  = let env' = case mn of
                 Nothing => env
                 Just n => n :: env in
    findBindableNames True env used argTy ++
    findBindableNames True env' used scope
findBindableNames arg env used (IPatvar n ty scope)
  = let env' = n :: env in
    findBindableNames arg env used ty ++
    findBindableNames arg env' used scope
findBindableNames arg env used (IApp i f a)
  = findBindableNames False env used f ++ findBindableNames True env used a
findBindableNames arg env used (IMustUnify x) = findBindableNames arg env used x
findBindableNames arg env used (IQuote x)     = findBindableNames arg env used x
findBindableNames arg env used (ICode x)      = findBindableNames arg env used x
findBindableNames arg env used (IEval x)      = findBindableNames arg env used x
findBindableNames arg env used (IEscape x)    = findBindableNames arg env used x
findBindableNames arg env used tm = []

mutual
  substNames : List Name -> List (Name, RawImp) -> RawImp -> RawImp
  substNames bound ps (IVar n)
    = if not (n `elem` bound)
         then case lookup n ps of
                   Just t => t
                   Nothing => IVar n
         else IVar n
  substNames bound ps (ILet n margTy argVal scope)
    = let bound' = n :: bound in
      ILet n (map (substNames bound ps) margTy)
             (     substNames bound ps argVal)
             (     substNames bound' ps scope)
  substNames bound ps (IPi i mn argTy retTy)
    = let bound' = maybe bound (\n=>n::bound) mn in
      IPi i mn (substNames bound  ps argTy)
               (substNames bound' ps argTy)
  substNames bound ps (ILam i mn argTy scope)
    = let bound' = maybe bound (\n=>n::bound) mn in
      ILam i mn (substNames bound  ps argTy)
                (substNames bound' ps argTy)
  substNames bound ps (IApp i f a) = IApp i (substNames bound ps f)
                                            (substNames bound ps a)
  substNames bound ps (ICase scr scrty xs)
    = ICase (substNames bound ps scr) (substNames bound ps scrty)
            (map (substNamesClause bound ps) xs)
  substNames bound ps (IMustUnify x) = IMustUnify (substNames bound ps x)
  substNames bound ps Implicit = Implicit
  substNames bound ps IType = IType
  substNames bound ps (IQuote x) = IQuote (substNames bound ps x)
  substNames bound ps (ICode x) = ICode (substNames bound ps x)
  substNames bound ps (IEval x) = IEval (substNames bound ps x)
  substNames bound ps (IEscape x) = IEscape (substNames bound ps x)
  substNames bound ps (IPatvar n ty scope)
    = let bound' = n :: bound in
      IPatvar n (substNames bound ps ty)
                (substNames bound' ps scope)
  substNames bound ps tm = tm

  substNamesClause : List Name -> List (Name, RawImp) -> ImpClause -> ImpClause
  substNamesClause bound ps (ImpossibleClause lhs) = ImpossibleClause (substNames bound [] lhs)
  substNamesClause bound ps (PatClause lhs rhs)
    = let bound' = map UN (map snd (findBindableNames True bound [] lhs))
                    ++ bound in
      PatClause (substNames [] [] lhs) --TODO Still the case for our explicit patvars?
                (substNames bound' ps rhs)

findScrutinee : {vs : _} ->
                Env Term vs -> RawImp -> Maybe (Var vs)
findScrutinee {vs = n' :: _} (b :: bs) (IVar n)
  = if n' == n && not (isLet b)
       then Just (MkVar First)
       else do MkVar p <- findScrutinee bs (IVar n)
               Just (MkVar (Later p))
findScrutinee _ _ = Nothing

getNestData : (Name, (Maybe Name, List (Var vars), a)) ->
              (Name, Maybe Name, List (Var vars))
getNestData (n, (mn, enames, _)) = (n, mn, enames)

lamsToPisEnv : Env Term vars -> Env Term vars
lamsToPisEnv [] = []
lamsToPisEnv ((Lam s i ty) :: bs) = Pi s i ty :: lamsToPisEnv bs
lamsToPisEnv (b :: bs) = b :: lamsToPisEnv bs

-- FIXME how do we order arguments / pattern vectors such that they form a telescope?
--       don't want to have Vect n a before pattern for n or a!

export
caseBlock : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Stg Stage} ->
            {auto u : Ref UST UState} ->
            ElabMode ->
            Env Term vars ->
            RawImp -> -- original scrutinee
            Term vars -> -- checked scrutinee
            Term vars -> -- its type
            List ImpClause -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
caseBlock {vars} mode env scr scrtm scrty alts expected
  = do scrn <- genName "scr"
       casen <- genName "case" -- TODO would be good to base this on the parent function name

       -- if the scrutinee is ones of the arguments in 'env' we should
       -- split on that, rather than adding it as a new argument
       let splitOn = findScrutinee env scr

       caseretty <- case expected of
         Just ty => getTerm ty
         _ => do nmty <- genName "caseTy"
                 newMeta env nmty TType Hole

       -- TODO what about staging of env if we've moved stages since binding them?

       s <- get Stg
       let casefnty = abstractEnvType env
                                      (maybe (Bind scrn (Pi s Explicit scrty) (weaken caseretty))
                                             (const caseretty)
                                             splitOn)

       addDef casen $ MkGlobalDef casefnty None
       let caseRef : Term vars = Ref Func casen
       let applyEnv = applyTo caseRef env
       let appTm : Term vars
                 = maybe (App AExplicit applyEnv scrtm)
                         (const applyEnv)
                         splitOn

       let alts' = map (updateClause casen casefnty splitOn env) alts

       processDef casen alts'

       pure (appTm, gnf env caseretty)
  where

  getBindName : Int -> Name -> List Name -> (Name, Name)
  getBindName idx n@(UN un) vs
    = if n `elem` vs then (n, MN un idx) else (n, n)
  getBindName idx n vs
    = if n `elem` vs then (n, MN "_cn" idx) else (n, n)

  -- Returns a list of names that nestednames should be applied to, mapped
  -- to what the name has become in the case block, and a list of terms for
  -- the LHS of the case to be applied to.
  addEnv : {vs : _} ->
           Int -> Env Term vs -> List Name -> (List (Name, Name), List RawImp)
  addEnv idx [] used = ([], [])
  addEnv idx {vs = v :: vs} (b :: bs) used
    = let n = getBindName idx v used
          (ns, rest) = addEnv (idx + 1) bs (snd n :: used)
          ns' = n :: ns in
      (ns', --IVar (snd n) :: rest)
            IPatvar (snd n) Implicit Implicit :: rest)
        -- TODO Adding these as patvars seems to make the actual args be left as implicits
        --      Maybe we need to use this function to get (names, patvars) ?
  addEnv' : {vs : _} ->
           Int -> Env Term vs -> List Name -> (List (AppInfo, RawImp), List (Name, RawImp))
  addEnv' idx [] used = ([], [])
  addEnv' idx {vs = v :: vs} (b :: bs) used
    = let n = getBindName idx v used
          mty = toTTImp $ binderType b
          appinfo = case binderInfo b of
                      Just Implicit => AImplicit
                      _             => AExplicit
          ty = fromMaybe (trace "Failed to unelab pattern type in case statement" Implicit)
                          mty
          (ns, rest) = addEnv' (idx + 1) bs (snd n :: used)
      in ((appinfo, IVar (snd n)) :: ns,
          (snd n, ty) :: rest)

  -- Replace a variable in the argument list; if the reference is to
  -- a variable kept in the outer environment (therefore not an argument
  -- in the list) don't consume it
  replace : (idx : Nat) -> RawImp -> List RawImp -> List RawImp
  replace Z lhs (old :: xs)
    = let lhs' = case old of
                   --IPatvar n ty scope => IPatvar n ty lhs
                   -- TODO Again, not sure on Patvar vs IAs
                   _ => lhs
      in lhs' :: xs
  replace (S k) lhs (x :: xs)
    = x :: replace k lhs xs
  replace _ _ xs = xs

  mkSplit : Maybe (Var vs) ->
            RawImp -> List RawImp ->
            List RawImp
  mkSplit Nothing lhs args = reverse (lhs :: args)
  mkSplit (Just (MkVar {i} prf)) lhs args
    = reverse (replace i lhs args)

  -- Pattern names used in the pattern we're matching on, so don't bind them
  -- in the generated case block
  -- TODO OK?
  usedIn : RawImp -> List Name
  usedIn (IPatvar n _ _) = [n]
  usedIn (IApp _ f a) = usedIn f ++ usedIn a
  usedIn _ = []

  -- Get a name update for the LHS (so that if there's a nested data declaration
  -- the constructors are applied to the environment in the case block)
  nestLHS : (Name, (Maybe Name, List (Var vars), a)) -> (Name, RawImp)
  nestLHS (n, (mn, ns, t))
    = (n, apply (IVar (fromMaybe n mn))
                (map (const (AExplicit, Implicit)) ns))

  removePatBinds : List (AppInfo, RawImp) -> List (AppInfo, RawImp)
  removePatBinds [] = []
  removePatBinds ((i, IPatvar _ _ sc) :: xs) = removePatBinds $ (i, sc) :: xs
  removePatBinds (x :: xs) = x :: removePatBinds xs

  wrapPatBinds : List (Name, RawImp) -> RawImp -> RawImp
  wrapPatBinds [] lhs = lhs
  wrapPatBinds ((pname, pty) :: ps) lhs = IPatvar pname pty (wrapPatBinds ps lhs)

  findPatBinds : List RawImp -> List (Name, RawImp)
  findPatBinds [] = []
  findPatBinds ((IPatvar n ty sc) :: xs) = (n, ty) :: findPatBinds (sc :: xs)
  findPatBinds (x :: xs) = findPatBinds xs

  impsToImplicit : {vars : _} -> (fnTy : Term vars) -> List (AppInfo, RawImp) -> List (AppInfo, RawImp)
  impsToImplicit _ [] = []
  impsToImplicit (Bind _ (Pi _ Implicit _) sc) (arg :: args) = (AImplicit, Implicit) :: impsToImplicit sc args
  impsToImplicit (Bind _ (Pi _ Explicit _) sc) (arg :: args) = arg                   :: impsToImplicit sc args
  impsToImplicit _ _ = [(AImplicit, Implicit)] -- Should never be anything but a pi binder or empty

  mapSnd : (List a-> List b) -> List (AppInfo,a) -> List (AppInfo,b)
  mapSnd f xs = zip (reverse (map fst xs) ++ [AExplicit]) (f $ map snd xs) -- TODO I think i should be not reversing, but just passing the tuple into every fn that needs it (so it can be reversed there!)

  updateClause : Name -> Term [] -> Maybe (Var vars) ->
                 Env Term vars -> ImpClause -> ImpClause
  updateClause casen fnty splitOn env (ImpossibleClause lhs)
    = let (args, pats) = addEnv' 0 env (usedIn lhs)
          args' = mapSnd (mkSplit splitOn lhs) args
          argsNoPatBind = removePatBinds args'
          lhs'  = wrapPatBinds (reverse pats ++ findPatBinds [lhs])
                               (apply (IVar casen) argsNoPatBind) in
      ImpossibleClause lhs'

  updateClause casen fnty splitOn env (PatClause lhs rhs)
    = let (args, pats) = addEnv' 0 env (usedIn lhs)
          args' = mapSnd (mkSplit splitOn lhs) args
          argsNoPatBind = impsToImplicit fnty (removePatBinds args')
          lhs' = wrapPatBinds (reverse pats ++ findPatBinds [lhs]) -- findPatBinds (map snd args'))
                              (apply (IVar casen) argsNoPatBind) in
      PatClause lhs' rhs


export
checkCase : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Stg Stage} ->
            {auto u : Ref UST UState} ->
            ElabMode ->
            Env Term vars ->
            (scr : RawImp) -> (scrty : RawImp) -> List ImpClause ->
            Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
checkCase mode env scr scrty_in alts exp
  = do

       -- We might have lambda bound names in our env but we're about
       -- to lift these our to a new top
       let env = lamsToPisEnv env

       -- Try to recover scrty if it's implicit
       scrty_exp <- case scrty_in of
                      Implicit => guessScrType alts
                      _ => pure scrty_in

       -- Check scrutinee type is a type
       (scrtyv, scrtyt) <- check env scrty_exp (Just gType)
       -- Check scrutinee has expected type
       (scrtm_in, gscrty) <- check env scr (Just (gnf env scrtyv))

       -- Check if we've managed to work out scrty (if not, we bail)
       scrty <- getTerm gscrty
       defs <- get Ctxt
       checkConcrete !(nf defs env scrty)

       caseBlock mode env scr scrtm_in scrty alts exp

  where
  checkConcrete : NF vs -> Core ()
  checkConcrete (NApp (NMeta n _) _)
    = throw (GenericMsg "Can't infer type for case scrutinee")
  checkConcrete _ = pure ()

  applyTo : Defs -> RawImp -> NF [] -> Core RawImp
  applyTo defs ty (NBind _ (Pi _ Explicit _ ) sc)
    = applyTo defs (IApp AExplicit ty Implicit)
        !(sc defs (toClosure [] Erased))
  applyTo defs ty (NBind _ (Pi _ Implicit _ ) sc)
    = applyTo defs (IApp AImplicit ty Implicit)
        !(sc defs (toClosure [] Erased))
  applyTo defs ty _ = pure ty

  -- Get the name and type of the family the scrutinee is in
  getRetTy : Defs -> NF [] -> Core (Maybe (Name, NF []))
  getRetTy defs (NBind _ (Pi _ _ _) sc)
    = getRetTy defs !(sc defs (toClosure [] Erased))
  getRetTy defs (NTCon n _ _ _ _)
    = do Just ty <- lookupDefType n defs
           | Nothing => pure Nothing
         pure (Just (n, !(nf defs [] ty)))
  getRetTy _ _ = pure Nothing

  -- Guess a scrutinee type by looking at the alternatives, so that we
  -- have a hint for building the case type
  guessScrType : List ImpClause -> Core RawImp
  guessScrType [] = pure $ Implicit
  guessScrType (PatClause x _ :: xs)
    = case getFn x of
        IVar n =>
          do defs <- get Ctxt
             Just ty <- lookupDefType n defs
                 | Nothing => guessScrType xs
             Just (tyn, tyty) <- getRetTy defs !(nf defs [] ty)
                 | _ => guessScrType xs
             applyTo defs (IVar tyn) tyty
        _ => guessScrType xs
  guessScrType (_ :: xs) = guessScrType xs
