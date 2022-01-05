{-
Utilities for erasure, based on the implementation in Idris 1.

The thoery is based on Matus Tejiscak's "Practical Erasure in Dependently Typed
Languages". See the paper here
https://eb.host.cs.st-andrews.ac.uk/drafts/dtp-erasure-draft.pdf, and thesis
here https://ziman.functor.sk/media/thesis.pdf
-}
module Core.Erasure

import Core.TT
import Core.Context
import Core.CaseTree

import Data.SortedMap as M
import Data.SortedSet as S
import Data.List as L
import Data.List.Reverse
import Data.Maybe
import Debug.Trace

-- Let's define some types

public export
Reason : Type
Reason = (Name, Int)

public export
UseMap : Type
UseMap = SortedMap Name (SortedMap Int (SortedSet Reason))

data Arg : Type where
  Ret  : Arg
  ArgN : Int -> Arg

Node : Type
Node = (Name, Arg)

-- Nodes along with sets of reasons (dependencies) for every one.
DepSet : Type
DepSet = SortedMap Node (SortedSet Reason)

-- | "Condition" is the conjunction of elementary assumptions along
-- the path from the root.  Elementary assumption (f, i) means that
-- "function f uses the argument i".
Cond : Type
Cond = SortedSet Node

Constraint : Type
Constraint = (Cond, DepSet)

--  type Deps = Map Cond DepSet
Deps : Type
Deps = SortedMap Cond DepSet

record VarInfo where
  constructor MkVarInfo
  viDeps : DepSet       -- ^ dependencies drawn in by the variable
  viFunArg : Maybe Int  -- ^ which function argument this variable came from (defined only for patvars)
  viMethod : Maybe Name -- ^ name of the metamethod represented by the var, if any

--  type Vars = Map Name VarInfo
Vars : Type
Vars = SortedMap Name VarInfo

-- Now some instances for those types

Show Arg where
  show Ret      = "Ret"
  show (ArgN n) = "ArgN " ++ show n

Eq Arg where
  Ret      == Ret      = True
  (ArgN x) == (ArgN y) = x==y
  _        == _        = False

Ord Arg where
  compare Ret Ret = EQ
  compare Ret (ArgN x) = GT
  compare (ArgN x) Ret = LT
  compare (ArgN x) (ArgN y) = compare x y

Ord k => Ord (SortedSet k) where
  compare a b = compare (S.toList a) (S.toList b)

-- And the bulk of the algorithm...

{-

Notes on Haskell conversion:

Their context is a map of names to a map on names(?) Is that the hierarchical
names coming into effect

-}

range : Nat -> List Int
range x = if x > 0 then [0 .. cast x - 1] else []

insertWith : (a -> a -> a) -> k -> a -> SortedMap k a -> SortedMap k a
insertWith f k a sm = case lookup k sm of
  Nothing => insert k a sm
  Just old => insert k (f a old) $ delete k sm

unionMap : (a -> Deps) -> List a -> Deps
unionMap f as = foldl (mergeWith (mergeWith union)) empty $ map f as

emptyVarInfo : VarInfo
emptyVarInfo = MkVarInfo empty Nothing Nothing

unApply : Term vars -> (Term vars, List (Term vars))
unApply tm = ua [] tm
  where
  ua : List (Term vars) -> Term vars -> (Term vars, List (Term vars))
  ua args (App f a) = ua (a::args) f
  ua args tm        = (tm, args)

revOnto : (xs, vs : List a) -> reverseOnto xs vs = reverse vs ++ xs
revOnto _ [] = Refl
revOnto xs (v :: vs)
  = rewrite revOnto (v :: xs) vs in
    rewrite appendAssociative (reverse vs) [v] xs in
    rewrite revOnto [v] vs in Refl

revLemma : (n : x) -> (as, bs : List x) -> reverseOnto [] as ++ (n :: bs) =
                                           reverseOnto [n] as ++ bs
revLemma n [] bs = Refl
revLemma n (x :: xs) ys
  = rewrite sym (revLemma x xs (n::ys)) in
    rewrite revOnto [x,n] xs in
    rewrite appendAssociative (reverseOnto [] xs) [x,n] ys in
    Refl

unfoldLams : Term vars -> (ns ** Term (reverse ns++vars))
unfoldLams (Bind n (Lam s info ty) scope) = let (args' ** scope') = unfoldLams scope
                                            in (n::args' ** rewrite sym (revLemma n args' vars) in scope')
unfoldLams tm = ([] ** tm)

lamToLet' : {vars:_} -> List (Term vars) -> Term vars -> Term vars
lamToLet' (arg :: args) (Bind n (Lam s info ty) scope) = let scope' = lamToLet' (map (weakenNs [n]) args) scope
                                                         in Bind n (Let s arg ty) $ scope'
lamToLet' args tm = apply tm args

lamToLet : {vars:_} -> Term vars -> Term vars
lamToLet tm = let (f, args) = unApply tm in lamToLet' args f

getFnArity : Term vars -> Nat
getFnArity (Bind x y scope) = S $ getFnArity scope
getFnArity _ = Z

getArity : Defs -> Name -> Nat
getArity defs n = case lookupDefPure n defs of
  Nothing => trace "Couldn't find name in Defs for arity check" 0
  (Just (MkGlobalDef type None)) => trace "Got None in arity check" 0
  (Just (MkGlobalDef type (PMDef args treeCT))) => length args
  (Just (MkGlobalDef type (DCon tag arity))) => arity
  (Just (MkGlobalDef type (TCon x tag arity))) => arity
  (Just (MkGlobalDef type Hole)) => trace "Can't find arity of hole" 0
  (Just (MkGlobalDef type (Guess guess constraints))) => trace "Can't find arity of guess" 0

indexMaybe : Nat -> List a -> Maybe a
indexMaybe Z     (x::xs) = Just x
indexMaybe (S n) (x::xs) = indexMaybe n xs
indexMaybe _     _       = Nothing

-- Generate new names for a particular constructor of a named data constructor
mkFieldName : Name -> Int -> Name
mkFieldName (UN n) fieldNo = MN n fieldNo
mkFieldName (MN n i) fieldNo = trace "Got an MN in mkField Name... uh oh" $ MN (n++"field"++show n) fieldNo

-- Our dependency map function is a bit simplier since we don't need arguments
-- for:
--   + `externs`: we don't have any externally defined functions!
--   + `used`: we don't have a %used pragma to mark things as non-erasable (should we?
--   + `ci`: we don't have interfaces (they handle these as a special case)
buildDepMap : Defs -> List Name -> Deps
buildDepMap defs startNames
  = addPostulates $ dfs empty empty startNames

  where
  postulates : List (Cond, DepSet)
  postulates = [(empty, fromList $ map (\n=>((n,Ret), empty)) startNames)]

  addPostulates : Deps -> Deps
  addPostulates deps = foldr (\(ds, rs) => insertWith (mergeWith union) ds rs) deps postulates

  -- extract all names that a function depends on
  -- from the Deps of the function
  allNames : Deps -> SortedSet Name
  allNames = foldr union empty . map names . M.toList
    where
    names : (Cond, DepSet) -> SortedSet Name
    names (cs, ns) = fromList (map fst $ S.toList cs) `union` fromList (map fst $ keys ns)

  localToName : (args : List Name) -> (idx : Nat) -> (0 p : IsVar name idx args) -> Name
  localToName (name :: ns) 0 First = name
  localToName (_ :: ns) (S k) (Later x) = localToName ns k x

  getDepsTerm : {vars:_} -> Vars -> List (Name, Cond -> Deps) -> Cond -> Term vars -> Deps

  -- References introduce dependencies as described in `vs'
  getDepsTerm vs bs cd (Ref nt n)
    = case lookup n bs of
        Just deps => deps cd
        Nothing   =>
          case lookup n vs of
            Just var => singleton cd (viDeps var)
            Nothing  => singleton cd (singleton (n, Ret) empty)

  -- Dependencies of locals are described in bs
  getDepsTerm vs bs cd (Local idx p)
    = let n = localToName vars idx p in
      case lookup n bs of
        Just deps => deps cd
        Nothing =>
          case M.lookup n vs of
            Just var =>
              case viMethod var of
                Just meth => viDeps var `ins` ( (singleton (meth,Ret) empty) `ins` empty )
                Nothing   => let ans = viDeps var in ans `ins` empty
            Nothing      => trace ("Couldn't find local var " ++ show n) empty
    where
    ins : DepSet -> Deps -> Deps
    ins = insertWith (M.mergeWith S.union) cd

    --fromMaybe (trace ("Wrong de bruijn indexing in getDepsTerm; idx=" ++ show idx ++ " length of bs = " ++ show (length bs)) empty)
    -- ( map (\x=>snd x cd) (indexMaybe idx bs) )

  getDepsTerm vs bs cd (Meta n args) = trace ("Cannot analyse metavar, "++show n) empty

  getDepsTerm vs bs cd (Bind n (Let _ val _) scope)
    = var val cd `mergeLeft` getDepsTerm vs ((n, const empty) :: bs) cd scope
    where
    var : Term vars -> Cond -> Deps
    var tm cd = getDepsTerm vs bs cd tm
  getDepsTerm vs bs cd (Bind n b             scope)
    = getDepsTerm vs ((n, const empty) :: bs) cd scope

  getDepsTerm vs bs cd (App f x) = let (fun, args) = unApply (App f x) in
      case fun of
        (Ref (DataCon tag arity) n)       => conditionalDeps n args
        (Ref (TyCon y tag arity) n)       => unconditionalDeps args
        (Ref Func n)                      => conditionalDeps n args
        (Ref Bound n) =>
          -- Debruijn-bound name
          case lookup n bs of
            Just deps => deps cd `union` unconditionalDeps args
            Nothing =>
              case lookup n vs of
                Just var =>
                  case viMethod var of
                    -- Local name that refers to a method
                    Just meth => viDeps var `ins` conditionalDeps meth args
                    Nothing   => viDeps var `ins` unconditionalDeps args
                Nothing  => conditionalDeps n args

        (Local idx p)
          => let n = localToName vars idx p in
             case lookup n bs of
               Just deps => deps cd `union` unconditionalDeps args
               Nothing =>
                 case M.lookup n vs of
                   Just var =>
                     case viMethod var of
                       Just meth => viDeps var `ins` conditionalDeps meth args
                       Nothing   => viDeps var `ins` unconditionalDeps args
                   Nothing      => trace ("Couldn't find local var " ++ show n) empty
                           --fromMaybe (trace ("Incorrect Local index during analysis; idx = " ++ show idx ++ ", length of bs =" ++ show (length bs)) $ const empty)              --(map snd $ indexMaybe idx bs) cd `union` unconditionalDeps args

        (Bind n b scope) => --getDepsTerm vs bs cd (lamToLet (App f x))
                            getDepsTerm vs ((n, const empty) :: bs) cd scope
        Erased           => empty
        (App f a)        => trace "Found nested App after unApply" empty
        (Quote tm)       => getDepsTerm vs bs cd tm --trace "Cannot analyse application to Quote" empty
        (TCode tm)       => trace "Cannot analyse application to Code Type" empty
        (Eval tm)        => trace "Cannot analyse application to Eval" empty
        (Escape tm)      => getDepsTerm vs bs cd tm --trace "Cannot analyse application to Escape" empty
        (Meta n args)    => trace ("Cannot analyse application of metavar ("++ show n++") to " ++ show args) empty
        TType            => trace ("Cannot analyse application of Type to " ++ show args) empty
    where
    union : Deps -> Deps -> Deps
    union = mergeWith $ mergeWith S.union
    ins : DepSet -> Deps -> Deps
    ins = insertWith (M.mergeWith S.union) cd
    unconditionalDeps : List (Term vars) -> Deps
    unconditionalDeps = unionMap (getDepsTerm vs bs cd)
    conditionalDeps : Name -> List (Term vars) -> Deps
    conditionalDeps n tms
      = ins (singleton (n,Ret) empty) . unionMap (getDepsArgs n) $ zip indices tms
      where
      getDepsArgs : Name -> (Maybe Int, Term vars) -> Deps
      getDepsArgs n (Just i , t) = getDepsTerm vs bs (S.insert (n, ArgN i) cd) t --conditional
      getDepsArgs n (Nothing, t) = getDepsTerm vs bs cd t                        --unconditional
      indices : List (Maybe Int)
      indices = map Just (range $ getArity defs n) ++ replicate (length tms `minus` getArity defs n) Nothing
    methodDeps : Name -> (Int, Term vars) -> Deps
    methodDeps ctorName (methNo, t)
      = getDepsTerm (vrs `mergeLeft` vs) (bruijns ++ bs) cond (snd dbody)
      where
      dbody : ( ns ** Term (reverse ns ++ vars))
      dbody = unfoldLams t
      args : List Name
      args = fst dbody
      metameth : Name
      metameth = mkFieldName ctorName methNo
      deps : Int -> DepSet
      deps i = singleton (metameth, ArgN i) empty
      vrs : Vars
      vrs = M.fromList [(v, MkVarInfo (deps i)
                                      (Just i)
                                      (Nothing)
                        ) | (v, i) <- zip args (range $ length args)
                       ]
      bruijns : List (Name, (Cond -> Deps))
      bruijns = reverse [ (n, \cd => singleton cd (deps i))
                        | (i,n) <- zip (range $ length args) args
                        ]
      cond : Cond
      cond = singleton (metameth, Ret)

  getDepsTerm vs bs cd TType       = empty
  getDepsTerm vs bs cd Erased      = empty
  getDepsTerm vs bs cd (Quote tm)  = getDepsTerm vs bs cd tm
  getDepsTerm vs bs cd (TCode tm)  = getDepsTerm vs bs cd tm
  getDepsTerm vs bs cd (Eval tm)   = getDepsTerm vs bs cd tm
  getDepsTerm vs bs cd (Escape tm) = getDepsTerm vs bs cd tm

  etaExpand : List Name -> Term vars -> Term vars
  etaExpand []      tm = tm
  etaExpand (n::ns) tm = etaExpand ns (App tm (Ref Bound n))

  mutual
    getDepsAlt : {vars : _} -> Name -> List Name -> Vars -> VarInfo -> CaseAlt vars -> Deps
    getDepsAlt fn es vs var (DefaultCase        ct) = getDepsCT fn es vs ct
    getDepsAlt fn es vs var (ConCase n tag args ct)
      = getDepsCT fn es (mergeLeft vs' vs) ct
      where
      varIdx : Int
      varIdx = fromMaybe (trace "Nonpatvar gound inside alt?! " 0) (viFunArg var)
      meth : Int -> Maybe Name
      meth i = Just $ mkFieldName n i
      vs' : Vars
      vs' = M.fromList [(v, MkVarInfo (insertWith union (n, ArgN j) (singleton (fn, varIdx)) (viDeps var))
                                      (viFunArg var)
                                      (meth j)
                       ) | (v, j) <- zip args (range $ length args)]

    getDepsCT : {args : _} -> Name -> List Name -> Vars -> CaseTree args -> Deps
    getDepsCT fn es vs (Unmatched _) = empty
    getDepsCT fn es vs Impossible = empty
    getDepsCT fn es vs (STerm tm) = getDepsTerm vs [] (singleton (fn, Ret)) (etaExpand es tm)
    getDepsCT fn es vs (Case idx p scTy alts)
      = -- we case-split on this variable, which marks it as used
        -- (unless there is exactly one case branch)
        -- hence we add a new dependency, whose only precondition is
        -- that the result of this function is used at all
        addTagDep $ unionMap (getDepsAlt fn es vs casedVar) alts -- coming from the whole subtree
      where
      name : Name
      name = localToName args idx p
      casedVar : VarInfo
      casedVar = fromMaybe (trace ("nonpatvar in case: " ++ show name) emptyVarInfo) (lookup name vs)
      addTagDep : Deps -> Deps
      addTagDep = case alts of
        [ ]       => const empty
        [_]       => id
        (x :: xs) => insertWith (mergeWith union) (singleton (fn, Ret)) (viDeps casedVar)

  getDepsDef : Name -> GlobalDef -> Deps
  getDepsDef n (MkGlobalDef type None) = trace "Encountered a None global def during erasure dep map"
                                               empty
  getDepsDef n (MkGlobalDef type (DCon tag arity         )) = empty -- These deps are created when _applying_ constructor args
  getDepsDef n (MkGlobalDef type (TCon x tag arity       )) = empty
  getDepsDef n (MkGlobalDef type Hole                     ) = empty
  getDepsDef n (MkGlobalDef type (Guess guess constraints)) = empty
  getDepsDef fn (MkGlobalDef type (PMDef args treeCT))
    = getDepsCT fn etaVars (mergeLeft etaMap varMap) treeCT
    where
    etaIdx : List Int
    etaIdx = drop (length args) (range $ getFnArity type)
    etaVars : List Name
    etaVars = [MN "eta" i | i<-etaIdx]
    varPair : Name -> Int -> (Name, VarInfo)
    varPair n argNo = (n
                      ,MkVarInfo (singleton (fn, ArgN argNo) empty)
                                 (Just argNo)
                                 (Nothing)
                      )
    etaMap : Vars
    etaMap = fromList [varPair (MN "eta" i) i | i<-etaIdx]
    varMap : Vars
    varMap = fromList [varPair v i | (v,i) <- zip args (range $ length args)]

  getDeps : Name -> Deps
  getDeps n = case lookupDefPure n defs of
    Nothing => case n of 
                 (MN ctorname i) => singleton (singleton (UN ctorname, ArgN i)) empty
                 _               => trace ("Unknown name " ++ show n ++ " found during erasure dep map")
                                          empty
    Just def => getDepsDef n def

  -- perform depth-first search
  -- to discover all the names used in the program
  -- and call getDeps for every name
  dfs : SortedSet Name -> Deps -> List Name -> Deps
  dfs visited deps [] = deps
  dfs visited deps (n :: ns) = case contains n visited of
      True  => dfs visited deps ns
      False => dfs (insert n visited) (mergeWith (mergeWith union) deps' deps) (next ++ ns)
    where
    deps' : Deps
    deps' = getDeps n
    depn : SortedSet Name
    depn = delete n $ allNames deps'
    next : List Name
    next = [n | n <- S.toList depn, not (contains n visited)]

-- | In each iteration, we find the set of nodes immediately reachable
-- from the current set of constraints, and then reduce the set of constraints
-- based on that knowledge.
--
-- In the implementation, this is phase-shifted. We first reduce the set
-- of constraints, given the newly reachable nodes from the previous iteration,
-- and then compute the set of currently reachable nodes.
-- Then we decide whether to iterate further.
forwardChain : SortedMap Node (SortedSet Int) -- ^ node index
             -> DepSet                        -- ^ all reachable nodes found so far
             -> DepSet                        -- ^ nodes reached in the previous iteration
             -> SortedMap Int Constraint      -- ^ numbered constraints
             -> (SortedMap Int Constraint, DepSet)
forwardChain index solution previouslyNew constrs
  = case 0 == length (M.toList currentlyNew) of
      -- No newly reachable nodes, fixed point has been reached
      True  => (constrs, solution)
      -- some newly reachable nodes, iterate more
      False => forwardChain index
                            (mergeWith union solution currentlyNew)
                            currentlyNew
                            constrs'
  where
  -- which constraints could give new results, given that `previouslyNew`
  -- has been derived in the last iteration
  affectedIxs : SortedSet Int
  affectedIxs = foldr union empty [
      fromMaybe empty (lookup n index)
      | n <- keys previouslyNew
    ]

  -- Update the pair (newly reached nodes, numbered constraint set)
  -- by reducing the constraint with the given number.
  reduceConstraint : SortedSet Node -> Int -> (DepSet, SortedMap Int (Cond, DepSet))
                                           -> (DepSet, SortedMap Int (Cond, DepSet))
  reduceConstraint previouslyNew i (news, constrs)
    = case lookup i constrs of
        -- Constraint number present in index but not found
        -- among the constraints. This happens more and more frequently
        -- as we delete constraints from the set.
        Nothing           => (news, constrs)
        Just (cond, deps) =>
          let cond' = difference cond previouslyNew in
          if 0 == length (S.toList cond')
          -- This constraint's set of preconditions has shrunk
          -- to the empty set. We can add its RHS to the set of newly
          -- reached nodes, and remove the constraint altogether.
          then (mergeWith union news deps, delete i constrs)
          else if (length (S.toList cond') < length (S.toList cond))
            -- This constraint's set of preconditions has shrunk
            -- so we need to overwrite the numbered slot
            -- with the updated constraint.
               then (news, insert i (cond', deps) constrs)
               -- This constraint's set of preconditions hasn't changed
               -- so we do not do anything about it
               else (news, constrs)

  -- Traverse all (potentially) affected constraints, building:
  --  1. a set of newly reached nodes
  --  2. updated set of constraints where the previously reached
  --     nodes have been removed
  newPair : (DepSet, SortedMap Int Constraint)
  newPair = foldr (reduceConstraint . S.fromList $ keys previouslyNew)
                  (empty, constrs)
                  affectedIxs
  currentlyNew : DepSet
  currentlyNew = fst newPair
  constrs' : SortedMap Int Constraint
  constrs' = snd newPair

-- | Find the minimal consistent usage by forward chaining.
--
-- We use a cleverer implementation that:
-- 1. First transforms Deps into a collection of numbered constraints
-- 2. For each node, we remember the numbers of constraints
--    that contain that node among their preconditions.
-- 3. When performing forward chaining, we perform unit propagation
--    only on the relevant constraints, not all constraints.
minimalUsage : Deps -> (Deps, (SortedSet Name, UseMap))
minimalUsage deps
  = let (a, b) = forwardChain (index numbered) seedDeps seedDeps numbered
    in (fromNumbered a, gather b)
  where
  toNumbered : Deps -> SortedMap Int Constraint
  toNumbered d = let ds = toList d
                 in fromList $ zip (range $ length ds) ds

  fromNumbered : SortedMap Int Constraint -> Deps
  fromNumbered = foldr (\(ns,vs) => insertWith (mergeWith union) ns vs) empty

  numbered : SortedMap Int Constraint
  numbered = toNumbered deps

  -- The initial solution. Consists of nodes that are
  -- reachable immediately, without any preconditions.
  seedDeps : DepSet
  seedDeps = foldr (mergeWith union) empty [ds | (cond, ds) <- values numbered, null cond]

  -- Build an index that maps every node to the set of constraints
  -- where the node appears among the preconditions.
  index : SortedMap Int Constraint -> SortedMap Node (SortedSet Int)
  index = foldr outer empty . toList
    where
    inner : Int -> Node -> SortedMap Node (SortedSet Int) ->  SortedMap Node (SortedSet Int)
    inner i n ix' = insertWith union n (singleton i) ix'
    outer : (Int, Constraint) -> SortedMap Node (SortedSet Int) -> SortedMap Node (SortedSet Int)
    outer (i, (ns, _)) ix = foldr (inner i) ix (S.toList ns)

  -- Convert a solution of constraints into:
  -- 1. the list of names used in the program
  -- 2. the list of arguments used, together with their reasons
  gather : DepSet -> (SortedSet Name, UseMap)
  gather = foldr ins (empty, empty) . M.toList
    where
    ins : (Node, SortedSet Reason) -> (SortedSet Name, UseMap) -> (SortedSet Name, UseMap)
    ins ((n, Ret   ), rs) (ns, umap) = (insert n ns, umap)
    ins ((n, ArgN i), rs) (ns, umap) = (ns, insertWith (mergeWith union) n (singleton i rs) umap)

-- Perform usage analysis for list of given names, returning the list of reachable
-- (non-erasable) names.
export
performUsageAnalysis : Defs -> List Name -> Core (List Name, UseMap)
performUsageAnalysis defs [] = pure ([], empty)
performUsageAnalysis defs ns
  = do -- Get the dependency graph
       let depMap = buildDepMap defs ns

       -- Search for reachable nodes
       let (residDeps, (reachableNames, minUse)) = minimalUsage depMap

       pure (S.toList reachableNames, minUse)
