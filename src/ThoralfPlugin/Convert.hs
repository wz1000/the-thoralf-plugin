{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module ThoralfPlugin.Convert where

import Debug.Trace

import Data.Char
import Data.Maybe ( mapMaybe, catMaybes )
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Set as S
import qualified SimpleSMT as SMT
import Data.Semigroup
import Control.Monad.Reader
import Prelude
import UniqSet

import DynFlags
import Outputable hiding ( (<>) )

-- GHC API imports:
import GhcPlugins hiding ( (<>) )
import TcRnTypes ( Ct, ctPred )
import Class ( Class(..) )
import TcType ( Kind, tyCoVarsOfTypesList )
import Var ( TyVar, Var )
import Type ( Type, PredTree (..), EqRel (..), getTyVar_maybe
            , splitTyConApp_maybe, splitFunTy_maybe
            , classifyPredType, tyVarKind )
import CoAxiom
import DataCon
import FV
import Unify

-- Internal imports
import ThoralfPlugin.Encode.TheoryEncoding
import Data.Vec



-- * Data Definitions
--------------------------------------------------------------------------------


-- ** Core Types

-- | The input needed to convert 'Ct' into smt expressions.
-- We need the class for dis equality, and an encoding of a collection of
-- theories.
data EncodingData where
  EncodingData ::
    { encodeDisEq :: Class
    , encodeTheory :: TheoryEncoding
    } -> EncodingData


-- | The output of converting constraints. We have a list of converted
-- constraints as well as a list of declarations. These declarations are
-- variable declarations as well as function symbols with accompanying
-- defining assert statements.
data ConvCts where
  ConvCts ::
    { convEquals :: [(SExpr, Ct)]
    , convDeps :: [SExpr]
    , convLDeps :: LateDeps
    } -> ConvCts


-- | Since our encoding data is passed around as a constant state, we put
-- it in a reader monad. Of course, conversion could fail, so we transform
-- from a Maybe monad.
type ConvMonad a = ReaderT EncodingData Maybe a




-- ** Basic Definitions

-- | The type of smt expressions.
type SExpr = SMT.SExpr



-- * Convert Function
--------------------------------------------------------------------------------

convert :: EncodingData -> [Ct] -> Maybe ConvCts
convert encodingData cts = runReaderT (conv cts) encodingData


conv :: [Ct] -> ConvMonad ConvCts
conv cts = do
  EncodingData disEqClass _ <- ask
  let disEquals = extractDisEq disEqClass cts
  let equals = extractEq cts
  convDisEqs <- mapSome $ fmap convPair (map fst disEquals)
  convEqs <- mapSome $ fmap convPair (map fst equals)

  let deps = mconcat $ map snd convDisEqs ++ map snd convEqs
  (decls,ldeps) <- convertDeps deps

  let eqExprs = map (mkEqExpr . fst) convEqs
  let disEqExprs = map (mkDisEqExpr . fst) convDisEqs
  let matchingCts = map snd $ disEquals ++ equals
  --guard (length matchingCts == length (disEqExprs ++ eqExprs))
  let convPairs = zip (disEqExprs ++ eqExprs) matchingCts
  return $ ConvCts convPairs decls ldeps

  where

  convPair :: (Type, Type) -> ConvMonad ((SExpr, SExpr), ConvDependencies)
  convPair (t1, t2) = do
    (t1', deps1) <- convertType t1
    (t2', deps2) <- convertType t2
    let sexpr = SMT.Atom
    let convertedPair = (sexpr t1', sexpr t2')
    return (convertedPair, deps1 <> deps2)

  mkEqExpr :: (SExpr, SExpr) -> SExpr
  mkEqExpr (s1,s2) = SMT.eq s1 s2

  mkDisEqExpr :: (SExpr, SExpr) -> SExpr
  mkDisEqExpr (s1,s2) = (SMT.not $ SMT.eq s1 s2)

  mapSome :: [ConvMonad a] -> ConvMonad [a]
  mapSome xs = do
    state <- ask
    let maybeVals = map (`runReaderT` state) xs
    return $ catMaybes maybeVals

showOut x = renderWithStyle unsafeGlobalDynFlags (ppr x) (defaultUserStyle unsafeGlobalDynFlags)

makeSMTName :: (Uniquable a, Outputable a) => a -> String
makeSMTName a = "v-"++filter isAlphaNum (showOut a)++"-"++show (getUnique a)

-- ** Extraction
--------------------------------------------------------------------------------

extractEq :: [Ct] -> [((Type, Type), Ct)]
extractEq = mapMaybe maybeExtractTyEq

extractDisEq :: Class -> [Ct] -> [((Type, Type), Ct)]
extractDisEq cls = mapMaybe (maybeExtractTyDisEq cls) where


maybeExtractTyDisEq :: Class -> Ct -> Maybe ((Type, Type), Ct)
maybeExtractTyDisEq disEqCls ct = do
  let predTree = classifyPredType $ ctPred ct
  ClassPred class' (_: t1 : t2 : _) <- return predTree
  guard (class' == disEqCls)
  return ((t1,t2),ct)

maybeExtractTyEq :: Ct -> Maybe ((Type, Type), Ct)
maybeExtractTyEq ct = do
  let predTree = classifyPredType $ ctPred ct
  case predTree of
    EqPred NomEq t1 t2 -> return ((t1,t2),ct)
    _ -> Nothing


  {-
  return ((simpIfCan t1, simpIfCan t2), ct) where

  simpIfCan :: Type -> Type
  simpIfCan t = case coreView t of
    Just t' -> t'
    Nothing -> t -}


-- ** Converting the Dependencies
----------------------------------------

nub :: Ord a => [a] -> [a]
nub = S.toList . S.fromList

convertDeps :: ConvDependencies -> ConvMonad ([SExpr], LateDeps)
convertDeps (ConvDeps tyvars' kdvars' decs deps) = do
  let tyvars = nub tyvars'
  let kdvars = nub kdvars'
  (EncodingData _ theories) <- ask
  let mkPred = tyVarPreds theories
  let tvPreds = foldMap (fmap SMT.Atom) $ mapMaybe mkPred tyvars

  convertedTyVars <- traverse convertTyVars tyvars

  let tyVarExprs  = map       fst convertedTyVars
  let tyVarKdVars = concatMap (fst . snd) convertedTyVars
  let tyVarDeps   = mempty{lateADTs = foldMap (snd . snd) convertedTyVars}

  let kindVars = nub $ tyVarKdVars  ++ kdvars
  let kindExprs = map mkSMTSort kindVars
  decExprs <- convertDecs decs
  -- Order matters:
  let varExprs = kindExprs ++ tyVarExprs
  let otherExprs = decExprs ++ tvPreds
  let exprs = varExprs ++ otherExprs
  return (exprs,deps<>tyVarDeps)

defineType :: [String] -> SExpr
defineType sorts' = SMT.Atom $
    "(declare-datatypes () ((Type (apply (fst Type) (snd Type)) (constructor (getCon String)) "++unwords xs++")))"
  where
  sorts = nub sorts'
  xs = map f sorts
  f s = unwords ["(inc"++s,"(get"++s,s++"))"]

convertFieldType :: TyCon -> [TyVar] -> Kind -> ConvMonad (String,([KdVar],UniqSet TyCon))
convertFieldType otycon oargs ty = do
  case splitTyConApp_maybe ty of
    Just (tcon,args)
      | (tcon == otycon && and (zipWith eqType args $ map mkTyVarTy oargs)) ->
        return (makeSMTName tcon, mempty)
    _ -> convertKind ty

convertPromoted :: TyCon -> ConvMonad (SExpr, UniqSet TyCon)
convertPromoted tc =
  if isAlgTyCon tc
  then do
    let dcs = visibleDataCons $ algTyConRhs tc
        argVars = tyConTyVars tc
        args = map makeSMTName argVars
        name = makeSMTName tc
        convertCon dc = do
          convertedFieldTypes <- traverse (convertFieldType tc argVars) (dataConOrigArgTys dc)
          let
            fieldTypes = map fst convertedFieldTypes
            deps = foldMap snd convertedFieldTypes
            fieldNames = map (\n -> dname++"Field"++show n ) [1..]
            fields = zipWith (\n t -> "("++n++" "++t++")") fieldNames fieldTypes
          return ("("++unwords (dname:fields)++")", deps)
          where
            dname = makeSMTName dc
    convertedCons <- traverse convertCon dcs
    let
      cons = map fst convertedCons
      defn = "(("++unwords (name:cons)++"))"
      smtStr = unwords ["(declare-datatypes ("++unwords args++")", defn,")"]
    return (SMT.Atom smtStr, foldMap (snd . snd) convertedCons)
  else lift $ Nothing

convertFam :: TyCon -> ConvMonad (SExpr,UniqSet TyCon)
convertFam fam = do
  let name = makeSMTName fam
  let kind = tyConKind fam
  let (argtys,resty) = splitFunTys kind
  argDeps <- mapM convertKind argtys
  (res,resDeps) <- convertKind resty
  let args = unwords $ map fst argDeps
  let smtStr = SMT.Atom $ unwords ["(declare-fun",name,"(" ++ args ++ ")",res,")"]
  let deps = foldMap (snd . snd) argDeps <> snd resDeps
  return (smtStr,deps)

convertFamEqs :: TyCon  -> ConvMonad ([SExpr],LateDeps)
convertFamEqs tc
  | Just bs <- isClosedSynFamilyTyConWithAxiom_maybe tc = do
      stmts <- compileBranches (makeSMTName tc) (fromBranches $ co_ax_branches bs)
      return (map fst stmts,foldMap snd stmts)
  | otherwise = return ([],mempty)

compileBranches :: String -> [CoAxBranch] -> ConvMonad [(SExpr,LateDeps)]
compileBranches funName bs = mapM (compileBranch funName) bs

compileBranch :: String -> CoAxBranch -> ConvMonad (SExpr, LateDeps)
compileBranch funName branch = do
  --get the patterns of the branches which are incompatible to the current one
  let incompatiblePatterns = map coAxBranchLHS $ coAxBranchIncomps branch
  --get the list of variables that occur in the left hand side of the current branch
  let varList = L.nub $ concatMap (fvVarList . tyCoFVsOfType) (coAxBranchLHS branch)
  --form the SMT expression "... a b c ..." that will be used in the lhs to say "(= (funName ... a b c ...) ...)"
  lhsExpr <- (unwords <$>) $ forM (coAxBranchLHS branch) $ \ty -> do
    (tyName, _) <- convertType ty
    return tyName
  --form the SMT expression "... (a Int) (b Type) ..." that will be used in the universal quantification
  let mkBindingExpr xs =  (unwords <$>) $ forM xs $ \var -> do
        let tyName = makeSMTName var
        (sortName, _) <- convertKind (tyVarKind var)
        return $ unwords ["(", tyName, sortName, ")"]
  bindingExpr <- mkBindingExpr varList
  -- get the variables that are conflicting and also what they are conflicting with
  let negList = concatMap (getConflicts varList (coAxBranchLHS branch)) incompatiblePatterns
  -- now form the expression saying that "(not (= a 1) (= b 2))" which will talk about the previous patterns
  negExprs <- forM negList $ \(v, t) -> do
    let vName = makeSMTName v
    (tName, _) <- convertType t
    return $ unwords ["(not","(", "=", vName, tName, "))"]
  let negExpr' = foldr1 (\x y -> unwords ["(", "or", x, y, ")"]) negExprs
      freeVars = tyCoVarsOfTypesList $ map snd negList
  innerBinds <- mkBindingExpr freeVars
  let negExpr
        | null freeVars = negExpr'
        | otherwise = "(forall ("++innerBinds++") "++negExpr'++")"
  -- form the SMT expression for the right hand side of the branch
  (rhsExpr,deps) <- convertType $ coAxBranchRHS branch
  let expr = if null varList
        then unwords $ ["(", "assert"]
                       ++ ["(", "=", "(", funName]
                       ++ [lhsExpr]
                       ++ [")", rhsExpr, ")", ")"]
        else if null negList
        then unwords $ ["(", "assert", "(", "forall", "("]
                       ++ [bindingExpr] ++ [")"]
                       ++ ["(", "=", "(", funName]
                       ++ [lhsExpr]
                       ++ [")", rhsExpr, ")", ")", ")"]
        else unwords $ ["(", "assert", "(", "forall", "("]
                       ++ [bindingExpr] ++ [")", "(", "=>" ]
                       ++ [negExpr]
                       ++ ["(", "=", "(", funName]
                       ++ [lhsExpr]
                       ++ [")", rhsExpr, ")", ")", ")", ")"]
  return (SMT.Atom expr,convLateDeps deps)

getConflicts :: [Var] -> [Type] -> [Type] -> [(Var, Type)]
getConflicts varList mainLHS incompatiblePattern =
  case tcUnifyTysFG (const BindMe) mainLHS incompatiblePattern of
    SurelyApart -> []
    MaybeApart _ -> []
    Unifiable subst@(TCvSubst vars tvEnv cvEnv) -> do
      v <- varList
      case lookupVarEnv tvEnv v of
        Nothing -> []
        Just ty -> [(v, ty)]

-- | Converting Local Declarations
convertDecs :: [Decl] -> ConvMonad [SExpr]
convertDecs ds = do
  let assocList = map (\(Decl k v) -> (k,v)) ds
  let ourMap = M.fromList assocList
  let uniqueDecs = foldMap snd $ M.toList ourMap
  return $ map SMT.Atom uniqueDecs where

mkSMTSort :: TyVar -> SExpr
mkSMTSort tv = let
  name = (makeSMTName tv)
  smtStr = "(declare-sort " ++ name ++ ")"
  in SMT.Atom smtStr


-- | Kind variables are just type variables
type KdVar = TyVar
convertTyVars :: TyVar -> ConvMonad (SExpr, ([KdVar],UniqSet TyCon))
convertTyVars tv = do
  (smtSort, kindVars) <- convertKind $ tyVarKind tv
  let tvId = makeSMTName tv
  let smtVar = "(declare-const " ++ tvId ++ " " ++ smtSort ++ ")"
  return (SMT.Atom smtVar, kindVars)

generatePrelude :: EncodingData -> LateDeps -> Maybe [SExpr]
generatePrelude enc deps = runReaderT (resolveLateDeps deps) enc

resolveLateDeps :: LateDeps -> ConvMonad [SExpr]
resolveLateDeps deps = do
  (famStmts,adts,sorts) <- resolveFams (lateTyFams deps)
  adtStmts <- resolveADTs (adts <> lateADTs deps)
  -- let fakeType = --SMT.Atom "(declare-sort Type)"
  return $ adtStmts ++ defineType (sorts <> lateNewSorts deps) : famStmts

resolveFams :: UniqSet TyCon -> ConvMonad ([SExpr],UniqSet TyCon,[String])
resolveFams fams = do
  (defs,eqs,adts,sorts) <- go emptyUniqSet (nonDetEltsUniqSet fams)
  return (defs++eqs,adts,sorts)
  where
    go done [] = return ([],[],mempty,[])
    go done (x:xs)
      | elementOfUniqSet x done = go done xs
      | otherwise = do
        (dfn,adts) <- convertFam x
        let done1 = addOneToUniqSet done x
        (cureqs,deps) <- convertFamEqs x
        let depFams = nonDetEltsUniqSet $ lateTyFams deps
        (defs,eqs,adts1,sorts1) <- go done1 (depFams ++ xs)
        return (dfn:defs,cureqs++eqs,adts<>lateADTs deps<>adts1,lateNewSorts deps ++ sorts1)

resolveADTs :: UniqSet TyCon -> ConvMonad [SExpr]
resolveADTs adts = fst <$> go emptyUniqSet (nonDetEltsUniqSet adts)
  where
    go done [] = return ([],done)
    go done (x:xs)
      | elementOfUniqSet x done = go done xs
      | otherwise = do
        (this,deps) <- convertPromoted x
        let done1 = addOneToUniqSet done x
        (before,done2) <- go done1 (nonDetEltsUniqSet deps)
        (after,done3) <- go done2 xs
        return (before ++ this:after,done3)


-- * Converting A Single Type
--------------------------------------------------------------------------------


-- ** Type Conversion Data
----------------------------------------

-- | A Type is converted into a string which is a valid SMT term, if the
-- dependencies are converted properly and sent to the solver before the
-- term is mentioned.
type ConvertedType = (String, ConvDependencies)

-- | These are dependencies that are shared across given
-- and wanted, and satisifying them may be recursive
data LateDeps
  = LateDeps
  { lateTyFams :: UniqSet TyCon
  , lateNewSorts :: [String]
  , lateADTs :: UniqSet TyCon
  }

instance Semigroup LateDeps where
  (LateDeps a1 b1 c1) <> (LateDeps a2 b2 c2) =
    LateDeps (a1<>a2) (b1<>b2) (c1<>c2)
instance Monoid LateDeps where
  mempty = LateDeps mempty mempty mempty
  mappend = (<>)

-- | These are pieces of a type that need to be converted into
-- SMT declarations or definitions in order for the converted
-- type to be well sorted or correct.
data ConvDependencies where
  ConvDeps ::
    { convTyVars :: [TyVar] -- Type variables for a known theory
    , convKdVars :: [TyVar] -- Kind variables for unknown theories
    , convDecs   :: [Decl]  -- SMT declarations specific to some converted type
    , convLateDeps :: LateDeps
    } -> ConvDependencies

noDeps :: ConvDependencies
noDeps = mempty

data Decl where
  Decl ::
    { decKey :: (String, String) -- ^ A unique identifier
    , localDec :: [String]       -- ^ A list of local declarations
    } -> Decl

type Hash = String

instance Semigroup ConvDependencies where
  (ConvDeps a1 b1 c1 d1) <> (ConvDeps a2 b2 c2 d2) =
    ConvDeps (a1<>a2) (b1<>b2) (c1<>c2) (d1<>d2)

instance Monoid ConvDependencies where
  mempty = ConvDeps [] [] [] mempty
  mappend = (<>)



-- ** Converting A Type
----------------------------------------



convertType :: Type -> ConvMonad ConvertedType
convertType ty = do
  case tyVarConv ty of
    Just (smtVar, tyvar) ->
      return  (smtVar, noDeps {convTyVars = [tyvar]})
    Nothing -> tryConvTheory ty

-- Converts types of arbitary SMT Sort to types of SMT Sort Type
convertTypeToSortType :: Type -> ConvMonad ConvertedType
convertTypeToSortType ty = do
  (t, deps) <- convertType ty
  (k, kdeps) <- convertKind $ typeKind ty
  if k == "Type"
  then return (t,deps)
  else do
    let t' = "(inc"++k++" "++t++")"
        kdvars = fst kdeps
        ldeps = mempty{lateADTs=snd kdeps, lateNewSorts=[k]}
    return $ (t', deps{convKdVars = kdvars ++ convKdVars deps
                      ,convLateDeps = convLateDeps deps <> ldeps})

tyVarConv :: Type -> Maybe (String, TyVar)
tyVarConv ty = do
  tyvar <- getTyVar_maybe ty
  -- Not checking for skolems.
  -- See doc on "dumb tau variables"
  let isSkolem = True
  guard isSkolem
  let tvarStr = makeSMTName tyvar
  return (tvarStr, tyvar)


tryConvTheory :: Type -> ConvMonad ConvertedType
tryConvTheory ty = do
  EncodingData _ theories <- ask
  let tyConvs = typeConvs theories
  case tryFns tyConvs ty of
    Just (TyConvCont tys kds cont decs) -> do
      recurTys <- vecMapAll convertType tys
      recurKds <- vecMapAll convertKind kds
      (decls, (decKds,decAdts)) <- convDecConts decs
      let convTys = fmap fst recurTys
      let convKds = fmap fst recurKds
      let converted = cont convTys convKds
      let tyDeps = foldMap snd recurTys
      let kdVars = foldMap (fst . snd) recurKds ++ decKds
      let adts   = foldMap (snd . snd) recurKds
      let deps = addDepParts tyDeps kdVars decls (adts<>decAdts)
      return (converted, deps)
    Nothing -> do
      defaultConvTy ty

addDepParts :: ConvDependencies -> [KdVar] -> [Decl] -> UniqSet TyCon -> ConvDependencies
addDepParts (ConvDeps t k decl late) ks decls adts =
  ConvDeps t (k ++ ks) (decl ++ decls) (late{lateADTs=lateADTs late <> adts})

convDecConts :: [DecCont] -> ConvMonad ([Decl], ([KdVar],UniqSet TyCon))
convDecConts dcs = do
  decConts <- traverse convDecCont dcs
  let decls = map fst decConts
  let kdVars = foldMap snd decConts
  return (decls, kdVars) where

  convDecCont :: DecCont -> ConvMonad (Decl, ([KdVar],UniqSet TyCon))
  convDecCont (DecCont kholes declName cont) = do
   recur <- vecMapAll convertKind kholes
   let kConvs = fmap fst recur
   let declKey = (declName, foldMap id kConvs)
   let kdVars = foldMap snd recur
   let decl = Decl declKey (cont kConvs)
   return (decl, kdVars)


defaultConvTy :: Type -> ConvMonad ConvertedType
defaultConvTy = tryFnsM [defFn, adtDef, defTyConApp, defTyApp] where
  adtDef :: Type -> ConvMonad ConvertedType
  adtDef ty = do
    (tc, tys') <- lift $ splitTyConApp_maybe ty
    dc <- lift $ isPromotedDataCon_maybe tc
    guard (isVanillaDataCon dc)
    let visibleArgs = map isVisibleTyConBinder $ tyConBinders tc
        tys = map snd $ filter fst $ zip visibleArgs tys'
    recur <- traverse convertType tys
    let defConvTys = map fst recur
    let tvars = foldMap snd recur
    let convTcon = makeSMTName dc
    let converted = case defConvTys of
          [] -> convTcon
          _ ->  "("++unwords (convTcon:defConvTys)++")"
    return (converted, tvars <> mempty{convLateDeps = mempty{lateADTs = unitUniqSet $ dataConTyCon dc}})

  defFn :: Type -> ConvMonad ConvertedType
  defFn ty = do
    (fn, arg) <- lift $ splitFunTy_maybe ty
    (fnStr, tv1) <- convertType fn
    (argStr, tv2) <- convertType arg
    let smtStr = fnDef fnStr argStr
    return (smtStr, tv1 <> tv2)

  fnDef :: String -> String -> String
  fnDef strIn strOut =
    "(apply (apply (constructor \"->\") " ++
      strIn ++ ") " ++ strOut ++ ")"

  defTyApp :: Type -> ConvMonad ConvertedType
  defTyApp ty = do
    (f,x) <- lift $ splitAppTy_maybe ty
    (f',xs) <- convertTypeToSortType f
    (x',ys) <- convertTypeToSortType x
    return (appDef f' x',xs<>ys)

  defTyConApp :: Type -> ConvMonad ConvertedType
  defTyConApp ty = do
    (tcon, tys) <- lift $ splitTyConApp_maybe ty
    if isTypeFamilyTyCon tcon
    then do
      -- Type families are represented as smt functions
      recur <- traverse convertType tys
      let defConvTys = map fst recur
      let tvars = foldMap snd recur
      let convTcon = makeSMTName tcon
      let converted = "("++unwords (convTcon:defConvTys)++")"
      return (converted, tvars <> mempty{convLateDeps = mempty{lateTyFams = unitUniqSet tcon}})
    else do
      -- Type constructors are represented as (constructor ...)
      recur <- traverse convertTypeToSortType tys
      let defConvTys = map fst recur
      let tvars = foldMap snd recur
      let convTcon = "(constructor \"" ++ (makeSMTName tcon) ++ "\")"
      let converted = foldl appDef convTcon defConvTys
      return (converted, tvars)

  appDef :: String -> String -> String
  appDef f x = "(apply " ++ f ++ " " ++ x ++ ")"


-- * Converting A Single Kind
------------------------------------------------------------------------------


-- | Converts a Kind into a String and some kind variables, and
-- ADT type constructors that must be defined for the kind to
-- make sense
convertKind :: Kind -> ConvMonad (String, ([KdVar],UniqSet TyCon))
convertKind kind =
  case getTyVar_maybe kind of
    Just tvar ->
      return ((makeSMTName tvar), ([tvar],mempty))
    Nothing -> convKindTheories kind

convKindTheories :: Kind -> ConvMonad (String, ([KdVar],UniqSet TyCon))
convKindTheories kind = do
  EncodingData _ theories <- ask
  let kindConvFns = kindConvs theories
  case tryFns kindConvFns kind of
    Just (KdConvCont kholes kContin) -> do
      recur <- vecMapAll convertKind kholes
      let convHoles = fmap fst recur
      let holeVars = foldMap snd recur
      return (kContin convHoles, holeVars)
    Nothing
      | Just (tcon,xs) <- splitTyConApp_maybe kind
      , isAlgTyCon tcon -> do
          let name = makeSMTName tcon
          args' <- traverse convertKind xs
          let args = map fst args'
              deps = (foldMap snd args') <> (mempty,unitUniqSet tcon)
          case args of
            [] -> return (name, deps)
            _ -> return (("("++unwords (name:args)++")"), deps)
      | otherwise -> return ("Type", mempty) -- Kind defaulting

-- * A Common Helper Function

-- | In order, try the functions.
tryFns :: [a -> Maybe b] -> a -> Maybe b
tryFns [] _ = Nothing
tryFns (f:fs) a = case f a of
  Nothing -> tryFns fs a
  Just b -> Just b
tryFnsM :: [a -> ConvMonad b] -> a -> ConvMonad b
tryFnsM [] _ = lift Nothing
tryFnsM (f:fs) a = do
  env <- ask
  case runReaderT (f a) env of
    Nothing -> tryFnsM fs a
    Just b -> lift $ Just b




