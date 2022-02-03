-- http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

{-# LANGUAGE GADTs #-}

-- Caveats
-- * All type variables used must be unique, e.g. Forall x. (Forall x. x) is
-- forbidden and so is TApp (EForall x. x) (Forall x. x).
--
-- This is because it is difficult to incorporate type varaible
-- shadowing into the system as-is without doing a lot of changes. This
-- restriction prevents the nesting of type variables.
-- One concern relating to this might be the possibility of evaluation creating
-- nested type variables. However, it is at present impossible to do. If we have
-- some arbitrary expression (EForall x. e), we have to, through evaluation,
-- somehow insert into e -- an expression involving EForall x. Since type
-- variables are unique, the only -- expression suitable would be
-- Eforall x. e itself. This would require some sort of recursive type
-- (e.g. \x -> x x) which we do not support.
--
-- * All types used must be well-formed, e.g. all type variables are bound, etc.
-- No well-formedness checks exist at present (at least for type variables).

module STLC where

-- import Language.Haskell.Liquid.Equational
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Map (Map(..))
import qualified Data.Map as M
import Data.Bifunctor (bimap)
import Control.Monad.Trans.RWS.Lazy
import Control.Monad.Trans.Class (lift)

type TVar  = String
type Var   = String
type Label = String

-- -- Figure out the import for this
-- -- but also it isn't super necessary
type Proof = ()
data QED = QED

(***) :: a -> QED -> Proof
_ *** QED = ()
infixl 2 ***

{-@ (==.) :: x:a -> y:{a | x == y} -> {o:a | o == y && o == x} @-}
(==.) :: a -> a -> a
_ ==. x = x

(?) :: a -> Proof -> a
x ? _ = x

data Type
  = TInt
  | TBool
  | TVar TVar
  | TFun Type Type
  | TPair Type Type
  | TRecord TRecord
  | TForall TVar Type
  deriving (Eq, Show)

data TRecord
  = TRecordBind Label Type TRecord
  | TRecordEmp
  deriving (Eq, Show)

data Op
  = Add
  | Leq
  | And
  deriving (Eq, Show)

data ExprU
  = EUBool Bool
  | EUVar Var
  | EUFun Var Var ExprU
  | EUApp ExprU ExprU
  deriving (Eq, Show)

data Expr
  = EBool Bool               -- ^ 'EBool b'       is 'b'
  | EInt  Int                -- ^ 'EInt i'        is 'i'
  | EBin  Op Expr Expr       -- ^ 'EBin o e1 e2'  is 'e1 o e2'
  | EVar  Var                -- ^ 'EVar x'        is 'x'
  | EFun  Var Var Type Type Expr  -- ^ 'EFun f x t tret e'  is 'fun tret f(x:t) e'
  | EApp  Expr Expr          -- ^ 'EApp e1 e2'    is 'e1 e2'
  | EPair Expr Expr          -- ^ 'EPair e1 e2'   is '(e1, e2)'
  | EFst Expr                -- ^ 'EFst e1'       is 'fst e1'
  | ERecordBind Label Expr Expr -- 'ERecordBind'  is record extension
  | ERecordEmp               -- ^ 'ERecordEmp'    is '{}'
  | EForall TVar Expr        -- ^ 'EForall tv e'  is '/\ t. e'
  | ETApp Expr Type          -- ^ 'ETApp e t'     is type application
  deriving (Eq, Show)

data Val
  = VBool Bool
  | VInt  Int
  | VClos Var Var Expr VEnv
  | VForallClos TVar Expr VEnv
  | VPair Val Val
  | VRecordBind Label Val Val
  | VRecordEmp
  deriving (Eq, Show)

data Result
  = Result Val
  | Stuck
  | Timeout
  deriving (Eq, Show)

data VEnv
  = VBind Var Val VEnv
  -- | VTVarBind TVar Type VEnv
  | VEmp
  deriving (Eq, Show)

data TEnv
  = TBind Var Type TEnv
  | TTVarBind TVar TEnv
  | TEmp
  deriving (Eq, Show)

data TStore
  = TSBind Var Type TStore
  | TSEmp
  deriving (Eq, Show)


{-@ reflect mapTEnv @-}
mapTEnv :: (Type -> Type) -> TEnv -> TEnv
mapTEnv f (TBind var t tenv) = TBind var (f t) (mapTEnv f tenv)
mapTEnv f (TTVarBind tv tenv) = TTVarBind tv (mapTEnv f tenv)
mapTEnv f TEmp = TEmp

{-@ mapTEnvPreservesLookup :: x:Var -> g:TEnv -> t:{Type| lookupTEnv x g == Just t} -> f:(Type -> Type) -> { lookupTEnv x (mapTEnv f g) == Just (f t) } @-}

{-@ ple mapTEnvPreservesLookup @-}
mapTEnvPreservesLookup :: Var -> TEnv -> Type -> (Type -> Type) -> Proof
mapTEnvPreservesLookup _x TEmp _t _f = trivial ()
mapTEnvPreservesLookup x g@(TBind v_bound t_bound rest) t f
  | x == v_bound =   lookupTEnv x (mapTEnv f g)
                 ==. lookupTEnv x (TBind v_bound (f t_bound) (mapTEnv f rest))
                 ==. Just (f t_bound)
                 ==. Just (f t)
                 *** QED
  | otherwise = mapTEnvPreservesLookup x rest t f
mapTEnvPreservesLookup x (TTVarBind _ rest) t f = mapTEnvPreservesLookup x rest t f

{-@ reflect mapResult @-}
mapResult :: (Val -> Result) -> Result -> Result
mapResult f r = case r of
                  Stuck    -> Stuck
                  Timeout  -> Timeout
                  Result v -> f v

{-@ reflect seq2 @-}
-- seq2 :: (a -> b -> Result c) -> Result a -> Result b -> Result c
seq2 :: (Val -> Val -> Result) -> Result -> Result -> Result
seq2 f r1 r2 = case r1 of
                 Stuck     -> Stuck
                 Timeout   -> Timeout
                 Result v1 -> case r2 of
                                Stuck     -> Stuck
                                Timeout   -> Timeout
                                Result v2 -> f v1 v2

{-@ reflect substTVar @-}
substTVar :: TVar -> Type -> Type -> Type
substTVar x tSub t@(TVar x')
  | x == x'   = tSub
  | otherwise = t
substTVar x tSub (TFun t1 t2) = TFun (substTVar x tSub t1) (substTVar x tSub t2)
substTVar x tSub (TPair t1 t2) = TPair (substTVar x tSub t1) (substTVar x tSub t2)
substTVar x tSub (TRecord tr) = TRecord (substTVarRecord x tSub tr)
substTVar x tSub t@(TForall x' tInner)
  -- The forall shadows x
  | x == x'   = t
  | otherwise = TForall x' (substTVar x tSub tInner)
substTVar _ _ TInt  = TInt
substTVar _ _ TBool = TBool

{-@ reflect substTVarRecord @-}
substTVarRecord :: TVar -> Type -> TRecord -> TRecord
substTVarRecord x tSub (TRecordBind l t tr) = TRecordBind l (substTVar x tSub t) (substTVarRecord x tSub tr)
substTVarRecord _ _ TRecordEmp = TRecordEmp

{-@ reflect substTVarExpr @-}
substTVarExpr :: TVar -> Type -> Expr -> Expr
substTVarExpr x tSub e = case e of
  EBool _             -> e
  EInt _              -> e
  EBin op e1 e2       -> EBin op (substTVarExpr x tSub e1) (substTVarExpr x tSub e2)
  EVar _              -> e
  EFun f x' t tRet eInner  -> EFun f x' (substTVar x tSub t) (substTVar x tSub tRet) (substTVarExpr x tSub eInner)
  EApp e1 e2          -> EApp (substTVarExpr x tSub e1) (substTVarExpr x tSub e2)
  EPair e1 e2         -> EPair (substTVarExpr x tSub e1) (substTVarExpr x tSub e2)
  EFst eInner         -> EFst (substTVarExpr x tSub eInner)
  ERecordBind l e1 e2 -> ERecordBind l (substTVarExpr x tSub e1) (substTVarExpr x tSub e2)
  ERecordEmp          -> e
  EForall x' eInner
    -- the forall shadows x
    | x == x'   -> e
    | otherwise -> EForall x' (substTVarExpr x tSub eInner)
  ETApp eInner t      -> ETApp (substTVarExpr x tSub eInner) (substTVar x tSub t)

-- | Inference
-- Constraint-based inference taken from http://dev.stephendiehl.com/fun/006_hindley_milner.html

-- Constraint generation
type Constraint = (Type, Type)
type VarCount = Int
-- type InferM a = RWST TStore [Constraint] VarCount (Either String) a
data InferState = InferState
  { tStore :: TStore
  , constraints :: [Constraint]
  -- Count in unary because of GHC issues
  , varCount :: String 
  }

{-@ data ExprUExpr where
      EU_Bool :: b:Bool 
              -> Prop (ExprUExpr (EUBool b) (EBool b))
      EU_Var  :: x:Var
              -> Prop (ExprUExpr (EUVar x) (EVar x))
      EU_Fun  :: f:Var -> x:Var -> t1:Type -> eu:ExprU -> e:Expr -> t2:Type
              -> Prop (ExprUExpr eu e)
              -> Prop (ExprUExpr (EUFun f x eu) (EFun f x t1 t2 e))
      EU_App  :: eu1:ExprU -> eu2:ExprU -> e1:Expr -> e2:Expr
              -> Prop (ExprUExpr eu1 e1)
              -> Prop (ExprUExpr eu2 e2)
              -> Prop (ExprUExpr (EUApp eu1 eu2) (EApp e1 e2))
  @-}

data ExprUExprP where
  ExprUExpr :: ExprU -> Expr -> ExprUExprP

data ExprUExpr where
  EU_Bool :: Bool -> ExprUExpr
  EU_Var  :: Var -> ExprUExpr
  EU_Fun  :: Var -> Var -> Type -> ExprU -> Expr -> Type -> ExprUExpr -> ExprUExpr
  EU_App  :: ExprU -> ExprU -> Expr -> Expr -> ExprUExpr -> ExprUExpr -> ExprUExpr

-- liquidhaskell can't find ++ so I guess we'll roll our own
{-@ reflect append @-}
append :: [a] -> [a] -> [a]
append [] bs = bs
append (a:as) bs = a : (append as bs)

-- same with map
{-@ reflect myMap @-}
myMap :: (a -> b) -> [a] -> [b]
myMap _ [] = []
myMap f (a:as) = f a : myMap f as

-- same with bimap
{-@ reflect myBimap @-}
myBimap :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
myBimap f g (x, y) = (f x, g y)

data MyEither a b = MyLeft a | MyRight b
{-@ data MyEither a b where
      MyLeft  :: a -> MyEither a b
      MyRight :: b -> MyEither a b
  @-}

{-@ reflect right @-}
right :: Type -> Either String Type
right t = Right t

{-@ reflect left @-}
left :: String -> Either String Type
left a = Left a

{-@ reflect lookupTStore @-}
lookupTStore :: Var -> TStore -> Either String Type
lookupTStore x TSEmp = left "lookupTStore: lookup failed"
lookupTStore x (TSBind v t ts)
  | x == v    = right t
  | otherwise = lookupTStore x ts

{-@ reflect freshTVar @-}
freshTVar :: InferState -> (InferState, Type)
freshTVar (InferState env consts varCount) = 
  (InferState env consts (varCount `append` varCount), TVar varCount)

{-@ reflect makeConstraint @-}
makeConstraint :: InferState -> Type -> Type -> InferState
makeConstraint (InferState env consts varCount) t1 t2 = 
  InferState env ((t1, t2):consts) varCount


data GenConstraintsResult where
  GCRight :: InferState -> ExprU -> Expr -> Type -> ExprUExpr -> GenConstraintsResult
  GCLeft  :: String -> GenConstraintsResult

{-@ data GenConstraintsResult where
      GCRight :: is:InferState -> eu:ExprU -> e:Expr -> t:Type
              -> Prop (ExprUExpr eu e)
              -> GenConstraintsResult
      GCLeft  :: String
              -> GenConstraintsResult
  @-}

{-@ reflect genConstraints @-}
-- {-@ genConstraints :: is0:InferState -> eu:ExprU 
--      -> Either String (e::Expr, (InferState, Type, {eu_e:ExprUExpr | prop eu_e == ExprUExpr eu e}))
--   @-}
{-@ genConstraints :: is0:InferState -> eu:ExprU 
     -> GenConstraintsResult
  @-}
genConstraints :: InferState -> ExprU -> GenConstraintsResult
genConstraints is eu@(EUBool b) = GCRight is eu (EBool b) TBool (EU_Bool b)
genConstraints is eu@(EUVar v) = case lookupTStore v env of
  Right tp -> GCRight is eu (EVar v) tp (EU_Var v)
  Left err -> GCLeft err
  where
    (InferState env _ _) = is
genConstraints is0 eu@(EUFun f x _) = case genConstraints is2 eu of
  GCRight (InferState _ newConsts newVc) _ e tp eu_e ->
    -- Return returnTV isntead of tp
    -- Add constraint that returnTV == tp
    GCRight (InferState originalEnv newConsts newVc) eu (EFun f x tv tp e) (TFun tv tp) (EU_Fun f x tv eu e tp eu_e)
  GCLeft err -> GCLeft err
  where
    (InferState originalEnv consts vc, tv) = freshTVar is0
    -- gen returnTV and bind to f
    is2 = InferState (TSBind x tv originalEnv) consts vc
genConstraints is0 eu@(EUApp eu1 eu2) = case genConstraints is0 eu1 of
  GCRight is1 eu1' e1 t1 eu1_e1 -> case genConstraints is1 eu2 of
    GCRight is2 eu2' e2 t2 eu2_e2 ->
      let (is3, tv) = freshTVar is2
          is4 = makeConstraint is3 t1 (TFun t2 tv) in
        GCRight is4 eu (EApp e1 e2) tv (EU_App eu1' eu2' e1 e2 eu1_e1 eu2_e2)
    GCLeft err -> GCLeft err
  GCLeft err -> GCLeft err
genConstraints _ _ = error "this shouldn't happen"

-- Constraint solving
data Subst
  = SEmp
  | SBind TVar Type Subst
type SolveM a = Either String a

{-@ reflect mapSubst @-}
mapSubst :: (Type -> Type) -> Subst -> Subst
mapSubst f SEmp = SEmp
mapSubst f (SBind tv tp subst) = SBind tv (f tp) (mapSubst f subst)

{-@ reflect findWithDefaultSubst @-}
findWithDefaultSubst :: Type -> TVar -> Subst -> Type
findWithDefaultSubst def _ SEmp = def
findWithDefaultSubst def searchTv (SBind tv tp subst)
  | searchTv == tv = tp
  | otherwise      = findWithDefaultSubst def searchTv subst

{-@ reflect insertSubst @-}
insertSubst :: TVar -> Type -> Subst -> Subst
insertSubst tv tp SEmp = SBind tv tp SEmp
insertSubst tv tp (SBind tv' tp' subst)
  | tv == tv' = SBind tv tp (insertSubst tv tp subst)
  | otherwise = SBind tv' tp' (insertSubst tv tp subst)

{-@ reflect unionSubst @-}
unionSubst :: Subst -> Subst -> Subst
unionSubst SEmp s = s
unionSubst (SBind tv tp subst) s = unionSubst subst (insertSubst tv tp s)

{-@ reflect composeSubst @-}
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = unionSubst (mapSubst (applySubst s1) s2) s1

{-@ reflect applySubst @-}
applySubst :: Subst -> Type -> Type
applySubst s t@(TVar tv) = findWithDefaultSubst t tv s
applySubst s t@TBool = t
applySubst s (TFun t1 t2) = TFun (applySubst s t1) (applySubst s t2)
-- TODO: left empty for totality, fill in with other cases
applySubst s t = t

{-@ reflect applySubstExpr @-}
applySubstExpr :: Subst -> Expr -> Expr
applySubstExpr s (EFun f x tArg tRet e) = 
  EFun f x (applySubst s tArg) (applySubst s tRet) (applySubstExpr s e)
applySubstExpr s (ETApp e t) = 
  ETApp (applySubstExpr s e) (applySubst s t)
applySubstExpr s e = e

{-@ reflect bind @-}
bind ::  TVar -> Type -> SolveM (Subst, [Constraint])
bind tv t | t == TVar tv = Right (SEmp, []) 
          | tv `S.member` freeTVars t = Left "occurs check failed"
          | otherwise = Right (SBind tv t SEmp, [])

{-@ reflect freeTVars @-}
freeTVars :: Type -> Set TVar
freeTVars (TVar tv) = S.singleton tv
freeTVars (TFun t1 t2) = freeTVars t1 `S.union` freeTVars t2
freeTVars (TBool) = S.empty
freeTVars (TInt) = S.empty
-- TODO: left empty for totality, fill in with other cases
freeTVars _ = S.empty

{-@ reflect unify @-}
unify :: Type -> Type -> SolveM (Subst, [Constraint])
unify t1 t2
  | t1 == t2 = Right (SEmp, [])
unify (TVar tv) t2 = bind tv t2
unify t1 (TVar tv) = bind tv t1
unify (TFun a1 a2) (TFun b1 b2) = case unify a1 b1 of
  Right (s1, cs1) -> case unify (applySubst s1 a2) (applySubst s1 b2) of
    Right (s2, cs2) ->
      Right (composeSubst s1 s2, cs1 `append` cs2)
    Left err -> Left err
  Left err -> Left err
unify _ _ = Left "unification failed"

{-@ reflect solveConstraints @-}
solveConstraints :: Subst -> [Constraint] -> SolveM Subst
solveConstraints s [] = Right s
solveConstraints s0 ((t1,t2):cs0) = case unify t1 t2 of
  Right (s1, cs1) ->
    solveConstraints (composeSubst s1 s0) (cs1 `append` myMap (myBimap (applySubst s1) (applySubst s1)) cs0)
  Left err -> Left err


-- TODO for next week
-- 1. Fix genConstraints to use the proper type (ask in LH slack / use a new
-- datatype instead of tuples)
-- 2. Move unnecessary code (interpreter) into a separate file.
-- 3. Try to generate ExprTy in the genConstraints.
-- 4. (Maybe) Persist the generated ExprUExpr through substitution and write a
-- proof that goes from untype expression all the way through inference to a
-- typed expression.

{-@ reflect infer @-}
infer :: TStore -> ExprU -> Either String Expr
infer ts eu = case genConstraints (InferState ts [] "0") eu of
  GCRight (InferState _ constraints _) _ eUnsolved tUnsolved _ -> case solveConstraints SEmp constraints of
    Right subst ->
      Right $ applySubstExpr subst eUnsolved --, applySubst subst tUnsolved)
    Left err -> Left err
  GCLeft err -> Left err

-- genConstraints ... (EUBool b) == Right (_, e, _)
-- => e == EBool b
--
-- genConstraints ... (EUFun f x eu) == Right (_, e, _)
-- => e == EFun f x _ _ e

{-@ erasure
      :: eu:ExprU
      -> e:Expr
      -> Prop (ExprUExpr eu e)
      -> {erase e == eu}
  @-}
erasure :: ExprU -> Expr -> ExprUExpr -> Proof
erasure eu@(EUBool b) e@(EBool _) (EU_Bool _)
  =   erase e 
  ==. EUBool b
  ==. eu
  *** QED
erasure eu@(EUVar v) e@(EVar _) (EU_Var _)
  =   erase e 
  ==. EUVar v
  ==. eu
  *** QED
erasure (EUFun f x eu) (EFun _ _ _ _ e) (EU_Fun _ _ _ _ _ _ eu_e)
  = erasure eu e eu_e
erasure (EUApp eu1 eu2) (EApp e1 e2) (EU_App _ _ _ _ eu1_e1 eu2_e2)
  = erasure eu1 e1 eu1_e1 ? erasure eu2 e2 eu2_e2
erasure (EUVar {}) _ (EU_Bool {}) = trivial ()
erasure (EUFun {}) _ (EU_Bool {}) = trivial ()
erasure (EUApp {}) _ (EU_Bool {}) = trivial ()
erasure (EUBool {}) _ (EU_Var {}) = trivial ()
erasure (EUFun {}) _ (EU_Var {}) = trivial ()
erasure (EUApp {}) _ (EU_Var {}) = trivial ()
erasure (EUBool {}) _ (EU_Fun {}) = trivial ()
erasure (EUVar {}) _ (EU_Fun {}) = trivial ()
erasure (EUApp {}) _ (EU_Fun {}) = trivial ()
erasure (EUBool {}) _ (EU_App {}) = trivial ()
erasure (EUVar {}) _ (EU_App {}) = trivial ()
erasure (EUFun {}) _ (EU_App {}) = trivial ()
-- TODO: Write the above ^
-- (with time): see how to return an ExprTy in genConstraints

{-@ reflect erase @-}
erase :: Expr -> ExprU
erase (EBool b) = EUBool b
erase (EVar v) = EUVar v
erase (EFun f x _ _ e) = EUFun f x (erase e)
erase (EApp e1 e2) = EUApp (erase e1) (erase e2)
-- TODO: Add other cases
erase _ = EUBool False

-- {-@ inversion :: p1:{infer st (EUFun f x eu) == Right e_fun} 
--               -> {infer st eu == Right e}
--   @-}

-- {-@ inferRespectsErasure :: eu:ExprU
--      -> st:TStore
--      -> e: Expr
--      -> p1:{infer st eu == Right e}
--      -> {erase (infer st eu) == Right eu}
--   @-}
-- inferRespectsErasure :: ExprU -> TStore -> Expr -> Proof -> Proof
-- inferRespectsErasure eu ts e inferSuccess = case eu of
--   EUBool b -> erase (infer st (EUBool b))
--               ==. erase (Right (EBool b))
--               ==. Right (EUBool b)
-- {-@ annotationProof :: eu:ExprU 
--       -> st:TStore
--       -> g:TEnv
--       -> e:Expr 
--       -> t:Type
--       -> p1:{infer st g eu == Just e}
--       -> p2:{erase e == eu}
--       -> p3:{readType e == Just t}
--       -> Prop (ExprTy g e t)
--   @-}
annotationProof = undefined

data TResult
  = TResult Type
  | TStuck

{-@ reflect readType @-}
readType :: TEnv -> Expr -> TResult
readType _ (EBool _)           = TResult TBool
readType _ (EInt _)            = TResult TInt
readType _ (ERecordEmp)        = TResult (TRecord TRecordEmp)
readType g (EBin op arg1 arg2) = case (op, readType g arg1, readType g arg2) of
  (Add, TResult TInt, TResult TInt)   -> TResult TInt
  (Leq, TResult TInt, TResult TInt)   -> TResult TBool
  (And, TResult TBool, TResult TBool) -> TResult TBool
  _                                   -> TStuck
readType g (EVar var)          = case lookupTEnv var g of
  Just t  -> TResult t
  Nothing -> TStuck
readType g (EFun f x tArg tRet eInner) = case readType (TBind x tArg (TBind f (TFun tArg tRet) g)) eInner of
  TResult _ -> TResult (TFun tArg tRet)
  TStuck   -> TStuck
readType g (EApp e1 e2)        = case (readType g e1, readType g e2) of
  (TResult (TFun t1 t2), TResult t)
    | t == t1 -> TResult t2
  _           -> TStuck
readType g (EPair e1 e2)       = case (readType g e1, readType g e2) of
  (TResult t1, TResult t2) -> TResult (TPair t1 t2)
  _                        -> TStuck
readType g (EFst e)            = case readType g e of
  TResult (TPair t1 _) -> TResult t1
  _                    -> TStuck
readType g (ERecordBind l e1 e2) = case (readType g e1, readType g e2) of
  (TResult t1, TResult (TRecord tr)) -> TResult (TRecord (TRecordBind l t1 tr))
  _                                  -> TStuck
readType g (EForall tv e)        = case (readType (TTVarBind tv g) e) of
  TResult t -> TResult (TForall tv t)
  _         -> TStuck
readType g (ETApp e t)          = case (readType g e) of
  TResult (TForall tv tp) -> TResult (substTVar tv t tp)
  _                       -> TStuck

--------------------------------------------------------------------------------
-- | Evaluator
--------------------------------------------------------------------------------

{-@ reflect lookupVEnv @-}
lookupVEnv :: Var -> VEnv -> Maybe Val
lookupVEnv x VEmp              = Nothing
lookupVEnv x (VBind y v env)   = if x == y then Just v else lookupVEnv x env
-- lookupVEnv x (VTVarBind _ _ env) = lookupVEnv x env

{-@ reflect eval @-}
eval :: VEnv -> Expr -> Result
eval _   (EBool b)    = Result (VBool b)
eval _   (EInt  n)    = Result (VInt  n)
eval s (EBin o e1 e2) = seq2 (evalOp o) (eval s e1) (eval s e2)
eval s (EVar x)       = case lookupVEnv x s of
                          Nothing -> Stuck
                          Just v  -> Result v
eval s (EFun f x t tRet e) = Result (VClos f x e s)
eval s (EApp e1 e2)   = seq2 evalApp (eval s e1) (eval s e2)
eval s (EPair e1 e2)  = seq2 evalPair (eval s e1) (eval s e2)
eval s (EFst e)       = mapResult evalFst (eval s e)
eval s (ERecordBind l e er)   = seq2 (evalRecord l) (eval s e) (eval s er)
eval s ERecordEmp = Result VRecordEmp
eval s (EForall tv e) = Result (VForallClos tv e s)
eval s (ETApp e t) = mapResult (evalTApp t) (eval s e)

{-@ reflect evalPair @-}
evalPair :: Val -> Val -> Result
evalPair v1 v2 = Result (VPair v1 v2)

{-@ reflect evalApp @-}
evalApp :: Val -> Val -> Result
evalApp v1@(VClos f x e s) v2 = eval (VBind x v2 (VBind f v1 s)) e
evalApp _                  _  = Stuck

{-@ reflect evalFst @-}
evalFst :: Val -> Result
evalFst (VPair v1 _) = Result v1
evalFst _ = Stuck

{-@ reflect evalRecord @-}
evalRecord :: Label -> Val -> Val -> Result
evalRecord l v vr@(VRecordBind _ _ _) = Result (VRecordBind l v vr)
evalRecord l v vr@(VRecordEmp) = Result (VRecordBind l v vr)
evalRecord _ v _ = Stuck

-- flipped because of SMTLib/LH issues with anonymous functions
{-@ reflect evalTApp @-}
evalTApp :: Type -> Val -> Result
evalTApp t (VForallClos x e s) = eval s (substTVarExpr x t e)
evalTApp _ _ = Stuck

{-@ reflect evalOp @-}
evalOp :: Op -> Val -> Val -> Result
evalOp Add (VInt n1)  (VInt n2)  = Result (VInt  (n1 +  n2))
evalOp Leq (VInt n1)  (VInt n2)  = Result (VBool (n1 <= n2))
evalOp And (VBool b1) (VBool b2) = Result (VBool (b1 && b2))
evalOp _   _          _          = Stuck

--------------------------------------------------------------------------------
-- | Tests before proofs
--------------------------------------------------------------------------------

tests  = [ e1              -- 15
         , EBin Leq e1 e1  -- True
         , EBin And e1 e1  -- Stuck!
         ]
  where
    e1 = EBin Add (EInt 5) (EInt 10)

--------------------------------------------------------------------------------
-- | Typing Results
--------------------------------------------------------------------------------

{- [ |- r : T ]


    |- v : T
  -------------------- [R_Res]
    |- Result v : T

  -------------------- [R_Time]
    |- Timeout  : T

-}

{-@ data ResTy where
      R_Res  :: x:Val -> t:Type -> Prop (ValTy x t) -> Prop (ResTy (Result x) t)
      R_Time :: t:Type -> Prop (ResTy Timeout t)
  @-}

data ResTyP where
  ResTy  :: Result -> Type -> ResTyP

data ResTy where
  R_Res  :: Val -> Type -> ValTy -> ResTy
  R_Time :: Type -> ResTy

--------------------------------------------------------------------------------
-- | Typing Values
--------------------------------------------------------------------------------

{- [ |- v : T ]

    ----------------------- [V_Bool]
      |- VBool b : TBool

    ----------------------- [V_Int]
      |- VInt i : TInt

    g |- s  (x,t1), (f,t1->t2),g |- e : t2
    --------------------------------------- [V_Clos]
      |- VClos f x e s : t1 -> t2

          |- v1 : t1  |- v2 : t2
    ------------------------------ [V_Pair]
      |- VPair (v1, t1) : (t1, t2)

    --------------------------------------- [V_RecordEmp]
      |- VRecordEmp : TRecord (TRecordEmp)

      |- val : t     |- vr : (TRecord tr)
    ---------------------------------------- [V_RecordBind]
      |- VRecordBind l val vr : TRecord (TRecordBind l t tr)

      g |- s    g, tv |- v : t
    ----------------------------- [V_Forall]  TODO: Change to a closure akin to V_Clos
      |- VForall tv e : TForall tv t

 -}

{-@ data ValTy where
      V_Bool :: b:Bool -> Prop (ValTy (VBool b) TBool)
      V_Int  :: i:Int  -> Prop (ValTy (VInt i)  TInt)
      V_Clos :: g:TEnv -> s:VEnv -> f:Var -> x:Var -> t1:Type -> t2:Type -> e:Expr
             -> Prop (StoTy g s)
             -> Prop (ExprTy (TBind x t1 (TBind f (TFun t1 t2) g)) e t2)
             -> Prop (ValTy (VClos f x e s) (TFun t1 t2))
      V_ForallClos :: g:TEnv -> s:VEnv -> x:TVar -> t:Type -> e:Expr
                   -> Prop (StoTy g s)
                   -> Prop (ExprTy (TTVarBind x g) e t)
                   -> Prop (ValTy (VForallClos x e s) (TForall x t))
      V_Pair :: v1:Val -> v2:Val -> t1:Type -> t2:Type
             -> Prop (ValTy v1 t1)
             -> Prop (ValTy v2 t2)
             -> Prop (ValTy (VPair v1 v2) (TPair t1 t2))
      V_RecordBind :: l:Label -> val:Val -> rcd:Val -> t:Type -> tr:TRecord
                   -> Prop (ValTy val t)
                   -> Prop (ValTy rcd (TRecord tr))
                   -> Prop (ValTy (VRecordBind l val rcd) (TRecord (TRecordBind l t tr)))
      V_RecordEmp :: Prop (ValTy VRecordEmp (TRecord TRecordEmp))
  @-}

data ValTyP where
  ValTy  :: Val -> Type -> ValTyP

data ValTy where
  V_Bool   :: Bool -> ValTy
  V_Int    :: Int  -> ValTy
  V_Clos   :: TEnv -> VEnv -> Var -> Var -> Type -> Type -> Expr -> StoTy -> ExprTy  -> ValTy
  V_ForallClos :: TEnv -> VEnv -> TVar -> Type -> Expr -> StoTy -> ExprTy  -> ValTy
  V_Pair   :: Val -> Val -> Type -> Type -> ValTy -> ValTy -> ValTy
  V_RecordBind :: Label -> Val -> Val -> Type -> TRecord -> ValTy -> ValTy -> ValTy
  V_RecordEmp :: ValTy

--------------------------------------------------------------------------------
-- | Typing Stores
--------------------------------------------------------------------------------

{- [ G |- S ]

   ------------------------[S_Emp]
   TEmp |- VEmp

      |- v : t   g |- s
   ------------------------[S_Bind]
   (x, t), g |- (x, v), s

      g |- s
   ------------------------[S_BindTVar]
   x, g |- s

 -}

{-@ data StoTy where
      S_Emp  :: Prop (StoTy TEmp VEmp)
      S_Bind :: x:Var -> t:Type -> val:Val -> g:TEnv -> s:VEnv
             -> Prop (ValTy val t)
             -> Prop (StoTy g   s)
             -> Prop (StoTy (TBind x t g) (VBind x val s))
      S_TVarBind :: x:TVar -> g:TEnv -> s:VEnv
                 -> Prop (StoTy g s)
                 -> Prop (StoTy (TTVarBind x g) s)
  @-}

data StoTyP where
  StoTy  :: TEnv -> VEnv -> StoTyP

data StoTy where
  S_Emp  :: StoTy
  S_Bind :: Var -> Type -> Val -> TEnv -> VEnv -> ValTy -> StoTy -> StoTy
  S_TVarBind :: TVar -> TEnv -> VEnv -> StoTy -> StoTy

--------------------------------------------------------------------------------
-- | Typing Expressions
--------------------------------------------------------------------------------

{-@ reflect opIn @-}
opIn :: Op -> Type
opIn Add = TInt
opIn Leq = TInt
opIn And = TBool

{-@ reflect opOut @-}
opOut :: Op -> Type
opOut Add = TInt
opOut Leq = TBool
opOut And = TBool

{-@ reflect lookupTEnv @-}
lookupTEnv :: Var -> TEnv -> Maybe Type
lookupTEnv x TEmp             = Nothing
lookupTEnv x (TBind y v env)  = if x == y then Just v else lookupTEnv x env
lookupTEnv x (TTVarBind _ env)  = lookupTEnv x env


{-

  --------------------------------------[E-Bool]
    G |- EBool b : TBool

  --------------------------------------[E-Int]
    G |- EInt n  : TInt

    lookupTEnv x G = Just t
  --------------------------------------[E-Var]
    G |- Var x  : t

    G |- e1 : opIn o  G |- e2 : opIn o
  --------------------------------------[E-Bin]
    G |- EBin o e1 e2 : opOut o


    (x,t1), (f, t1->t2), G |- e : t2
  --------------------------------------[E-Fun]
    G |- EFun f x t1 t2 e : t1 -> t2

    G |- e1 : t1 -> t2   G |- e2 : t1
  --------------------------------------[E-App]
    G |- EApp e1 e2 : t2

  --------------------------------------[E-RecordEmp]
    G |- ERecordEmp : TRecord TRecordEmp

    G |- e : t   G |- er : TRecord tr
  --------------------------------------[E-RecordBind]
    G |- ERecordBind l e er : TRecord (TRecordBind l t tr)

         G, tv |- e : t
  ----------------------------- [E_Forall]
    G |- EForall tv e : TForall tv t

    G |- e : TForall tv t  G |- t'
  ----------------------------- [E_TApp]
    G |- ETApp e t' : t[tv -> t']

-}

-- TODO
-- Add a Type well-formedness check wherever types are introduced (E_Fun t1,
-- E_TApp t), add a lemma that says if G |- e : t, then G |- t.

{-@ data ExprTy where
      E_Bool :: g:TEnv -> b:Bool
             -> Prop (ExprTy g (EBool b) TBool)
      E_Int  :: g:TEnv -> i:Int
             -> Prop (ExprTy g (EInt i)  TInt)
      E_Bin  :: g:TEnv -> o:Op -> e1:Expr -> e2:Expr
             -> Prop (ExprTy g e1 (opIn o))
             -> Prop (ExprTy g e2 (opIn o))
             -> Prop (ExprTy g (EBin o e1 e2) (opOut o))
      E_Var  :: g:TEnv -> x:Var -> t:{Type| lookupTEnv x g == Just t}
             -> Prop (ExprTy g (EVar x) t)
      E_Fun  :: g:TEnv -> f:Var -> x:Var -> t1:Type -> e:Expr -> t2:Type
             -> Prop (ExprTy (TBind x t1 (TBind f (TFun t1 t2) g)) e t2)
             -> Prop (ExprTy g (EFun f x t1 t2 e) (TFun t1 t2))
      E_App  :: g:TEnv -> e1:Expr -> e2:Expr -> t1:Type -> t2:Type
             -> Prop (ExprTy g e1 (TFun t1 t2))
             -> Prop (ExprTy g e2 t1)
             -> Prop (ExprTy g (EApp e1 e2) t2)
      E_Pair :: g:TEnv -> e1:Expr -> e2:Expr -> t1:Type -> t2:Type
             -> Prop (ExprTy g e1 t1)
             -> Prop (ExprTy g e2 t2)
             -> Prop (ExprTy g (EPair e1 e2) (TPair t1 t2))
      E_Fst  :: g:TEnv -> e:Expr -> t1:Type -> t2:Type
             -> Prop (ExprTy g e (TPair t1 t2))
             -> Prop (ExprTy g (EFst e) t1)
      E_RecordBind :: g:TEnv -> l:Label -> e:Expr -> er:Expr -> t:Type -> tr:TRecord
                   -> Prop (ExprTy g e t)
                   -> Prop (ExprTy g er (TRecord tr))
                   -> Prop (ExprTy g (ERecordBind l e er) (TRecord (TRecordBind l t tr)))
      E_RecordEmp :: g:TEnv -> Prop (ExprTy g ERecordEmp (TRecord TRecordEmp))
      E_Forall :: g:TEnv -> x:TVar -> e:Expr -> t:Type
             -> Prop (ExprTy (TTVarBind x g) e t)
             -> Prop (ExprTy g (EForall x e) (TForall x t))
      E_TApp :: g:TEnv -> e:Expr -> x:TVar -> t_x:Type -> t_fa:Type
               -> Prop (ExprTy g e (TForall x t_fa))
               -> Prop (ExprTy g (ETApp e t_x) (substTVar x t_x t_fa))
  @-}

data ExprTyP where
  ExprTy :: TEnv -> Expr -> Type -> ExprTyP

data ExprTy where
  E_Bool   :: TEnv -> Bool -> ExprTy
  E_Int    :: TEnv -> Int  -> ExprTy
  E_Var    :: TEnv -> Var  -> Type -> ExprTy
  E_Bin    :: TEnv -> Op   -> Expr -> Expr -> ExprTy -> ExprTy -> ExprTy
  E_Fun    :: TEnv -> Var -> Var -> Type -> Expr -> Type -> ExprTy -> ExprTy
  E_App    :: TEnv -> Expr -> Expr -> Type -> Type -> ExprTy -> ExprTy -> ExprTy
  E_Pair   :: TEnv -> Expr -> Expr -> Type -> Type -> ExprTy -> ExprTy -> ExprTy
  E_Fst    :: TEnv -> Expr -> Type -> Type -> ExprTy -> ExprTy
  E_RecordBind :: TEnv -> Label -> Expr -> Expr -> Type -> TRecord -> ExprTy -> ExprTy -> ExprTy
  E_RecordEmp :: TEnv -> ExprTy
  E_Forall :: TEnv -> TVar -> Expr -> Type -> ExprTy -> ExprTy
  E_TApp :: TEnv -> Expr -> TVar -> Type -> Type -> ExprTy -> ExprTy

--------------------------------------------------------------------------------
-- | Lemma 1: "evalOp_safe"
--------------------------------------------------------------------------------

{-@ reflect isValTy @-}
isValTy :: Val -> Type -> Bool
isValTy (VInt _)  TInt  = True
isValTy (VBool _) TBool = True
isValTy _         _     = False

{-@ propValTy :: o:Op -> w:Val -> Prop (ValTy w (opIn o)) -> { w' : Val | w = w' && isValTy w' (opIn o) } @-}
propValTy :: Op -> Val -> ValTy -> Val
propValTy Add w (V_Int _) = w
propValTy Leq w (V_Int _)  = w
propValTy And w (V_Bool _) = w

{-@ evalOp_safe
      :: o:Op -> v1:{Val | isValTy v1 (opIn o) } -> v2:{Val | isValTy v2 (opIn o) }
      -> (v :: Val, ( {y:() | evalOp o v1 v2 == Result v} , {z:ValTy | prop z = ValTy v (opOut o)}))
  @-}
evalOp_safe :: Op -> Val -> Val -> (Val, ((), ValTy))
evalOp_safe Add (VInt n1) (VInt n2)   = (VInt n, ((), V_Int n))   where n = n1 + n2
evalOp_safe Leq (VInt n1) (VInt n2)   = (VBool b, ((), V_Bool b)) where b = n1 <= n2
evalOp_safe And (VBool b1) (VBool b2) = (VBool b, ((), V_Bool b)) where b = b1 && b2



{-@ evalOp_res_safe
      :: o:Op -> r1:Result -> r2:Result
      -> Prop (ResTy r1 (opIn o))
      -> Prop (ResTy r2 (opIn o))
      -> Prop (ResTy (seq2 (evalOp o) r1 r2) (opOut o))
  @-}
evalOp_res_safe :: Op -> Result -> Result -> ResTy -> ResTy -> ResTy
evalOp_res_safe o (Result v1) (Result v2) (R_Res _ t1 vt1) (R_Res _ t2 vt2)
  = case evalOp_safe o (propValTy o v1 vt1) (propValTy o v2 vt2) of
      (v, (_, vt)) -> R_Res v (opOut o) vt
evalOp_res_safe o _ _  (R_Time t1) _
  = R_Time (opOut o)
evalOp_res_safe o _ _  _ (R_Time t2)
  = R_Time (opOut o)

--------------------------------------------------------------------------------
-- | Lemma 2: "lookup_safe"
--------------------------------------------------------------------------------
{-@ lookup_safe :: g:TEnv -> s:VEnv -> x:Var -> t:{Type | lookupTEnv x g == Just t}
                -> Prop (StoTy g s)
                -> (w :: Val, ({z:() | lookupVEnv x s ==  Just w} , {z:ValTy | prop z = ValTy w t} ))
  @-}
lookup_safe :: TEnv -> VEnv -> Var -> Type -> StoTy -> (Val, ((), ValTy))
lookup_safe _ _ _ _ S_Emp
  = trivial ()
lookup_safe g s x t (S_Bind y yt yv g' s' yvt gs')
  | x == y
  = (yv, ((), yvt))
  | otherwise
  = lookup_safe g' s' x t gs'
lookup_safe _ _ x t (S_TVarBind _ g' s' gs')
  = lookup_safe g' s' x t gs'

--------------------------------------------------------------------------------
-- | Lemma 3: "app_safe"
--------------------------------------------------------------------------------

{-@ substTVarContext
      :: g:TEnv -> s:VEnv
      -> Prop (StoTy g s)
      -> x:TVar -> t_x:Type
      -> ( g' :: {y:TEnv | g'=mapTEnv (substTVar x t_x) g}
         , {z:StoTy | prop z = StoTy g' s}
         )
  @-}
substTVarContext :: TEnv -> VEnv -> StoTy -> TVar -> Type -> (TEnv,StoTy)
substTVarContext g@TEmp s@VEmp gs@S_Emp _ _ = (g, gs)
-- how to do substitution on ValTy?
substTVarContext (TBind _ t g) (VBind _ v s) (S_Bind x_var _ _ _ _ v_t gs) x t_x = undefined
substTVarContext (TTVarBind _ g) s (S_TVarBind x_tvar _ _ gs) x t_x =
  let (g', gs') = substTVarContext g s gs x t_x
   in (TTVarBind x_tvar g', S_TVarBind x_tvar g' s gs')

{-@ fixSubstPair
      :: g:TEnv -> e:Expr -> t1:Type -> t2:Type -> x:TVar -> t_x:Type
      -> Prop (ExprTy g e (substTVar x t_x (TPair t1 t2)))
      -> Prop (ExprTy g e (TPair (substTVar x t_x t1) (substTVar x t_x t2)))
  @-}
fixSubstPair :: TEnv -> Expr -> Type -> Type -> TVar -> Type -> ExprTy -> ExprTy
fixSubstPair _ _ _ _ _ _ e_t1_t2 = e_t1_t2

{-@ substTForallVarNotEqP
      :: x_fa:TVar -> t_fa:Type -> x_subst:TVar -> t_subst:Type
      -> p:{x_fa != x_subst}
      -> {substTVar x_subst t_subst (TForall x_fa t_fa) == TForall x_fa (substTVar x_subst t_subst t_fa)}
  @-}
substTForallVarNotEqP :: TVar -> Type -> TVar -> Type -> Proof -> Proof
substTForallVarNotEqP x_fa t_fa x_subst t_subst varNotEqP
  =   substTVar x_subst t_subst (TForall x_fa t_fa)
  ==. TForall x_fa (substTVar x_subst t_subst t_fa) ? varNotEqP
  *** QED

{-@ substTForallVarEqP
      :: x_fa:TVar -> t_fa:Type -> x_subst:TVar -> t_subst:Type
      -> p:{x_fa == x_subst}
      -> {substTVar x_subst t_subst (TForall x_fa t_fa) == TForall x_fa t_fa}
  @-}
substTForallVarEqP :: TVar -> Type -> TVar -> Type -> Proof -> Proof
substTForallVarEqP x_fa t_fa x_subst t_subst varEqP
  =   substTVar x_subst t_subst (TForall x_fa t_fa)
  ==. TForall x_fa t_fa ? varEqP
  *** QED

{-@ substEForallVarNotEqP
      :: x_fa:TVar -> e_fa:Expr -> x_subst:TVar -> t_subst:Type
      -> p:{x_fa != x_subst}
      -> {substTVarExpr x_subst t_subst (EForall x_fa e_fa) == EForall x_fa (substTVarExpr x_subst t_subst e_fa)}
  @-}
substEForallVarNotEqP :: TVar -> Expr -> TVar -> Type -> Proof -> Proof
substEForallVarNotEqP x_fa e_fa x_subst t_subst varNotEqP
  =   substTVarExpr x_subst t_subst (EForall x_fa e_fa)
  ==. EForall x_fa (substTVarExpr x_subst t_subst e_fa) ? varNotEqP
  *** QED

{-@ substEForallVarEqP
      :: x_fa:TVar -> e_fa:Expr -> x_subst:TVar -> t_subst:Type
      -> p:{x_fa == x_subst}
      -> {substTVarExpr x_subst t_subst (EForall x_fa e_fa) == EForall x_fa e_fa}
  @-}
substEForallVarEqP :: TVar -> Expr -> TVar -> Type -> Proof -> Proof
substEForallVarEqP x_fa e_fa x_subst t_subst varEqP
  =   substTVarExpr x_subst t_subst (EForall x_fa e_fa)
  ==. EForall x_fa e_fa ? varEqP
  *** QED

{-@ fixSubstTForallEq
      :: t:Type -> x_subst:TVar -> t_subst:Type
      -> p:{t == substTVar x_subst t_subst t}
      -> {t':Type | t' == substTVar x_subst t_subst t}
  @-}
fixSubstTForallEq :: Type -> TVar -> Type -> Proof -> Type
fixSubstTForallEq t _ _ tEq
  = t ? tEq

{-@ fixSubstEForallEq
      :: e:Expr -> x_subst:TVar -> t_subst:Type
      -> p:{e == substTVarExpr x_subst t_subst e}
      -> {e':Expr | e' == substTVarExpr x_subst t_subst e}
  @-}
fixSubstEForallEq :: Expr -> TVar -> Type -> Proof -> Expr
fixSubstEForallEq e _ _ eEq
  = e ? eEq

{-@ fixSubstTForallNotEq
      :: t1:Type -> t2:Type
      -> p:{t1 == t2}
      -> {t':Type | t' == t1 && t' == t2}
  @-}
fixSubstTForallNotEq :: Type -> Type -> Proof -> Type
fixSubstTForallNotEq t1 _ p
  = t1 ? p

{-@ substETAppVarNotEqP
      :: t_ta:Type -> e_ta:Expr -> x_subst:TVar -> t_subst:Type
      -> {ETApp (substTVarExpr x_subst t_subst e_ta) (substTVar x_subst t_subst t_ta) == substTVarExpr x_subst t_subst (ETApp e_ta t_ta)}
  @-}
substETAppVarNotEqP :: Type -> Expr -> TVar -> Type -> Proof
substETAppVarNotEqP t_ta e_ta x_subst t_subst
  =   ETApp (substTVarExpr x_subst t_subst e_ta) (substTVar x_subst t_subst t_ta)
  ==. substTVarExpr x_subst t_subst (ETApp e_ta t_ta)
  *** QED

{-@ switchSubstTVar
      :: tv1:TVar -> t1:Type -> tv2:TVar -> t2:Type -> tInner:Type
      -> p:{tv1 != tv2}
      -> {substTVar tv2 t2 (substTVar tv1 t1 tInner) == substTVar tv1 (substTVar tv2 t2 t1) (substTVar tv2 t2 tInner) }
  @-}
switchSubstTVar :: TVar -> Type -> TVar -> Type -> Type -> Proof -> Proof
switchSubstTVar tv1 t1 tv2 t2 tInner t1t2NEq
  = undefined
  -- =   substTVar tv2 t2 (substTVar tv1 t1 tInner)
  -- ==. substTVar tv2 t2 (substTVar tv1 (substTVar tv2 t2 t1) tInner)
  -- ==. substTVar tv1 (substTVar tv2 t2 t1) (substTVar tv2 t2 tInner) ? t1t2NEq
  -- *** QED

{-@ fixSubstVar
      :: x:Var -> t:Type -> g:TEnv
      -> y:{lookupTEnv x g == Just t}
      -> z:{tp:Type | lookupTEnv x g == Just t && tp == t}
  @-}

fixSubstVar :: Var -> Type -> TEnv -> Proof -> Type
fixSubstVar _ t _ proof = t ? proof

-- Change Prop (ExprTy (TTVarBind x g) e t)
-- to reflect that x can be anywhere in the context?

{-@ substTVarExprTy
     :: g:TEnv -> s:VEnv -> e:Expr -> t:Type -> x:TVar -> t_x:Type
     -> g' : {y:TEnv | y=mapTEnv (substTVar x t_x) g}
     -> Prop (ExprTy g e t)
     -> Prop (ExprTy g' (substTVarExpr x t_x e) (substTVar x t_x t))
  @-}

substTVarExprTy :: TEnv -> VEnv -> Expr -> Type -> TVar -> Type -> TEnv -> ExprTy -> ExprTy
substTVarExprTy g s _ _ x t_x g' e_t = case e_t of
  E_Bool _ b -> E_Bool g' b
  E_Int _ i  -> E_Int g' i
  E_Bin _ o e1 e2 e1_tIn e2_tIn ->
    let tIn = opIn o
        e1_tIn' = substTVarExprTy g s e1 tIn x t_x g' e1_tIn
        e2_tIn' = substTVarExprTy g s e2 tIn x t_x g' e2_tIn
     -- need to somehow convince liquid haskell that substTVar x t_x (opIn o) = opIn o
     in E_Bin g' o (substTVarExpr x t_x e1) (substTVarExpr x t_x e2) e1_tIn' e2_tIn'
  E_Var _ x_var t ->
    let t' = fixSubstVar x_var (substTVar x t_x t) g' (mapTEnvPreservesLookup x_var g t (substTVar x t_x))
     in E_Var g' x_var t'
  E_Fun _ f xArg t1 eInner t2 e_t2 ->
    let t1' = substTVar x t_x t1
        t2' = substTVar x t_x t2
        eInner' = substTVarExpr x t_x eInner
        g_args = (TBind xArg t1 (TBind f (TFun t1 t2) g))
        -- TODO: pass the right arguments, substitute on t1 and t2?
        (g_args', _) = substTVarContext g_args undefined undefined x t_x
        e_t2' = substTVarExprTy g_args' undefined eInner t2 x t_x g' e_t2
     in E_Fun g' f xArg t1' eInner' t2' e_t2'
  E_App _ e1 e2 t1 t2 e1_t1_t2 e2_t1 ->
    let t1' = substTVar x t_x t1
        t2' = substTVar x t_x t2
        e1' = substTVarExpr x t_x e1
        e2' = substTVarExpr x t_x e2
        e1_t1_t2' = substTVarExprTy g s e1 (TFun t1 t2) x t_x g' e1_t1_t2
        e2_t1' = substTVarExprTy g s e2 t1 x t_x g' e2_t1
     in E_App g' e1' e2' t1' t2' e1_t1_t2' e2_t1'
  E_Pair _ e1 e2 t1 t2 e1_t1 e2_t2 ->
    let t1' = substTVar x t_x t1
        t2' = substTVar x t_x t2
        e1' = substTVarExpr x t_x e1
        e2' = substTVarExpr x t_x e2
        e1_t1' = substTVarExprTy g s e1 t1 x t_x g' e1_t1
        e2_t2' = substTVarExprTy g s e2 t2 x t_x g' e2_t2
     in E_Pair g' e1' e2' t1' t2' e1_t1' e2_t2'
  E_Fst _ e t1 t2 e_t1_t2 ->
    let t1' = substTVar x t_x t1
        t2' = substTVar x t_x t2
        e'  = substTVarExpr x t_x e
        e_t1_t2' = substTVarExprTy g s e (TPair t1 t2) x t_x g' e_t1_t2
        fixed_e_t1_t2' = fixSubstPair g' e' t1 t2 x t_x e_t1_t2'
     in E_Fst g' e' t1' t2' fixed_e_t1_t2'
  E_RecordBind _ l e er t tr e_t er_tr ->
    let t'  = substTVar x t_x t
        tr' = substTVarRecord x t_x tr
        e'  = substTVarExpr x t_x e
        er' = substTVarExpr x t_x er
        e_t' = substTVarExprTy g s e t x t_x g' e_t
        er_tr' = substTVarExprTy g s er (TRecord tr) x t_x g' er_tr
     in E_RecordBind g' l e' er' t' tr' e_t' er_tr'
  E_RecordEmp _ -> E_RecordEmp g'
  E_Forall _ x' eInner t eInner_t
    -- x' shadows x, so do no substitution.
    -- TODO t_x cannot reference x'
    | x == x'   -> undefined -- FIXME
    | otherwise ->
      let t' = substTVar x t_x t
          eInner' = substTVarExpr x t_x eInner
          eInner_t' = substTVarExprTy (TTVarBind x' g) s eInner t x t_x (TTVarBind x' g') eInner_t
       in E_Forall g' x' eInner' t' eInner_t'
        ? substTForallVarNotEqP x' t x t_x ()
        ? substEForallVarNotEqP x' eInner x t_x ()
  -- We want to substitute on t_x' always (it can't shadow this variable). We might not substitute inside
  -- of the forall, though, but that's handled in the recursive case.
  E_TApp _ e x' t_x' t_fa e_t_forall
    | x == x' -> undefined -- FIXME
    | otherwise ->
      let t_x'' = substTVar x t_x t_x'
          t_fa' = substTVar x t_x t_fa
          e' = substTVarExpr x t_x e
          t_forall = (TForall x' t_fa)
          e_t_fa' = substTVarExprTy g s e t_forall x t_x g' e_t_forall
            ? substTForallVarNotEqP x' t_forall x t_x ()
          fixed_e' = e' ? substEForallVarNotEqP x' e x t_x ()
       in E_TApp g' fixed_e' x' t_x'' t_fa' e_t_fa'
          ? switchSubstTVar x' t_x' x t_x t_fa ()

{-@ evalTApp_safe
      :: vv:Val -> x:TVar -> t_fa:Type -> t_x:Type
      -> Prop (ValTy vv (TForall x t_fa))
      -> Prop (ResTy (evalTApp t_x vv) (substTVar x t_x t_fa))
  @-}

evalTApp_safe :: Val -> TVar -> Type -> Type -> ValTy -> ResTy
evalTApp_safe v@(VForallClos _ _e _s) x t_fa t_x (V_ForallClos g s _x _t e gs e_t)
  = eval_safe g' s e' t' e_t' gs'
  where
    e' = substTVarExpr x t_x e
    t' = substTVar x t_x t_fa
    g_x = TTVarBind x g
    (g', gs') = substTVarContext g_x s undefined x t_x
    e_t' = substTVarExprTy g_x s e t_fa x t_x g' e_t

evalTApp_safe (VInt {}) _ _ _ (V_ForallClos {})
  = trivial ()

evalTApp_safe (VBool {}) _ _ _ (V_ForallClos {})
  = trivial ()

evalTApp_safe (VPair {}) _ _ _ (V_ForallClos {})
  = trivial ()

evalTApp_safe (VRecordEmp) _ _ _ (V_ForallClos {})
  = trivial ()

evalTApp_safe (VRecordBind {}) _ _ _ (V_ForallClos {})
  = trivial ()

evalTApp_safe (VClos {}) _ _ _ (V_ForallClos {})
  = trivial ()

{-@ evalTApp_res_safe
      :: r:Result -> x:TVar -> t_fa:Type -> t_x:Type
      -> Prop (ResTy r (TForall x t_fa))
      -> Prop (ResTy (mapResult (evalTApp t_x) r) (substTVar x t_x t_fa))
  @-}
evalTApp_res_safe :: Result -> TVar -> Type -> Type -> ResTy -> ResTy
evalTApp_res_safe (Result v) x t_fa t_x (R_Res _ _ v_t_fa)
  = evalTApp_safe v x t_fa t_x v_t_fa
evalTApp_res_safe _ x t_fa t_x (R_Time {})
  = R_Time (substTVar x t_x t_fa)

{-@ evalApp_safe
      :: v1:Val -> v2:Val -> t1:Type -> t2:Type
      -> Prop (ValTy v1 (TFun t1 t2))
      -> Prop (ValTy v2 t1)
      -> Prop (ResTy (evalApp v1 v2) t2)
  @-}
evalApp_safe :: Val -> Val -> Type -> Type -> ValTy -> ValTy -> ResTy
evalApp_safe v1@(VClos f x e s) v2 t1 t2 v1_t1_t2@(V_Clos g _ _ _ _ _ _ g_s gxf_e_t2) v2_t1
  = eval_safe gxf sxf e t2 gxf_e_t2 gxf_sxf
  where
    gf      = TBind f (TFun t1 t2) g
    sf      = VBind f v1           s
    gxf     = TBind x t1 gf
    sxf     = VBind x v2 sf
    gf_sf   = S_Bind f (TFun t1 t2) v1 g  s  v1_t1_t2 g_s
    gxf_sxf = S_Bind x t1           v2 gf sf v2_t1    gf_sf

evalApp_safe (VInt {}) _ _ _ (V_Clos {}) _
  = trivial ()

evalApp_safe (VBool {}) _ _ _ (V_Clos {}) _
  = trivial ()

evalApp_safe (VPair {}) _ _ _ (V_Clos {}) _
  = trivial ()

evalApp_safe (VRecordEmp) _ _ _ (V_Clos {}) _
  = trivial ()

evalApp_safe (VRecordBind {}) _ _ _ (V_Clos {}) _
  = trivial ()

evalApp_safe (VForallClos {}) _ _ _ (V_Clos {}) _
  = trivial ()


{-@ evalApp_res_safe
      :: r1:Result -> r2:Result -> t1:Type -> t2:Type
      -> Prop (ResTy r1 (TFun t1 t2))
      -> Prop (ResTy r2 t1)
      -> Prop (ResTy (seq2 evalApp r1 r2) t2)
  @-}
evalApp_res_safe :: Result -> Result -> Type -> Type -> ResTy -> ResTy -> ResTy
evalApp_res_safe (Result v1) (Result v2) t1 t2 (R_Res _ _ v1_t1_t2) (R_Res _ _ v2_t1)
  = evalApp_safe v1 v2 t1 t2 v1_t1_t2 v2_t1
evalApp_res_safe _ _ _ t2 (R_Time {}) _
  = R_Time t2
evalApp_res_safe _ _ _ t2 _ (R_Time {})
  = R_Time t2

{-@ evalPair_safe
     :: v1:Val -> v2:Val -> t1:Type -> t2:Type
     -> Prop (ValTy v1 t1)
     -> Prop (ValTy v2 t2)
     -> Prop (ResTy (evalPair v1 v2) (TPair t1 t2))
  @-}
evalPair_safe :: Val -> Val -> Type -> Type -> ValTy -> ValTy -> ResTy
evalPair_safe v1 v2 t1 t2 v1_t1 v2_t2
  = R_Res v t vt
  where
    v  = VPair v1 v2
    t  = TPair t1 t2
    vt = V_Pair v1 v2 t1 t2 v1_t1 v2_t2

{-@ evalPair_res_safe
      :: r1:Result -> r2:Result -> t1:Type -> t2:Type
      -> Prop (ResTy r1 t1)
      -> Prop (ResTy r2 t2)
      -> Prop (ResTy (seq2 evalPair r1 r2) (TPair t1 t2))
  @-}
evalPair_res_safe :: Result -> Result -> Type -> Type -> ResTy -> ResTy -> ResTy
evalPair_res_safe (Result v1) (Result v2) t1 t2 (R_Res _ _ v1_t1) (R_Res _ _ v2_t2)
  = evalPair_safe v1 v2 t1 t2 v1_t1 v2_t2
evalPair_res_safe _ _ t1 t2 (R_Time {}) _
  = R_Time (TPair t1 t2)
evalPair_res_safe _ _ t1 t2 _ (R_Time {})
  = R_Time (TPair t1 t2)

{-@ evalFst_safe
      :: vv:Val -> t1:Type -> t2:Type
      -> Prop (ValTy vv (TPair t1 t2))
      -> Prop (ResTy (evalFst vv) t1)
  @-}
evalFst_safe :: Val -> Type -> Type -> ValTy -> ResTy
evalFst_safe (VPair v1 _) t1 _ (V_Pair _ _ _ _ v1_t1 _)
  = R_Res v1 t1 v1_t1
evalFst_safe (VInt {}) t1 _ (V_Pair {})
  = trivial ()
evalFst_safe (VBool {}) t1 _ (V_Pair {})
  = trivial ()
evalFst_safe (VClos {}) t1 _ (V_Pair {})
  = trivial ()
evalFst_safe (VRecordEmp) _ _ (V_Pair {})
  = trivial ()
evalFst_safe (VRecordBind {}) _ _ (V_Pair {})
  = trivial ()
evalFst_safe (VForallClos {}) _ _ (V_Pair {})
  = trivial ()

{-@ evalFst_res_safe
      :: r:Result -> t1:Type -> t2:Type
      -> Prop (ResTy r (TPair t1 t2))
      -> Prop (ResTy (mapResult evalFst r) t1)
  @-}
evalFst_res_safe :: Result -> Type -> Type -> ResTy -> ResTy
evalFst_res_safe (Result v) t1 t2 (R_Res _ _ v_t1_t2)
  = evalFst_safe v t1 t2 v_t1_t2
evalFst_res_safe _ t1 _ (R_Time {})
  = R_Time t1

{-@ evalRecord_safe
      :: l:Label -> val:Val -> vr:Val -> t:Type -> tr:TRecord
      -> Prop (ValTy val t)
      -> Prop (ValTy vr (TRecord tr))
      -> Prop (ResTy (evalRecord l val vr) (TRecord (TRecordBind l t tr)))
  @-}
evalRecord_safe :: Label -> Val -> Val -> Type -> TRecord -> ValTy -> ValTy -> ResTy
evalRecord_safe _ _ (VPair {}) _ _ _ (V_RecordBind {})
  = trivial ()
evalRecord_safe _ _ (VInt {}) _ _ _ (V_RecordBind {})
  = trivial ()
evalRecord_safe _ _ (VBool {}) _ _ _ (V_RecordBind {})
  = trivial ()
evalRecord_safe _ _ (VClos {}) _ _ _ (V_RecordBind {})
  = trivial ()
evalRecord_safe _ _ (VPair {}) _ _ _ (V_RecordEmp {})
  = trivial ()
evalRecord_safe _ _ (VInt {}) _ _ _ (V_RecordEmp {})
  = trivial ()
evalRecord_safe _ _ (VBool {}) _ _ _ (V_RecordEmp {})
  = trivial ()
evalRecord_safe _ _ (VClos {}) _ _ _ (V_RecordEmp {})
  = trivial ()
evalRecord_safe _ _ (VForallClos {}) _ _ _ (V_RecordEmp {})
  = trivial ()
evalRecord_safe l val vr t tr val_t vr_tr =
  R_Res vrecord trecord vrecord_trecord
  where
    vrecord = VRecordBind l val vr
    trecord = TRecord (TRecordBind l t tr)
    vrecord_trecord = V_RecordBind l val vr t tr val_t vr_tr

{-@ evalRecord_res_safe
      :: l:Label -> r:Result -> rRcd:Result -> t:Type -> tr:TRecord
      -> Prop (ResTy r t)
      -> Prop (ResTy rRcd (TRecord tr))
      -> Prop (ResTy (seq2 (evalRecord l) r rRcd) (TRecord (TRecordBind l t tr)))
  @-}
evalRecord_res_safe :: Label -> Result -> Result -> Type -> TRecord -> ResTy -> ResTy -> ResTy
evalRecord_res_safe l (Result v) (Result vr) t tr (R_Res _ _ v_t) (R_Res _ _ vr_tr) =
  evalRecord_safe l v vr t tr v_t vr_tr
evalRecord_res_safe l _ _ t tr (R_Time {}) _ =
  R_Time (TRecord (TRecordBind l t tr))
evalRecord_res_safe l _ _ t tr _ (R_Time {}) =
  R_Time (TRecord (TRecordBind l t tr))

--------------------------------------------------------------------------------
-- | THEOREM: "eval_safe"
--------------------------------------------------------------------------------

{-@ readTypeSafe :: g:TEnv -> e:Expr -> t:Type
              -> Prop (ExprTy g e t)
              -> {readType g e == TResult t}
  @-}
readTypeSafe :: TEnv -> Expr -> Type -> ExprTy -> Proof
readTypeSafe g e@(EBool b) _ (E_Bool _ _)
  =   readType g e
  ==. TResult TBool
  *** QED
readTypeSafe g e@(EInt i) _ (E_Int _ _)
  =   readType g e
  ==. TResult TInt
  *** QED
readTypeSafe g e@ERecordEmp _ (E_RecordEmp _)
  =   readType g e
  ==. TResult (TRecord TRecordEmp)
  *** QED
readTypeSafe g e@(EBin o e1 e2) t (E_Bin _ _ _ _ e1_t1 e2_t2)
  =   readType g e
  ?   readTypeSafe g e1 (opIn o) e1_t1
  ?   readTypeSafe g e2 (opIn o) e2_t2
  ==. TResult (opOut o)
  *** QED
readTypeSafe g e@(EVar var) _ (E_Var _ _ t)
  =   readType g e
  ==. TResult t
  *** QED
readTypeSafe g e@(EFun f x tArg tRet eInner) _ (E_Fun _ _ _ _ _ _ e_tRet)
  =   readType g e
  ?   readTypeSafe (TBind x tArg (TBind f (TFun tArg tRet) g)) eInner tRet e_tRet
  ==. TResult (TFun tArg tRet)
  *** QED
readTypeSafe g e@(EApp e1 e2) _ (E_App _ _ _ t1 t2 e1_t1_t2 e2_t1)
  =   readType g e
  ?   readTypeSafe g e1 (TFun t1 t2) e1_t1_t2
  ?   readTypeSafe g e2 t1 e2_t1
  ==. TResult t2
  *** QED
readTypeSafe g e@(EPair e1 e2) _ (E_Pair _ _ _ t1 t2 e1_t1 e2_t2)
  =   readType g e
  ?   readTypeSafe g e1 t1 e1_t1
  ?   readTypeSafe g e2 t2 e2_t2
  ==. TResult (TPair t1 t2)
  *** QED
readTypeSafe g e@(EFst ePair) _ (E_Fst _ _ t1 t2 ePair_t1_t2)
  =   readType g e
  ?   readTypeSafe g ePair (TPair t1 t2) ePair_t1_t2
  ==. TResult t1
  *** QED
readTypeSafe g (ERecordBind l e er) _ (E_RecordBind _ _ _ _ t tr e_t er_tr)
  =   readType g (ERecordBind l e er)
  ?   readTypeSafe g e t e_t
  ?   readTypeSafe g er (TRecord tr) er_tr
  ==. TResult (TRecord (TRecordBind l t tr))
  *** QED
readTypeSafe g (EForall tv e) _ (E_Forall _ _ _ t e_t)
  =   readType g (EForall tv e)
  ?   readTypeSafe (TTVarBind tv g) e t e_t
  ==. TResult (TForall tv t)
  *** QED
readTypeSafe g (ETApp e t) _ (E_TApp _ _ x t_x t_fa e_t_fa)
  =   readType g (ETApp e t)
  ?   readTypeSafe g e (TForall x t_fa) e_t_fa
  ==. TResult (substTVar x t_x t_fa)
  *** QED

-- {-@ inference2 :: gTEnv -> e:Expr -> t:Type
--                -> p:{infer e == Just t}
--                -> Prop (ExprTy g e t)
--   @-}

{-@ eval_safe :: g:TEnv -> s:VEnv -> e:Expr -> t:Type
              -> Prop (ExprTy g e t)
              -> Prop (StoTy  g s)
              -> Prop (ResTy (eval s e) t)
  @-}
eval_safe :: TEnv -> VEnv -> Expr -> Type -> ExprTy -> StoTy -> ResTy

eval_safe _ _ (EBool b) _ (E_Bool {}) _
  = R_Res (VBool b) TBool (V_Bool b)

eval_safe _ _ (EInt n) _ (E_Int {}) _
  = R_Res (VInt n) TInt (V_Int n)

eval_safe g s (EBin o e1 e2) t (E_Bin _ _ _ _ et1 et2) gs
  = evalOp_res_safe o (eval s e1) (eval s e2) rt1 rt2
  where
    rt1          = eval_safe g s e1 (opIn o) et1 gs
    rt2          = eval_safe g s e2 (opIn o) et2 gs

eval_safe g s (EVar x) t (E_Var {}) gs
  = R_Res w t wt
  where
    (w, (_, wt)) = lookup_safe g s x t gs

eval_safe g s (EFun f x t1 t2 e) t (E_Fun _ _ _ _ _ _ et2) gs
  = R_Res (VClos f x e s) t (V_Clos g s f x t1 t2 e gs et2)

eval_safe g s (EForall x e) tp@(TForall _ t) (E_Forall _ _ _ _ et) gs
  = R_Res (VForallClos x e s) tp (V_ForallClos g s x t e gs et)

eval_safe _ _ (EForall _ _) _ (E_Forall _ _ _ _ _) _
  = trivial ()

eval_safe g s (EApp e1 e2) t2 (E_App _ _ _ t1 _ e1_t1_t2 e2_t1) gs
  = evalApp_res_safe (eval s e1) (eval s e2) t1 t2 r1_t1_t2 r2_t1
  where
    r1_t1_t2 = eval_safe g s e1 (TFun t1 t2) e1_t1_t2 gs
    r2_t1    = eval_safe g s e2 t1           e2_t1    gs

eval_safe g s (EPair e1 e2) t (E_Pair _ _ _ _ _ e1_t1 e2_t2) gs
  = case t of
      (TPair t1 t2) -> evalPair_res_safe (eval s e1) (eval s e2) t1 t2 (eval_safe g s e1 t1 e1_t1 gs) (eval_safe g s e2 t2 e2_t2 gs)
      _             -> trivial ()

eval_safe g s (EFst e) _ (E_Fst _ _ t1 t2 e1_t1_t2) gs
  = evalFst_res_safe (eval s e) t1 t2 r1_t1_t2
  where
    r1_t1_t2 = eval_safe g s e (TPair t1 t2) e1_t1_t2 gs

eval_safe _ _ ERecordEmp _ (E_RecordEmp {}) _
  = R_Res VRecordEmp (TRecord (TRecordEmp)) V_RecordEmp

eval_safe g s (ERecordBind l e er) tp (E_RecordBind _ _ _ _ _ _ e_t er_tr) gs
  = case tp of
      TRecord (TRecordBind _ t tr) -> evalRecord_res_safe l (eval s e) (eval s er) t tr (eval_safe g s e t e_t gs) (eval_safe g s er (TRecord tr) er_tr gs)
      _ -> trivial ()

eval_safe g s (ETApp e t) tp (E_TApp _ _ x t_x t_fa e_t_fa) gs
  = evalTApp_res_safe (eval s e) x t_fa t_x (eval_safe g s e (TForall x t_fa) e_t_fa gs)


-- Tests
test_bools = [ eval_safe g s e t e_t gs
               -- , eval_safe g s e t e_t_bad gs -- should fail
             ]
  where
    g = TEmp
    s = VEmp
    e = EBool False
    t = TBool
    e_t = E_Bool g False
    e_t_bad = E_Bool g True
    gs = S_Emp

test_forall_1 = eval_safe g s e t e_t gs
  where
    g = TEmp
    s = VEmp
    x = "x"
    eInner = EBool False
    tInner = TBool
    eInner_tInner = E_Bool (TTVarBind x g) False
    e = EForall x eInner
    t = TForall x tInner
    e_t = E_Forall g x eInner tInner eInner_tInner
    gs = S_Emp

test_forall_2 = eval_safe g s e t e_t gs
  where
    g = TEmp
    s = VEmp
    t_x = "a" -- both could be "x" but this makes it easier to read
    v_x = "x"
    f = "f"
    eVar = EVar v_x
    tVar = TVar t_x
    eVar_tVar = E_Var (TBind v_x tVar (TBind f (TFun tVar tVar) g')) v_x tVar
    eInner = EFun f v_x tVar tVar eVar
    tInner = TFun tVar tVar
    g' = TTVarBind t_x g
    eInner_tInner = E_Fun g' f v_x tVar eVar tVar eVar_tVar
    e = EForall t_x eInner
    t = TForall t_x tInner
    e_t = E_Forall g t_x eInner tInner eInner_tInner
    gs = S_Emp

test_tapp_1 = eval_safe g s e t e_t gs
  where
    g = TEmp
    s = VEmp
    x = "x"
    eInner = EBool False
    tInner = TBool
    eInner_tInner = E_Bool (TTVarBind x g) False
    e_fa = EForall x eInner
    t_fa = TForall x tInner
    e_t_fa = E_Forall g x eInner tInner eInner_tInner
    e = ETApp e_fa TInt
    t = TBool
    e_t = E_TApp g e_fa x TInt tInner e_t_fa
    gs = S_Emp

test_tapp_2 = eval_safe g s e t e_t gs
  where
    g = TEmp
    s = VEmp
    t_x = "a" -- both could be "x" but this makes it easier to read
    v_x = "x"
    f = "f"
    eVar = EVar v_x
    tVar = TVar t_x
    eVar_tVar = E_Var (TBind v_x tVar (TBind f (TFun tVar tVar) g')) v_x tVar
    eInner = EFun f v_x tVar tVar eVar
    tInner = TFun tVar tVar
    g' = TTVarBind t_x g
    eInner_tInner = E_Fun g' f v_x tVar eVar tVar eVar_tVar
    e_fa = EForall t_x eInner
    t_fa = TForall t_x tInner
    e_t_fa = E_Forall g t_x eInner tInner eInner_tInner
    e = ETApp e_fa TInt
    t = TFun TInt TInt
    e_t = E_TApp g e_fa t_x TInt tInner e_t_fa
    gs = S_Emp

main :: IO ()
main = do
  run $ EUBool False
  run $ EUFun "f" "x" (EUBool True)
  run $ EUApp (EUFun "f" "x" (EUVar "x")) (EUBool True)
  run $ EUFun "f" "x" (EUApp (EUVar "x") (EUVar "x"))
  run $ EUApp (EUFun "f" "x" (EUVar "x")) (EUFun "g" "y" (EUVar "y"))
  run $ EUFun "_" "f" (EUFun "_" "g" (EUFun "_" "x" (EUApp (EUApp (EUVar "f") (EUVar "x")) (EUApp (EUVar "g") (EUVar "x")))))
  where
    run = print . infer TSEmp
  -- putStrLn . printer $ test_tapp_1
  -- putStrLn . printer $ test_tapp_2
  -- where
  --   printer resTy = case resTy of
  --     R_Res val ty valTy -> "val: " ++ show val ++ " type: " ++ show ty
  --     R_Time ty -> "timeout, type: " ++ show ty


--------------------------------------------------------------------------------
-- | Boilerplate
--------------------------------------------------------------------------------

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ trivial :: {v:a | false} -> b @-}
trivial :: a -> b
trivial x = trivial x
