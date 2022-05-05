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
  -- | UVar String
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
  , varCount :: Int
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


{-@ data AlgoJudgement where
      AJ_Bool :: g:TEnv -> s:TStore -> b:Bool
              -> Prop (AlgoJudgement g s (EUBool b) (EBool b) TBool s)
      AJ_Var  :: g:TEnv -> s:TStore -> x:Var -> t:{Type | lookupTEnv x g == Just t}
              -> Prop (AlgoJudgement g s (EUVar x) (EVar x) t s)
  @-}

data AlgoJudgementP where
  AlgoJudgement :: TEnv -> TStore -> ExprU -> Expr -> Type -> TStore -> AlgoJudgementP

data AlgoJudgement where
  AJ_Bool :: TEnv -> TStore -> Bool -> AlgoJudgement
  AJ_Var  :: TEnv -> TStore -> Var -> Type -> AlgoJudgement
  AJ_App  :: TEnv -> TStore -> Expr -> Expr -> Type -> Type -> AlgoJudgement -> AlgoJudgement -> AlgoJudgement

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

{-@ reflect showDigit @-}
{-@ showDigit :: {x:Int | x >= 0 && x < 10} -> Char @-}
showDigit :: Int -> Char
showDigit 0 = '0'
showDigit 1 = '1'
showDigit 2 = '2'
showDigit 3 = '3'
showDigit 4 = '4'
showDigit 5 = '5'
showDigit 6 = '6'
showDigit 7 = '7'
showDigit 8 = '8'
showDigit 9 = '9'

{-@ reflect showInt' @-}
showInt' x acc = if dividend == 0
                  then showDigit rem : acc
                  else showInt' dividend (showDigit rem : acc)
  where
    dividend = x `div` 10
    rem = x `mod` 10

{-@ reflect showInt @-}
showInt :: Int -> String
showInt x = showInt' x []

{-@ reflect freshTVar @-}
freshTVar :: InferState -> (InferState, Type)
freshTVar (InferState env consts varCount) = 
  (InferState env consts (varCount + 1), TVar $ showInt varCount)

{-@ reflect makeConstraint @-}
makeConstraint :: InferState -> Type -> Type -> InferState
makeConstraint (InferState env consts varCount) t1 t2 = 
  InferState env ((t1, t2):consts) varCount


data GenConstraintsResult where
  GCRight :: InferState -> ExprU -> Expr -> Type -> ExprUExpr -> GenConstraintsResult
  GCLeft  :: String -> GenConstraintsResult

{-@ data GenConstraintsResult where
      GCRight :: is:InferState -> g:TEnv -> eu:ExprU -> e:Expr -> t:Type
              -> Prop (ExprUExpr eu e)
              -> (Subst -> ExprTy g e' t')
              -> GenConstraintsResult
      GCLeft  :: String
              -> GenConstraintsResult
  @-}

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
genConstraints is0 eu_f@(EUFun f x eu) = case genConstraints is2 eu of
  GCRight (InferState _ newConsts newVc) _ e tp eu_e ->
    -- Return returnTV isntead of tp
    -- Add constraint that returnTV == tp
    GCRight (InferState originalEnv newConsts newVc) eu_f (EFun f x tv tp e) (TFun tv tp) (EU_Fun f x tv eu e tp eu_e)
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
  deriving (Eq, Show)
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
-- 1. Write down a formalization for unification variables on paper.
--    * Judgement for uvars with a store in ExprTy
--    * Write up judgement for unification
--    * Judgements take in a store and return a new store
-- 2. Remove constraint generation (inline unify).
-- (Maybe) Persist the generated ExprUExpr through substitution and write a
-- proof that goes from untype expression all the way through inference to a
-- typed expression.

{-@ reflect infer @-}
infer :: TStore -> ExprU -> Either String (Expr, Type)
infer ts eu = case genConstraints (InferState ts [] 0) eu of
  GCRight (InferState _ constraints _) _ eUnsolved tUnsolved _ -> case solveConstraints SEmp constraints of
    Right subst ->
      Right $ (applySubstExpr subst eUnsolved, applySubst subst tUnsolved)
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

main :: IO ()
main = do
  -- run $ EUBool False
  -- run $ EUFun "f" "x" (EUBool True)
  -- run $ EUApp (EUFun "f" "x" (EUVar "x")) (EUBool True)
  -- run $ EUFun "f" "x" (EUApp (EUVar "x") (EUVar "x"))
  run $ EUApp (EUFun "f" "x" (EUVar "x")) (EUFun "g" "y" (EUVar "y"))
  -- run $ EUFun "_" "f" (EUFun "_" "g" (EUFun "_" "x" (EUApp (EUApp (EUVar "f") (EUVar "x")) (EUApp (EUVar "g") (EUVar "x")))))
  where
    run = print . infer TSEmp

--------------------------------------------------------------------------------
-- | Boilerplate
--------------------------------------------------------------------------------

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ trivial :: {v:a | false} -> b @-}
trivial :: a -> b
trivial x = trivial x
