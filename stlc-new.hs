{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

{-# LANGUAGE GADTs #-}

module STLC where
import Language.Haskell.Liquid.Equational
import Data.Set (Set)
import qualified Data.Set as S

-- Dunno why the import doesn't work
-- type Proof = ()
-- data QED = QED
-- 
-- (***) :: a -> QED -> Proof
-- _ *** QED = ()
-- infixl 2 ***
-- 
-- {-@ (==.) :: x:a -> y:{a | x == y} -> {o:a | o == y && o == x} @-}
-- (==.) :: a -> a -> a
-- _ ==. x = x
-- 
-- (?) :: a -> Proof -> a
-- x ? _ = x

type UVar  = Int
type TVar  = String
type Var   = String

data Type
  = TUnit
  | UVar UVar
  | TVar TVar
  | TArr Type Type
  deriving (Eq, Show)

data ExprU
  = EUUnit
  | EUVar Var
  | EULam Var ExprU
  | EUApp ExprU ExprU
  deriving (Eq, Show)

data Expr
  = EUnit
  | EVar Var
  | ELam Var Type Expr
  | EApp Expr Expr
  deriving (Eq, Show)

data TEnv
  = TBind Var Type TEnv
  | TEmp
  deriving (Eq, Show)

data TStore
  = TSBind UVar Type TStore
  | TSEmp
  deriving (Eq, Show)

data TState
  = TState 
  { tStore  :: TStore
  , uvCount :: UVar
  }
  deriving (Eq, Show)

{-@ reflect freeUVars @-}
freeUVars :: Type -> Set UVar
freeUVars (TArr t1 t2) = freeUVars t1 `S.union` freeUVars t2
freeUVars (TUnit) = S.empty
freeUVars (UVar uv) = S.singleton uv
freeUVars (TVar tv) = S.empty

{-@ reflect solvedUVars @-}
solvedUVars :: TStore -> Set UVar
solvedUVars TSEmp = S.empty
solvedUVars (TSBind uv _ s) = S.singleton uv `S.union` (solvedUVars s)

{-@ reflect right @-}
right :: Type -> Either String Type
right t = Right t

{-@ reflect left @-}
left :: String -> Either String Type
left a = Left a

{-@ reflect lookupTStore @-}
lookupTStore :: UVar -> TStore -> Either String Type
lookupTStore x TSEmp = left "lookupTStore: lookup failed"
lookupTStore x (TSBind v t ts)
  | x == v    = right t
  | otherwise = lookupTStore x ts

-- data TStoreComparison
--   = TStoreEq
--   | TStoreOneMore
--   | TStoreNotEqOrOneMore
--   deriving (Eq, Show)
-- 
-- {-@ reflect compareTStore @-}
-- compareTStore :: TStore -> TStore -> TStoreComparison
-- compareTStore t1 t2 = case (t1, t2) of
--   (t1', t2') | t1' == t2' -> TStoreEq
--   (t1', TSBind u v t2') | t1' == t2' -> TStoreOneMore
--   _ -> TStoreNotEqOrOneMore
-- 
-- {-@ reflect isSameOrOneMoreTStore @-}
-- isSameOrOneMoreTStore :: TStore -> TStore -> Bool
-- isSameOrOneMoreTStore t1 t2
--   | t1 == t2 = True
-- isSameOrOneMoreTStore t1 (TSBind u v t2) = t1 == t2
-- isSameOrOneMoreTStore _ _ = False

{-@ reflect isPrefixTStore @-}
isPrefixTStore :: TStore -> TStore -> Bool
isPrefixTStore ts1 ts2
  | ts1 == ts2 = True
  | otherwise  = case ts2 of
      TSEmp -> False
      TSBind _u _v ts2' -> isPrefixTStore ts1 ts2'

{-@ reflect applyTStoreToTEnv @-}
applyTStoreToTEnv :: TStore -> TEnv -> TEnv
applyTStoreToTEnv _ TEmp = TEmp
applyTStoreToTEnv s (TBind x t g) = TBind x (applyTStoreToType s t) (applyTStoreToTEnv s g)

{-@ reflect applyTStoreToType @-}
applyTStoreToType :: TStore -> Type -> Type
applyTStoreToType TSEmp t = t 
-- -- Apply substitutions from the inside-out
applyTStoreToType (TSBind uv tSubst s) t =
  let t' = applyTStoreToType s t
   in applySubstToType uv tSubst t'
-- Should be impossible to reach, added for LH totality check
-- (although GHC detects that this will never be reached)
-- applyTStoreToType _ _ = TUnit

{-@ reflect applyTStoreToExpr @-}
applyTStoreToExpr :: TStore -> Expr -> Expr
applyTStoreToExpr TSEmp e = e
applyTStoreToExpr _ EUnit = EUnit
applyTStoreToExpr _ (EVar v) = EVar v
applyTStoreToExpr s (ELam x t e) = ELam x (applyTStoreToType s t) (applyTStoreToExpr s e)
applyTStoreToExpr s (EApp e1 e2) = EApp (applyTStoreToExpr s e1) (applyTStoreToExpr s e2)

{-@ reflect applySubstToType @-}
applySubstToType :: UVar -> Type -> Type -> Type
applySubstToType _uv _substType TUnit = TUnit
applySubstToType _uv _substType (TVar v) = TVar v
applySubstToType uv substType (TArr t1 t2) = TArr (applySubstToType uv substType t1) (applySubstToType uv substType t2)
applySubstToType uv1 substType (UVar uv2)
  | uv1 == uv2 = substType
  | otherwise  = UVar uv2

{-@ reflect lookupTEnv @-}
lookupTEnv :: Var -> TEnv -> Either String Type
lookupTEnv x TEmp             = left "lookupTEnv: lookup failed"
lookupTEnv x (TBind y v env)  = if x == y then right v else lookupTEnv x env
-- lookupTEnv x (TTVarBind _ env)  = lookupTEnv x env

{-@ data DeclJudgement where
     DJ_Unit :: g:TEnv
             -> Prop (DeclJudgement g EUnit TUnit)
     DJ_Var  :: g:TEnv -> x:Var -> t:{Type | lookupTEnv x g == Right t}
             -> Prop (DeclJudgement g (EVar x) t)
     DJ_Lam  :: g:TEnv -> x:Var -> t1:Type -> e:Expr -> t2:Type
             -> Prop (DeclJudgement (TBind x t1 g) e t2)
             -> Prop (DeclJudgement g (ELam x t1 e) (TArr t1 t2))
     DJ_App  :: g:TEnv -> e1:Expr -> e2:Expr -> t1:Type -> t2:Type
             -> Prop (DeclJudgement g e1 (TArr t1 t2))
             -> Prop (DeclJudgement g e2 t1)
             -> Prop (DeclJudgement g (EApp e1 e2) t2)
  @-}
data DeclJudgementP where
  DeclJudgement :: TEnv -> Expr -> Type -> DeclJudgementP

data DeclJudgement where
  DJ_Unit :: TEnv -> DeclJudgement
  DJ_Var  :: TEnv -> Var -> Type -> DeclJudgement
  DJ_Lam  :: TEnv -> Var -> Type -> Expr -> Type -> DeclJudgement -> DeclJudgement
  DJ_App  :: TEnv -> Expr -> Expr -> Type -> Type -> DeclJudgement -> DeclJudgement -> DeclJudgement

{-@ reflect freshUVar @-}
freshUVar :: TState -> (UVar, TState)
freshUVar (TState tStore uvCounter) = (uvCounter, TState tStore (uvCounter + 1))

-- Lemmas and helpers for tEq

{-@ reflect rightTStore @-}
rightTStore :: TStore -> Either String TStore
rightTStore t = Right t

{-@ leftTStore :: ts:TStore -> s:String -> Either String {ts': TStore | isPrefixTStore ts ts'}
  @-}
leftTStore :: TStore -> String -> Either String TStore
leftTStore _ a = Left a

-- TODO:
--   * Use (and write) isPrefix instead of TStoreComparison (remove this witness).
--   * Structure the proof using two cases:
--      | ts1 == ts2 = ...
--      | otherwise  = ...
--   * The otherwise case will involve a recursive call to tEqWeakening
--   * May need to add refinements on isPrefix (unsure, reflection may suffice)

{-@ tEqWeakening :: ts1:TStore -> {ts2:TStore| isPrefixTStore ts1 ts2} -> t1:Type -> t2:Type
                 -> p:{applyTStoreToType ts1 t1 == applyTStoreToType ts1 t2}
                 -> {applyTStoreToType ts2 t1 == applyTStoreToType ts2 t2}
  @-}
tEqWeakening :: TStore -> TStore -> Type -> Type -> Proof -> Proof
tEqWeakening ts1 ts2 t1 t2 pt1Eqt2
  | ts1 == ts2 = let applyT1Eq =   applyTStoreToType ts1 t1
                               ==. applyTStoreToType ts2 t1
                               *** QED
                     applyT2Eq =   applyTStoreToType ts1 t2
                               ==. applyTStoreToType ts2 t2
                               *** QED
                  in  applyTStoreToType ts2 t1
                  ==. applyTStoreToType ts2 t2
                    ? applyT1Eq
                    ? applyT2Eq
                    ? pt1Eqt2
                  *** QED
  | otherwise = case ts2 of
                  TSEmp             -> trivial ()
                  TSBind u sub ts2' ->  applyTStoreToType ts2 t1
                                    ==. applySubstToType u sub (applyTStoreToType ts2' t1)
                                      ? tEqWeakening ts1 ts2' t1 t2 pt1Eqt2
                                    ==. applySubstToType u sub (applyTStoreToType ts2' t2)
                                    ==. applyTStoreToType ts2 t2
                                    *** QED
-- tEqWeakening ts1 ts2 t1 t2 TStoreEq pt1Eqt2
--   =   applyTStoreToType ts2 t1
--   ==. applyTStoreToType ts2 t2
--     ? applyT1Eq
--     ? applyT2Eq
--     ? pt1Eqt2
--   *** QED
--   where
--     applyT1Eq =   applyTStoreToType ts1 t1
--               ==. applyTStoreToType ts2 t1
--               *** QED
--     applyT2Eq =   applyTStoreToType ts1 t2
--               ==. applyTStoreToType ts2 t2
--               *** QED
-- tEqWeakening ts1 ts2@(TSBind u sub ts2Inner) t1 t2 TStoreOneMore pt1Eqt2
--   =   applyTStoreToType ts2 t1
--   ==. applyTStoreToType ts2 t2
--     ? applyT1OneMore
--     ? applyT2OneMore
--     ? pt1Eqt2
--   *** QED
--   where
--     applyT1OneMore =   applyTStoreToType ts2 t1
--                    ==. applySubstToType u sub (applyTStoreToType ts2Inner t1)
--                    ==. applySubstToType u sub (applyTStoreToType ts1 t1)
--                    ==. applySubstToType u sub (applyTStoreToType ts1 t1)
--                    *** QED
--     applyT2OneMore =   applyTStoreToType ts2 t2
--                    ==. applySubstToType u sub (applyTStoreToType ts2Inner t2)
--                    ==. applySubstToType u sub (applyTStoreToType ts1 t2)
--                    *** QED
-- tEqWeakening _ts1 TSEmp _t1 _t2 TStoreOneMore _pt1Eqt2 = trivial ()
-- tEqWeakening _ _ _ _ TStoreNotEqOrOneMore _ = trivial ()
-- 
-- {-@ tEqEqualP :: ts1:TStore -> {ts2:TStore | isPrefixTStore ts1 ts2} -> t1:Type -> t2:Type
--               -> p:{t1 == t2} -> p2:{ts1 == ts2}
--               -> {applyTStoreToType ts2 t1 == applyTStoreToType ts2 t2}
--   @-}
-- tEqEqualP ts1 ts2 t1 t2 pt1Eqt2 pts1Eqts2
--   =   applyTStoreToType ts1 t1 
--   ==. applyTStoreToType ts2 t2
--   ?   pt1Eqt2
--   *** QED
-- 
-- {-@ applyTStoreDistributionP :: ts:TStore -> t1:Type -> t2:Type
--                              -> {applyTStoreToType ts (TArr t1 t2) == TArr (applyTStoreToType ts t1) (applyTStoreToType ts t2)}
--   @-}
-- applyTStoreDistributionP :: TStore -> Type -> Type -> Proof
-- applyTStoreDistributionP TSEmp t1 t2
--   =   applyTStoreToType TSEmp (TArr t1 t2)
--   ==. TArr (applyTStoreToType TSEmp t1) (applyTStoreToType TSEmp t2)
--   *** QED
-- applyTStoreDistributionP (TSBind u tSub ts') t1 t2
--   =   applyTStoreToType (TSBind u tSub ts') (TArr t1 t2)
--   ==. applySubstToType u tSub (applyTStoreToType ts' (TArr t1 t2))
--     ? applyTStoreDistributionP ts' t1 t2
--   ==. applySubstToType u tSub (TArr (applyTStoreToType ts' t1) (applyTStoreToType ts' t2))
--   ==. TArr (applySubstToType u tSub (applyTStoreToType ts' t1)) (applySubstToType u tSub (applyTStoreToType ts' t2))
--   ==. TArr (applyTStoreToType (TSBind u tSub ts') t1) (applyTStoreToType (TSBind u tSub ts') t2)
--   *** QED
-- 
-- {-@ tEqArrowP :: ts1:TStore -> {ts2:TStore | isPrefixTStore ts1 ts2} -> t1:Type -> t2:Type -> t3:Type -> t4:Type
--               -> p1:{applyTStoreToType ts1 t1 == applyTStoreToType ts1 t3}
--               -> p2:{applyTStoreToType ts2 t2 == applyTStoreToType ts2 t4}
--               -> {applyTStoreToType ts2 (TArr t1 t2) == applyTStoreToType ts2 (TArr t3 t4)}
--   @-}
-- tEqArrowP :: TStore -> TStore -> Type -> Type -> Type -> Type -> Proof -> Proof -> Proof
-- tEqArrowP ts1 ts2 t1 t2 t3 t4 pt1Eqt3 pt2Eqt4
--   =   applyTStoreToType ts2 (TArr t1 t2)
--     ? applyTStoreDistributionP ts2 t1 t2
--   ==. TArr (applyTStoreToType ts2 t1) (applyTStoreToType ts2 t2)
--   ==. TArr (applyTStoreToType ts2 t3) (applyTStoreToType ts2 t2)
--   ==. TArr (applyTStoreToType ts2 t3) (applyTStoreToType ts2 t4)
--     ? applyTStoreDistributionP ts2 t3 t4
--   ==. applyTStoreToType ts2 (TArr t3 t4)
--     ? pt1Eqt3'
--     ? pt2Eqt4
--   *** QED
--   where
--     pt1Eqt3' = undefined -- tEqWeakening ts1 ts2 t1 t3 pt1Eqt3

-- Return LH witness that (tStore `app` t1 is literally equal to tStore `app` t2)
-- {-@ tEq :: ts:TStore -> t1:Type -> t2:Type 
--         -> Either String {ts':TStore | applyTStoreToType ts' t1 == applyTStoreToType ts' t2 && isPrefixTStore ts ts'}
--   @-}
-- tEq :: TStore -> Type -> Type -> Either String TStore
-- tEq ts t1 t2
--   | t1 == t2 = rightTStore ts
--              -- ? tEqEqualP ts ts t1 t2 tsc () ()
-- tEq ts (TArr t1 t2) (TArr t3 t4) = case tEq ts t1 t2 of
--   Left err -> leftTStore ts err
--   Right ts1 -> case tEq ts1 t3 t4 of
--     Left err -> leftTStore ts err
--     Right ts2 -> rightTStore ts2 
--                -- ? tEqArrowP ts1 ts2 t1 t2 t3 t4 tsc () ()
-- tEq ts (UVar uv) t = if uv `S.notMember` freeUVars t && uv `S.notMember` solvedUVars ts
--   then rightTStore $ TSBind uv t ts 
--   else leftTStore ts "tEq: occurs check failed"
-- tEq ts t (UVar uv) = if uv `S.notMember` freeUVars t && uv `S.notMember` solvedUVars ts
--   then rightTStore $ TSBind uv t ts
--   else leftTStore ts "tEq: occurs check failed"
-- tEq ts t1 t2
--   | applyTStoreToType ts t1 /= t1 || applyTStoreToType ts t2 /= t2 = tEq ts (applyTStoreToType ts t1) (applyTStoreToType ts t2)
-- tEq ts t1 t2 = leftTStore ts "tEq: not equal"

-- infer :: TState -> TEnv -> ExprU -> Either String (Expr, Type, TState, DeclJudgement)
-- infer ts g EUUnit = Right (EUnit, TUnit, ts, DJ_Unit g)
-- infer ts g (EUVar v) = case lookupTEnv v g of
--   Left err -> Left err
--   Right t  -> Right (EVar v, t, ts, DJ_Var g v t)
-- infer ts g (EUApp eu1 eu2) =
--   let (u, ts0) = freshUVar ts
--    in case infer ts0 g eu1 of
--         Left err -> Left err
--         Right (e1, tArr, ts1, e1_tArr) -> 
--           case infer ts1 g eu2 of
--             Left err -> Left err
--             Right (e2, tArg, ts2, e2_tArg) ->
--               case tEq (tStore ts2) tArr (TArr tArg (UVar u)) of
--                 Left err -> Left err
--                 Right tStore' -> Right (EApp e1 e2, UVar u, ts2 {tStore = tStore'}, DJ_App g e1 e2 tArg (UVar u) e1_tArr e2_tArg)
-- infer ts g (EULam x eu) =
--   let (u, ts0) = freshUVar ts
--    in case infer ts0 (TBind x (UVar u) g) eu of
--         Left err -> Left err
--         Right (e, tRet, ts1, e_tRet) -> Right (ELam x (UVar u) e, TArr (UVar u) tRet, ts1, DJ_Lam g x (UVar u) e tRet e_tRet)

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ trivial :: {v:a | false} -> b @-}
trivial :: a -> b
trivial x = trivial x

-- Test stuff
initialTState :: TState
initialTState = TState TSEmp 0

-- inferTest :: TState -> TEnv -> ExprU -> Either String (Expr, Type, TState)
-- inferTest ts g eu = case infer ts g eu of
--   Left err -> Left err
--   Right (e, t, ts', _) -> Right (e, t, ts')
