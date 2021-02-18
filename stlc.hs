-- http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html 

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

{-# LANGUAGE GADTs #-}

-- TODO
-- Add type information to the store when evaluation happens?
-- id = EForall Y. \x: Y -> x
-- (EForall X. (id @ X)) @ Int
--              ^- V_Clos g s f x (TVar "Y") (TVar "Y") e
-- ETApp g (EForall X. (ETApp id X)) Int

-- ExprTy g (ETApp id X) (X -> X)[X |-> Int]
-- ExprTy g (ETapp id X) (Int -> Int)

module STLC where 

type TVar  = String
type Var   = String 
type Label = String

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

data Expr 
  = EBool Bool               -- ^ 'EBool b'       is 'b'
  | EInt  Int                -- ^ 'EInt i'        is 'i'
  | EBin  Op Expr Expr       -- ^ 'EBin o e1 e2'  is 'e1 o e2'
  | EVar  Var                -- ^ 'EVar x'        is 'x'
  | EFun  Var Var Type Expr  -- ^ 'EFun f x t e'  is 'fun f(x:t) e'
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
eval s (EFun f x t e) = Result (VClos f x e s) 
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

-- flipped because of SMTLib issues with anonymous functions
{-@ reflect evalTApp @-}
evalTApp :: Type -> Val -> Result
-- substitute on terms here
evalTApp _ (VForallClos x e s) = eval s e
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
      | R_Time :: t:Type -> Prop (ResTy Timeout t) 
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
      | V_Int  :: i:Int  -> Prop (ValTy (VInt i)  TInt) 
      | V_Clos :: g:TEnv -> s:VEnv -> f:Var -> x:Var -> t1:Type -> t2:Type -> e:Expr 
               -> Prop (StoTy g s) 
               -> Prop (ExprTy (TBind x t1 (TBind f (TFun t1 t2) g)) e t2)
               -> Prop (ValTy (VClos f x e s) (TFun t1 t2)) 
      | V_ForallClos :: g:TEnv -> s:VEnv -> x:TVar -> t:Type -> e:Expr
                     -> Prop (StoTy g s)
                     -> Prop (ExprTy (TTVarBind x g) e t)
                     -> Prop (ValTy (VForallClos x e s) (TForall x t))
      | V_Pair :: v1:Val -> v2:Val -> t1:Type -> t2:Type 
               -> Prop (ValTy v1 t1) 
               -> Prop (ValTy v2 t2)
               -> Prop (ValTy (VPair v1 v2) (TPair t1 t2))
      | V_RecordBind :: l:Label -> val:Val -> rcd:Val -> t:Type -> tr:TRecord
                     -> Prop (ValTy val t)
                     -> Prop (ValTy rcd (TRecord tr))
                     -> Prop (ValTy (VRecordBind l val rcd) (TRecord (TRecordBind l t tr)))
      | V_RecordEmp :: Prop (ValTy VRecordEmp (TRecord TRecordEmp))
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
      | S_Bind :: x:Var -> t:Type -> val:Val -> g:TEnv -> s:VEnv
               -> Prop (ValTy val t) 
               -> Prop (StoTy g   s) 
               -> Prop (StoTy (TBind x t g) (VBind x val s)) 
      | S_TVarBind :: x:TVar -> g:TEnv -> s:VEnv
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
    G |- EFun f x t1 e : t1 -> t2 

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

{-@ data ExprTy where 
       E_Bool  :: g:TEnv -> b:Bool 
               -> Prop (ExprTy g (EBool b) TBool)
      | E_Int  :: g:TEnv -> i:Int  
               -> Prop (ExprTy g (EInt i)  TInt)
      | E_Bin  :: g:TEnv -> o:Op -> e1:Expr -> e2:Expr 
               -> Prop (ExprTy g e1 (opIn o)) 
               -> Prop (ExprTy g e2 (opIn o))
               -> Prop (ExprTy g (EBin o e1 e2) (opOut o))
      | E_Var  :: g:TEnv -> x:Var -> t:{Type| lookupTEnv x g == Just t} 
               -> Prop (ExprTy g (EVar x) t)
      | E_Fun  :: g:TEnv -> f:Var -> x:Var -> t1:Type -> e:Expr -> t2:Type
               -> Prop (ExprTy (TBind x t1 (TBind f (TFun t1 t2) g)) e t2)
               -> Prop (ExprTy g (EFun f x t1 e) (TFun t1 t2))       
      | E_App  :: g:TEnv -> e1:Expr -> e2:Expr -> t1:Type -> t2:Type 
               -> Prop (ExprTy g e1 (TFun t1 t2))
               -> Prop (ExprTy g e2 t1)
               -> Prop (ExprTy g (EApp e1 e2) t2)
      | E_Pair :: g:TEnv -> e1:Expr -> e2:Expr -> t1:Type -> t2:Type
               -> Prop (ExprTy g e1 t1)
               -> Prop (ExprTy g e2 t2)
               -> Prop (ExprTy g (EPair e1 e2) (TPair t1 t2))
      | E_Fst  :: g:TEnv -> e:Expr -> t1:Type -> t2:Type
               -> Prop (ExprTy g e (TPair t1 t2))
               -> Prop (ExprTy g (EFst e) t1)
      | E_RecordBind :: g:TEnv -> l:Label -> e:Expr -> er:Expr -> t:Type -> tr:TRecord
                     -> Prop (ExprTy g e t)
                     -> Prop (ExprTy g er (TRecord tr))
                     -> Prop (ExprTy g (ERecordBind l e er) (TRecord (TRecordBind l t tr)))
      | E_RecordEmp :: g:TEnv -> Prop (ExprTy g ERecordEmp (TRecord TRecordEmp))
      | E_Forall :: g:TEnv -> x:TVar -> e:Expr -> t:Type
               -> Prop (ExprTy (TTVarBind x g) e t)
               -> Prop (ExprTy g (EForall x e) (TForall x t))       
      | E_TApp :: g:TEnv -> e:Expr -> x:TVar -> t_x:Type -> t_fa:Type
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

-- {-@ evalTApp_safe
--       :: v:Val -> x:TVar -> t_fa:Type -> t_x:Type
--       -> Prop (ValTy v (TForall x t_fa))
--       -> Prop (ResTy (evalTApp v t_x) (substTVar x t_x t_fa))
--   @-}

-- We need to substitute on the inner term (both here and in evalTApp)
-- in order to guarantee that the returned type is going to match
-- (e.g. the inner type might be Forall x. x -> x, but if the outer
--  type is applied to x=Int, then this needs to be substituted in order
--  for the resulting type to match Int -> Int)
-- evalTApp_safe v@(VForallClos x e s) 
--   = eval_safe g' s' e t' (ExprTy g' e t')
--   where
--     t' = (substTVar x t_x t_fa)

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

eval_safe g s (EFun f x t1 e) t (E_Fun _ _ _ _ _ t2 et2) gs 
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

--------------------------------------------------------------------------------
-- | Boilerplate 
--------------------------------------------------------------------------------

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ trivial :: {v:a | false} -> b @-}
trivial :: a -> b
trivial x = trivial x  
