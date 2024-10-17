module Type (typecheck) where
import Term
import Control.Monad (forM_, when)
import Data.Maybe (isNothing, mapMaybe, isJust)
import Debug.Trace (trace)

-- {x = e : T}
type Context = [(String, (Maybe Term, Term))]

globalContext :: Context
globalContext =
  [
    -- eqInd
    --   : forall A (x: A) (P : A -> Uni), P x -> forall (y: A), x = y -> P y
    ("eqInd", (Just TAssumed, -- HACK
      TPi (Just "A") (TUni 0) $ TPi (Just "x") (TDeBruijn 0) $
      TPi (Just "P") (TPi Nothing (TDeBruijn 1) (TUni 0)) $
      TPi Nothing (TApp (TDeBruijn 0) (TDeBruijn 1)) $
      TPi (Just "y") (TDeBruijn 2) $
      TPi Nothing (TEq (Just $ TDeBruijn 3) (TDeBruijn 2) (TDeBruijn 0)) $
      TApp (TDeBruijn 1) (TDeBruijn 0)))
  ]

-- too lazy to figure out monad transformers
newtype Checker a = Checker
  { chk :: Context -> Either String a }

instance Functor Checker where
  fmap f x = Checker $ \ctx ->
    case chk x ctx of
      Left e -> Left e
      Right v -> Right $ f v

instance Applicative Checker where
  pure x = Checker (\_ -> Right x)
  f <*> x = Checker $ \ctx ->
    case chk f ctx of
      Left e -> Left e
      Right f' ->
        case chk x ctx of
        Left e -> Left e
        Right x' -> Right $ f' x'

instance Monad Checker where
  x >>= f = Checker $ \ctx ->
    case chk x ctx of
      Left e -> Left e
      Right v -> chk (f v) ctx

instance MonadFail Checker where
  fail e = Checker $ \_ -> Left e

get :: Checker Context
get = Checker Right

local :: (Context -> Context) -> Checker a -> Checker a
local f x = Checker $ \ctx ->
  case chk x $ f ctx of
    Left e -> Left e
    Right v -> Right v

modError :: (String -> Context -> String) -> Checker a -> Checker a
modError f x = Checker $ \ctx ->
  case chk x ctx of
    Left e -> Left $ f e ctx
    Right v -> Right v

(??) :: Checker a -> (String -> Context -> String) -> Checker a
x ?? f = modError f x

lookupType :: String -> Checker Term
lookupType x =
  do
    ctx <- get
    case lookupIndex x ctx of
      Just (i, t) -> return $ incrFree (i + 1) $ snd t
      Nothing -> fail $ "could not find type for `" ++ x ++ "`"

getType :: Int -> Checker Term
getType n =
  do
    ctx <- get
    return $ incrFree (n + 1) $ snd $ snd $ ctx !! n

-- variables always have to have a value to be looked up
lookupValue :: String -> Checker Term
lookupValue x =
  do
    ctx <- get
    case lookup x ctx of
      Just (Just t, _) -> return t
      _ -> fail $ "could not find value for `" ++ x ++ "`"

-- bindings dont have to though
getValue :: Int -> Checker (Maybe Term)
getValue n =
  do
    ctx <- get
    return $ incrFree (n + 1) <$> fst (snd $ ctx !! n)

-- debug fail
-- faild :: Maybe Term -> String -> Checker a
-- faild (Just t) e =
--   do
--     ctx <- get
--     fail $ e ++ "\nwhile checking: " ++ show t ++ "\ncontext: " ++ show ctx
-- faild Nothing e =
--   do
--     ctx <- get
--     fail $ e ++ "\ncontext: " ++ show ctx

-- why is this not in the stdlib!
insert :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insert a b [] = [(a, b)]
insert a b ((a', _):xs) | a == a' = (a, b):xs
insert a b (x:xs) = x : insert a b xs

lookupIndex :: Eq a => a -> [(a, b)] -> Maybe (Int, b)
lookupIndex _ [] = Nothing
lookupIndex a ((a', b):_) | a == a' = Just (0, b)
lookupIndex a (_:xs) =
  do
    (i, b) <- lookupIndex a xs
    return (i + 1, b)


-- beta and eta reductions
-- alpha equivalence is just structural so we dont add it
-- beta' is the same as substitution, and eta' is the same as
-- checking for boundedness
incrFree' :: Int -> Int -> Term -> Term
incrFree' l i (TDeBruijn m) | m >= l = TDeBruijn $ m + i
incrFree' l i (TAnn e t) = TAnn (incrFree' l i e) (incrFree' l i t)
incrFree' l i (TPi (Just x) a r) =
  TPi (Just x) (incrFree' l i a) (incrFree' l' i r)
  where l' = l + 1
incrFree' l i (TPi Nothing a r) =
  TPi Nothing (incrFree' l i a) (incrFree' l i r)
incrFree' l i (TLam x Nothing e) = TLam x Nothing (incrFree' l' i e)
  where l' = l + 1
incrFree' l i (TLam x (Just t) e) =
  TLam x (Just (incrFree' l i t)) (incrFree' l' i e)
  where l' = l + 1
incrFree' l i (TApp f e) = TApp (incrFree' l i f) (incrFree' l i e)
incrFree' l i (TEq Nothing a b) =
  TEq Nothing (incrFree' l i a) (incrFree' l i b)
incrFree' l i (TEq (Just t) a b) =
  TEq (Just (incrFree' l i t)) (incrFree' l i a) (incrFree' l i b)
incrFree' l i (TRefl a) = TRefl (incrFree' l i a)
incrFree' _ _ t = t

incrFree :: Int -> Term -> Term
incrFree = incrFree' 0

-- e[n := v]
substVar :: Term -> Int -> Term -> Term
substVar (TDeBruijn m) n v | n == m = incrFree n v
substVar (TAnn e t) n v = TAnn (substVar e n v) (substVar t n v)
substVar (TPi (Just x) a r) n v =
  TPi (Just x) (substVar a n v) (substVar r n' v)
  where n' = n + 1
substVar (TPi Nothing a r) n v = TPi Nothing (substVar a n v) (substVar r n v)
substVar (TLam x (Just t) r) n v =
  TLam x (Just (substVar t n v)) (substVar r n' v)
  where n' = n + 1
substVar (TLam x Nothing r) n v = TLam x Nothing (substVar r n' v)
  where n' = n + 1
substVar (TApp f e) n v = TApp (substVar f n v) (substVar e n v)
substVar (TEq Nothing a b) n v = TEq Nothing (substVar a n v) (substVar b n v)
substVar (TEq (Just t) a b) n v =
  TEq (Just (substVar t n v)) (substVar a n v) (substVar b n v)
substVar (TRefl a) n v = TRefl (substVar a n v)
substVar e _ _ = e

beta :: Term -> Term
beta (TApp (TLam _ _ e) v) = substVar (incrFree' 1 (-1) e) 0 v
beta t = t

instantiatePi :: Term -> Term -> Maybe (Term, Term)
instantiatePi (TPi (Just _) a b) v = Just (a, substVar (incrFree' 1 (-1) b) 0 v)
instantiatePi (TPi Nothing a b) _ = Just (a, b)
instantiatePi _ _ = Nothing

-- eta' :: Int -> Term -> Bool
-- eta' n (TDeBruijn m) | n == m = False
-- eta' n (TAnn e t) =  eta' n e && eta' n t
-- eta' n (TPi (Just _) a r) = eta' n a && eta' n' r
--   where n' = n + 1
-- eta' n (TPi Nothing a r) = eta' n a && eta' n r
-- eta' n (TLam _ (Just t) r) = eta' n t && eta' n' r
--   where n' = n + 1
-- eta' n (TLam _ Nothing r) = eta' n' r
--   where n' = n + 1
-- eta' n (TApp f e) = eta' n f && eta' n e
-- eta' _ _ = True

-- eta :: Term -> Term
-- eta (TApp (TLam _ _ (TApp f (TDeBruijn 0))) v) | eta' 0 f = TApp f v
-- eta t = t


-- equality

-- weak normal head form
-- pi-forall uses this because nontermination + efficiency, so we will here too
-- nontermination shouldnt be an issue though afaik
wnhf :: Term -> Checker Term
wnhf (TApp f e) =
  do
    f' <- wnhf f
    case f' of
      TLam {} ->
        wnhf (beta (TApp f' e))
      _ -> return $ TApp f' e
wnhf (TAnn e _) = wnhf e
wnhf (TGlobal x) =
  do
    v <- lookupValue x
    wnhf v
wnhf t@(TDeBruijn n) =
  do
    v <- getValue n
    case v of
      Just t' -> wnhf t'
      Nothing -> return t
wnhf t = return t

equate :: Term -> Term -> Checker ()
equate a b | a == b = return ()
equate (TUni _) (TUni _) = return () -- HACK
equate a b =
  do
    a' <- wnhf a
    b' <- wnhf b
    modError (\s ctx -> s ++ "\n  " ++
      let c = map fst ctx in
      "could not equate terms " ++ showWith a c ++
      " and " ++ showWith b c ++ "\n\n") $ equate' a' b'

equate' :: Term -> Term -> Checker ()
equate' (TApp f e) (TApp f' e') = equate f f' >> equate e e'
equate' (TLam x _ e) (TLam _ _ e') =
  local ((x, (Nothing, TAssumed)):) $ equate e e'
equate' (TPi (Just x) a r) (TPi (Just _) a' r') = equate a a' >>
  local ((x, (Nothing, TAssumed)):) (equate r r')
equate' (TPi Nothing a r) (TPi Nothing a' r') = equate a a' >> equate r r'
equate' (TEq (Just t) a b) (TEq (Just t') a' b') =
  equate t t' >> equate a a' >> equate b b'
equate' (TEq Nothing a b) (TEq Nothing a' b') = equate a a' >> equate b b'
equate' (TRefl a) (TRefl b) = equate a b
equate' _ _ = fail ""


-- here is where we define our type checker, based on a bidirectional typing

inferType :: Term -> Checker Term

------------------------IUni
-- Γ |- 𝕌#u ==> 𝕌#u+1
inferType (TUni u) = return $ TUni u -- $ u + 1

--   x:T in Γ
------------------IVar
-- Γ |- x ==> T
inferType (TGlobal x) = lookupType x
inferType (TDeBruijn n) = getType n

--       Γ |- f ==> A
-- Γ |- wnhf A ~> ∀(x: A'), B
--       Γ |- e <== A'
-------------------------------IApp
--    Γ |- f e ==> B[e/x]
inferType app@(TApp f e) =
  do
    t <- inferType f
    t' <- wnhf t
    (a, b) <- case instantiatePi t' e of
      Just (a, b) -> return (a, b)
      Nothing -> fail "expected pi/function type"
    checkType e a
    return b
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith app c' ++ " ==> ??\n"

--     Γ |- A <== 𝕌#u
--   Γ,x:A |- B <== 𝕌#u
---------------------------IPi
-- Γ |- ∀(x: A), B ==> 𝕌#u
inferType pii@(TPi (Just x) a b) =
  do
    checkType a $ TUni 0
    local ((x, (Nothing, a)):) $ checkType b $ TUni 0
    return $ TUni 0
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith pii c' ++ " ==> ??\n"

--    Γ |- A <== 𝕌
--    Γ |- B <== 𝕌
-----------------------IFunc
-- Γ |- A -> B ==> 𝕌
inferType pii@(TPi Nothing a b) =
  do
    checkType a $ TUni 0
    checkType b $ TUni 0
    return $ TUni 0
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith pii c' ++ " ==> ??\n"

--   Γ |- A <== 𝕌
--   Γ |- a <== A
---------------------IAnn
-- Γ |- a: A ==> A
inferType ann@(TAnn e t) =
  do
    checkType e t
    return t
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith ann c' ++ " ==> ??\n"

--       Γ |- A <== 𝕌
--     Γ,x:A |- e ==> B
------------------------------ILam
-- Γ |- λx.e ==> ∀(x: A), B
-- inferType (TLam x (Just t) e) =
--   do
--     checkType t $ TUni Nothing
--     r <- local ((x, (Nothing, t)):) $ inferType e
--     let r' = toDeBruijn' [x] r
--     if r == r' then
--       return $ TPi Nothing t r'
--     else
--       return $ TPi (Just x) t r'
inferType (TLam {}) = fail "type inference of lambdas is unsupported"

inferType eq@(TEq (Just t) a b) =
  do
    checkType a t
    checkType b t
    return $ TUni 0
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith eq c' ++ " ==> ??\n"

inferType eq@(TEq Nothing a b) =
  do
    t <- inferType a
    checkType b t
    return $ TUni 0
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith eq c' ++ " ==> ??\n"

inferType _ = fail "TODO"

checkType :: Term -> Term -> Checker ()

--   Γ |- e <== A
-- Γ |- wnhf A ~> B
----------------------CWnhf
--   Γ |- e <== B
checkType e t =
  do
    t' <- wnhf t
    checkType' e t'
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith e c' ++ " <== " ++ showWith t c' ++ "\n"

checkType' :: Term -> Term -> Checker ()

--     u' > u
------------------IUni
-- Γ |- 𝕌#u <== 𝕌#u'
checkType' (TUni _u) (TUni _u') =
  return ()
  -- if u' > u then
  --   return ()
  -- else fail $ show (TUni u) ++ " cannot be in universe " ++ show (TUni u')


--       Γ |- A ==> 𝕌
--     Γ,x:A |- e <== B
------------------------------CLam
-- Γ |- λx.e <== ∀(x: A), B
checkType' lam@(TLam x t e) t_pi@(TPi (Just _) a r) =
  do
    checkType t_pi $ TUni 0
    forM_ t (equate a)
    local ((x, (Nothing, a)):) $ checkType e r
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith lam c' ++ " <== " ++ showWith t_pi c' ++ "\n"
checkType' lam@(TLam x t e) t_pi@(TPi Nothing a r) =
  do
    checkType t_pi $ TUni 0
    forM_ t (equate a)
    local ((x, (Nothing, a)):) $ checkType e (incrFree 1 r)
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith lam c' ++ " <== " ++ showWith t_pi c' ++ "\n"
checkType' (TLam {}) _ = fail "lambda is always a pi/function type"

--          Γ |- A <== 𝕌
--          Γ |- a <== A
------------------------------------
--    Γ |- refl(A) a <== a =(A) a
checkType' refl@(TRefl a) t_eq@(TEq t' x y) =
  do
    checkType t_eq $ TUni 0
    forM_ t' (checkType a)
    equate a x
    equate a y
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith refl c' ++ " <== " ++ showWith t_eq c' ++ "\n"

-- Γ |- a ==> A
-- Γ |- A === B
------------------CInfer
-- Γ |- a <== B
checkType' e t =
  do
    t' <- inferType e
    equate t t'
    return ()
  ?? \s c ->
    let c' = map fst c in
    s ++ "  during " ++ showWith e c' ++ " <== " ++ showWith t c' ++ "\n"


-- final typechecking stuff

typeUndupped :: String -> Checker ()
typeUndupped x =
  do
    ctx <- get
    when (isJust $ lookup x ctx) $ fail $
      "`" ++ show x ++ "` has two type declarations"

valueUndupped :: String -> Checker ()
valueUndupped x =
  do
    ctx <- get
    case lookup x ctx of
      Just (Just _, _) -> fail $
        "`" ++ show x ++ "` has two definitions"
      _ -> return ()

checkTop :: [Top] -> Checker [(String, (Term, Term))]
checkTop [] =
  do
    ctx <- get
    let undefed = filter (isNothing . fst . snd) ctx
    case undefed of
      (_:_) -> fail $ "no definitions for the following: "
        ++ foldl (\b (a, _) -> b ++ "\n" ++ show a) "" undefed
      [] -> return $ mapMaybe
        (\(s, (e, t)) -> case e of
          Just e' -> Just (s, (e', t))
          Nothing -> Nothing)
        ctx
checkTop (TTyping x t : xs) =
  do
    typeUndupped x
    modError (\s _ -> "in `" ++ x ++ "`'s type: " ++ s) $
      checkType t $ TUni 0
    local ((x, (Nothing, t)):) $ checkTop xs
checkTop (TAssign x e : xs) =
  do
    valueUndupped x
    t <- modError (\s _ -> "in `" ++ x ++ "`'s value: " ++ s) $ do
      t <- lookupType x
      checkType e t
      return t
    local (insert x (Just e, t)) $ checkTop xs

typecheck :: [Top] -> Either String [(String, (Term, Term))]
typecheck tops = reverse <$> chk (checkTop tops) globalContext
