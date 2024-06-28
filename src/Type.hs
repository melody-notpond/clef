module Type (typecheck, makeDeBruijn) where
import Term
import Control.Monad (forM_)
import Data.Maybe (isNothing, mapMaybe)

-- {x = e : T}
type Context = [(String, (Maybe Term, Term))]

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

modError :: (String -> String) -> Checker a -> Checker a
modError f x = Checker $ \ctx ->
  case chk x ctx of
    Left e -> Left $ f e
    Right v -> Right v

lookupType :: String -> Checker Term
lookupType x =
  do
    ctx <- get
    case lookupIndex x ctx of
      Just (i, t) -> return $ incrDeBruijn (i + 1) $ snd t
      Nothing -> fail $ "could not find type for `" ++ x ++ "`"

getType :: Int -> Checker Term
getType n =
  do
    ctx <- get
    return $ incrDeBruijn (n + 1) $ snd $ snd $ ctx !! n

lookupValue :: String -> Checker Term
lookupValue x =
  do
    ctx <- get
    case lookup x ctx of
      Just (Just t, _) -> return t
      _ -> fail $ "could not find value for `" ++ x ++ "`"

getValue :: Int -> Checker Term
getValue n =
  do
    ctx <- get
    case snd $ ctx !! n of
      (Just t, _) -> return t
      _ -> fail $ "could not find value for index " ++ show n

-- debug fail
faild :: Maybe Term -> String -> Checker a
faild (Just t) e =
  do
    ctx <- get
    fail $ e ++ "\nwhile checking: " ++ show t ++ "\ncontext: " ++ show ctx
faild Nothing e =
  do
    ctx <- get
    fail $ e ++ "\ncontext: " ++ show ctx

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
beta'' :: Int -> Int -> Term -> Term
beta'' n i (TDeBruijn m) | m >= n = TDeBruijn $ m + i
beta'' n i (TAnn e t) = TAnn (beta'' n i e) (beta'' n i t)
beta'' n i (TPi (Just x) a r) = TPi (Just x) (beta'' n i a) (beta'' n' i r)
  where n' = n + 1
beta'' n i (TPi Nothing a r) = TPi Nothing (beta'' n i a) (beta'' n i r)
beta'' n i (TLam x Nothing e) = TLam x Nothing (beta'' n' i e)
  where n' = n + 1
beta'' n i (TLam x (Just t) e) = TLam x (Just (beta'' n i t)) (beta'' n' i e)
  where n' = n + 1
beta'' n i (TApp f e) = TApp (beta'' n i f) (beta'' n i e)
beta'' _ _ t = t

incrDeBruijn :: Int -> Term -> Term
incrDeBruijn = beta'' 0

beta' :: Int -> Term -> Term -> Term
beta' n (TDeBruijn m) v | n == m = beta'' 0 n v
beta' _ (TDeBruijn m) _ = TDeBruijn $ m - 1
beta' n (TAnn e t) v = TAnn (beta' n e v) (beta' n t v)
beta' n (TPi (Just x) a r) v = TPi (Just x) (beta' n a v) (beta' n' r v)
  where n' = n + 1
beta' n (TPi Nothing a r) v = TPi Nothing (beta' n a v) (beta' n r v)
beta' n (TLam x (Just t) r) v =
  TLam x (Just (beta' n t v)) (beta' n' r v)
  where n' = n + 1
beta' n (TLam x Nothing r) v = TLam x Nothing (beta' n' r v)
  where n' = n + 1
beta' n (TApp f e) v = TApp (beta' n f v) (beta' n e v)
beta' _ e _ = e

beta :: Term -> Term
beta (TApp (TLam _ _ e) v) = beta' 0 e v
beta t = t

forceBeta :: Term -> Term -> Term
forceBeta = beta' 0

eta' :: Int -> Term -> Bool
eta' n (TDeBruijn m) | n == m = False
eta' n (TAnn e t) =  eta' n e && eta' n t
eta' n (TPi (Just _) a r) = eta' n a && eta' n' r
  where n' = n + 1
eta' n (TPi Nothing a r) = eta' n a && eta' n r
eta' n (TLam _ (Just t) r) = eta' n t && eta' n' r
  where n' = n + 1
eta' n (TLam _ Nothing r) = eta' n' r
  where n' = n + 1
eta' n (TApp f e) = eta' n f && eta' n e
eta' _ _ = True

eta :: Term -> Term
eta (TApp (TLam _ _ (TApp f (TDeBruijn 0))) v) | eta' 0 f = TApp f v
eta t = t

used :: Int -> Term -> Bool
used = eta'


unify :: Term -> Term -> Checker ()
unify a b | a == b = return ()
unify a b = faild Nothing $
  "could not unify terms " ++ show a ++ " and " ++ show b


-- here is where we define our type checker, based on a bidirectional typing

inferType :: Term -> Checker Term

------------------IUni
-- Γ |- 𝕌 ==> 𝕌
inferType (TUni _) = return $ TUni Nothing

--   x:T in Γ
------------------IVar
-- Γ |- x ==> T
inferType (TVar x) = lookupType x
inferType (TDeBruijn n) = getType n

-- Γ |- f ==> ∀(x: A), B
--     Γ |- e <== A
---------------------------IApp
--  Γ |- f e ==> B[e/x]
inferType (TApp f e) =
  do
    t_f <- inferType f
    (a, b) <- case t_f of
      TPi Nothing a b -> return (a, b)
      TPi (Just _) a b ->
        let b' = forceBeta b e in
        return (a, b')
      _ -> faild (Just (TAnn f t_f)) "expected pi/function type"
    checkType e a
    return b

--     Γ |- A <== 𝕌
--   Γ,x:A |- B <== 𝕌
---------------------------IPi
-- Γ |- ∀(x: A), B ==> 𝕌
inferType (TPi (Just x) a b) =
  do
    checkType a $ TUni Nothing
    local ((x, (Nothing, a)):) $ checkType b $ TUni Nothing
    return $ TUni Nothing

--    Γ |- A <== 𝕌
--    Γ |- B <== 𝕌
-----------------------IFunc
-- Γ |- A -> B ==> 𝕌
inferType (TPi Nothing a b) =
  do
    checkType a $ TUni Nothing
    checkType b $ TUni Nothing
    return $ TUni Nothing

--   Γ |- A <== 𝕌
--   Γ |- a <== A
---------------------IAnn
-- Γ |- a: A ==> A
inferType (TAnn e t) =
  do
    checkType e t
    return t

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

checkType :: Term -> Term -> Checker ()

--       Γ |- A ==> 𝕌
--     Γ,x:A |- e <== B
------------------------------CLam
-- Γ |- λx.e <== ∀(x: A), B
checkType (TLam x t e) t_pi@(TPi (Just _) a r) =
  do
    checkType t_pi $ TUni Nothing
    forM_ t (unify a)
    local ((x, (Nothing, a)):) $ checkType e r
checkType (TLam x t e) t_pi@(TPi Nothing a r) =
  do
    checkType t_pi $ TUni Nothing
    forM_ t (unify a)
    local ((x, (Nothing, a)):) $ checkType e (incrDeBruijn 1 r)
checkType (TLam {}) _ = fail "lambda is always a pi/function type"

-- Γ |- a ==> A
------------------CInfer
-- Γ |- a <== A
checkType e t =
  do
    t' <- inferType e
    unify t t'
    return ()


-- final typechecking stuff

popArgs :: Term -> [String] -> Checker (Term, [(String, (Maybe Term, Term))])
popArgs t [] = return (t, [])
popArgs (TPi _ a t) (x:xs) =
  do
    (t', xs') <-  popArgs t xs
    return (t', (x, (Nothing, a)):xs')
popArgs t (x:_) = fail $ "couldnt get type for `" ++ x ++ "` from " ++ show t

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
    modError (("in `" ++ show x ++ "`'s type: ")++) $
      checkType t $ TUni Nothing
    local ((x, (Nothing, t)):) $ checkTop xs
checkTop (TAssign x args e : xs) =
  do
    t <- modError (("in `" ++ x ++ "`'s value: ")++) $ do
      t <- lookupType x
      (t', add) <- popArgs t args
      local (add++) $ checkType e t'
      return t
    local (insert x (Just e, t)) $ checkTop xs

makeDeBruijn :: [Top] -> [Top]
makeDeBruijn [] = []
makeDeBruijn (TAssign x args e : xs) =
  TAssign x args (toDeBruijn e) : makeDeBruijn xs
makeDeBruijn (TTyping x t : xs) =
  TTyping x (toDeBruijn t) : makeDeBruijn xs

unmakeDeBruijn
  :: Either String [(String, (Term, Term))]
  -> Either String [(String, (Term, Term))]
unmakeDeBruijn (Left e) = Left e
unmakeDeBruijn (Right []) = Right []
unmakeDeBruijn (Right ((x, (e, t)) : xs)) =
  do
    xs' <- unmakeDeBruijn $ Right xs
    return $ (x, (fromDeBruijn [] e, fromDeBruijn [] t)) : xs'

typecheck :: [Top] -> Either String [(String, (Term, Term))]
typecheck tops = reverse <$>
  unmakeDeBruijn (chk (checkTop (makeDeBruijn tops)) [])
