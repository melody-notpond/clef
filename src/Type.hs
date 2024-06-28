module Type (typecheck, makeDeBruijn) where
import Term
import Control.Monad (forM_, when)
import Data.Maybe (isNothing, mapMaybe, isJust)

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
    return $ incrDeBruijn (n + 1) <$> fst (snd $ ctx !! n)

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
wnhf (TVar x) =
  do
    v <- lookupValue x
    wnhf v
wnhf t@(TDeBruijn n) =
  do
    v <- getValue n
    case v of
      Just t' -> wnhf t'
      Nothing -> return t
wnhf t@(TLam {}) =
  -- adding in eta reduction for more flexibility :3
  case eta t of
    t'@(TApp {}) -> wnhf t'
    _ -> return t
wnhf t = return t

equate :: Term -> Term -> Checker ()
equate a b | a == b = return ()
equate a b =
  do
    a' <- wnhf a
    b' <- wnhf b
    ctx <- get
    let ctx' = map fst ctx
    modError (\_ ->
      "could not equate terms " ++
      show (fromDeBruijn ctx' a) ++ " and " ++
      show (fromDeBruijn ctx' b)) $ equate' a' b'

equate' :: Term -> Term -> Checker ()
equate' (TApp f e) (TApp f' e') = equate f f' >> equate e e'
equate' (TLam _ _ e) (TLam _ _ e') = equate e e'
equate' (TPi (Just _) a r) (TPi (Just _) a' r') = equate a a' >> equate r r'
equate' (TPi Nothing a r) (TPi Nothing a' r') = equate a a' >> equate r r'
equate' _ _ = fail ""


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

--       Γ |- f ==> A
-- Γ |- wnhf A ~> ∀(x: A'), B
--       Γ |- e <== A'
-------------------------------IApp
--    Γ |- f e ==> B[e/x]
inferType (TApp f e) =
  do
    t <- inferType f
    t' <- wnhf t
    (a, b) <- case t' of
      TPi Nothing a b -> return (a, b)
      TPi (Just _) a b ->
        let b' = forceBeta b e in
        return (a, b')
      _ -> fail "expected pi/function type"
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

--   Γ |- e <== A
-- Γ |- wnhf A ~> B
----------------------CWnhf
--   Γ |- e <== B
checkType e t =
  do
    t' <- wnhf t
    checkType' e t'

checkType' :: Term -> Term -> Checker ()

--       Γ |- A ==> 𝕌
--     Γ,x:A |- e <== B
------------------------------CLam
-- Γ |- λx.e <== ∀(x: A), B
checkType' (TLam x t e) t_pi@(TPi (Just _) a r) =
  do
    checkType t_pi $ TUni Nothing
    forM_ t (equate a)
    local ((x, (Nothing, a)):) $ checkType e r
checkType' (TLam x t e) t_pi@(TPi Nothing a r) =
  do
    checkType t_pi $ TUni Nothing
    forM_ t (equate a)
    local ((x, (Nothing, a)):) $ checkType e (incrDeBruijn 1 r)
checkType' (TLam {}) _ = fail "lambda is always a pi/function type"

-- Γ |- a ==> A
-- Γ |- A === B
------------------CInfer
-- Γ |- a <== B
checkType' e t =
  do
    t' <- inferType e
    equate t t'
    return ()


-- final typechecking stuff

popArgs :: Term -> [String] -> Checker Term
popArgs t = foldr (\x -> (<$>) (TLam x Nothing)) (return t)

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
    modError (("in `" ++ show x ++ "`'s type: ")++) $
      checkType t $ TUni Nothing
    local ((x, (Nothing, t)):) $ checkTop xs
checkTop (TAssign x args e : xs) =
  do
    valueUndupped x
    (e', t) <- modError (("in `" ++ x ++ "`'s value: ")++) $ do
      t <- lookupType x
      e' <- popArgs e args
      checkType e' t
      return (e', t)
    local (insert x (Just e', t)) $ checkTop xs

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
