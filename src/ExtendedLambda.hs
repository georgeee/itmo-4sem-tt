{-# LANGUAGE PackageImports, FlexibleContexts #-}
module ExtendedLambda where

import Debug.Trace
import Data.List
import Common
import Data.Foldable as F
import Data.Maybe
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Trans.Either
import Control.Monad.Error.Class
import Control.Monad.State.Strict
import Text.Parsec hiding ((<|>), many, State, oneOf)
import Control.Applicative
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS

data IOp = Add | Subtract
iop :: IOp -> Integer -> Integer -> Integer
iop Add = (+)
iop Subtract = (-)

infixl 4 :~
infixl 3 :@

type ELContext = HM.HashMap Var ExtendedLambda

infixl 2 ::=
data ExtendedLambda = ELContext ::= ExtendedLambdaBase

noContext = (HM.empty ::=)

data ExtendedLambdaBase = I Integer
                    | B Bool
                    | Y
                    | PrL
                    | PrR
                    | InL
                    | InR
                    | Case
                    | If
                    | IOp IOp
                    | OrdOp Ordering
                    | ExtendedLambda :~ ExtendedLambda --pair
                    | Abs Var ExtendedLambda
                    | ExtendedLambda :@ ExtendedLambda
                    | V Var

instance Show ExtendedLambda where
  show = show' 0

instance Show ExtendedLambdaBase where
  show = show'' 0

p i s = (replicate (i*2) ' ') ++ s
sps = flip replicate ' '
show' :: Int -> ExtendedLambda -> String
show' i (bs ::= t) = if HM.null bs then show'' i t else let i' = i + 1 in
            concat [ "\n" ++ (sps $ i * 2) ++ "(let " ++ (intercalate (",\n" ++ (sps $ i * 2 + 4)) $ showLBs i' bs)
                   , "\n" ++ (sps $ i' * 2 - 1) ++ "in " ++ (show'' i' t) ++ ")"
                   ]
show'' _ (I x) = show x
show'' _ (B b) = if b then "T" else "F"
show'' _ Y = "Y"
show'' _ PrL = "PrL"
show'' _ PrR = "PrR"
show'' _ InL = "InL"
show'' _ InR = "InR"
show'' _ Case = "Case"
show'' _ If = "If"
show'' _ (IOp Add) = "Plus"
show'' _ (IOp Subtract) = "Minus"
show'' _ (OrdOp EQ) = "Eq"
show'' _ (OrdOp LT) = "Lt"
show'' _ (OrdOp GT) = "Gt"
show'' i (l :~ r) = let i' = i + 1 in "<" ++ (show' i' l) ++ ", " ++ (show' i' r) ++ ">"
show'' i (Abs v e) = let i' = i + 1 in "(\\" ++ v ++ ". " ++ (show' i' e) ++ ")"
show'' i (l :@ r) = let i' = i + 1 in (show' i' l) ++ " " ++ (show''' i' r)
show'' _ (V v) = v

show''' i r@(_ ::= _ :@ _) = "(" ++ (show' i r) ++ ")"
show''' i r = show' i r

showLBs i = map (\(v, s) -> v ++ " = " ++ (show' i s)) . HM.toList

spaces1 :: Stream s m Char => ParsecT s u m ()
spaces1 = skipMany1 space

integer :: (Stream s m Char, Integral a, Read a) => ParsecT s u m a
integer = read <$> (many1 digit)

infixl 4 <*!
infixl 4 <**
infixl 4 **>
infixl 4 !*>
x <*! y = x <* spaces1 <* y
x <** y = x <* spaces  <* y
x !*> y = x *> spaces1 *> y
x **> y = x *> spaces  *> y

mergeContexts :: MonadState Int m => ELContext -> ELContext -> m ELContext
mergeContexts l1 l2 = HM.fromList <$> modifyLs HM.empty (l2' ++ l1')
  where l1' = HM.toList l1
        l2' = HM.toList l2
        modifyLs _ [] = return []
        modifyLs vs ((v, e):as) = if v `HM.member` vs
                                     then freshId v >>= \v' -> let vs' = HM.insert v (noContext $ V v') vs
                                                                in (:) . (,) v' <$> repl vs' e <*> modifyLs vs' as
                                     else let vs' = HM.insert v (noContext $ V v) vs
                                           in (:) . (,) v <$> repl vs' e <*> modifyLs vs' as
        repl = replaceAllFree

mergeContexts' l1 (l2 ::= e) = (::= e) <$> mergeContexts l1 l2

parsecRunState m = getState >>= \s -> let (a, s') = runState m s
                                       in putState s' >> return a

elParse :: (Stream s m Char) => ParsecT s Int m ExtendedLambda
elParse = expr
  where expr = letE <|> (abs <|> appsAbs)
        abs = (\v e -> noContext $ Abs v e) <$> (char '\\' **> var')
                    <*> (spaces *> (string "." <|> string "->") **> expr)
        letE = do ls <- (try (string "let" *> space) **> (HM.fromList <$> sepBy1 letBind (spaces *> char ',' *> spaces)) <* spaces)
                  e <- (try (string "in" *> space) **> expr)
                  parsecRunState (mergeContexts' ls e)
        letBind = (,) <$> var' <*> (spaces *> char '=' **> expr)
        apps = many1 (atom <* spaces)
        appsAbs = impl <$> apps <*> ((Just <$> abs) <|> pure Nothing)
          where impl :: [ExtendedLambda] -> Maybe ExtendedLambda -> ExtendedLambda
                impl es m = impl' $ maybe id (:) m es
                impl' (a:[]) = a
                impl' (a:as) = foldl (\b e -> noContext $ b :@ e) a as
        atom = letE <|> parens' expr
             <|> (noContext <$> ((I <$> integer)
                            <|> (B <$> (try $ (char 'T' *> pure True) <|> (char 'F' *> pure False)))
                            <|> (try $ char 'Y' *> pure Y)
                            <|> (try (string "PrL") *> pure PrL)
                            <|> (try (string "PrR") *> pure PrR)
                            <|> (try (string "InL") *> pure InL)
                            <|> (try (string "InR") *> pure InR)
                            <|> (try (string "Case") *> pure Case)
                            <|> (try (string "If") *> pure If)
                            <|> (try (string "Plus") *> pure (IOp Add))
                            <|> (try (string "Minus") *> pure (IOp Subtract))
                            <|> (try (string "Eq") *> pure (OrdOp EQ))
                            <|> (try (string "Lt") *> pure (OrdOp LT))
                            <|> (try (string "Gt") *> pure (OrdOp GT))
                            <|> ((:~) <$> (char '<' **> expr) <*> (spaces *> char ',' **> expr <** char '>'))
                            <|> (V <$> var') ) )
        var' = try $ checkNotKeyWord =<< var

checkNotKeyWord :: (Monad m) => Var -> m Var
checkNotKeyWord x = if x `elem` ["in", "let"]
                       then fail $ x ++ " is reserved as a keyword"
                       else return x

testElParse = testParser elParse 0

testElParseSt :: MonadState Int m => String -> m ExtendedLambda
testElParseSt = testParserSt elParse

freshId :: (Num s, Show s, MonadState s f) => String -> f String
freshId x = (('_' : x) ++ ) . show <$> (get <* modify (+1))

infixl 4 <.$>
infixl 4 <.*>

(<.$>) :: (Functor f, Functor g) => (a -> b) -> g (f a) -> g (f b)
f <.$> g = fmap f <$> g

(<.*>) :: (Applicative f, Monad m) => m (f (a -> b)) -> m (f a) -> m (f b)
mf <.*> mg = mf >>= \fab -> mg >>= \fa -> return $ fab <*> fa

insertWithReplace :: MonadState Int m => Var -> ExtendedLambda -> HM.HashMap Var ExtendedLambda -> m (HM.HashMap Var ExtendedLambda)
insertWithReplace x e m = HM.insert x e <$> mapM (replaceAllFree (HM.singleton x e)) m

normalizeRecursion :: MonadState Int m => ExtendedLambda -> m ExtendedLambda
normalizeRecursion e = snd <$> impl e
  where -- returns (expr with recursion replaced, set of free variables inside resulting expression)
        impl (ls ::= e) = (::=) <.$> replaceLB' <.*> impl' e
          where allLetVars = HM.fromList $ zip (HM.keys ls) [1..]
                replaceLB' = (\(ls, _, ls') -> HM.fromList $ reverse ls ++ ls') <.$> foldM (replaceLB allLetVars) (HS.empty, ([], HM.empty, [])) (zip [1..] $ HM.toList ls)
        impl' (a :~ b) = (:~) <.$> impl a <.*> impl b
        impl' (a :@ b) = (:@) <.$> impl a <.*> impl b
        impl' (Abs v e) = impl e >>= \(fv, e') -> return (HS.delete v fv, Abs v e')
        impl' e@(V v) = return (HS.singleton v, e)
        impl' e = return $ pure e


        replaceLB vs (fv0, (bs, rm, newLbs)) (i, (x, e))
            = replaceAllFree rm e >>= impl >>= \(fv, e') ->
              let needY = x `HS.member` fv
                  -- fv' is a set of vars of same let, comming after current (if not empty, wee need to present new var x0)
                  fv' = HM.keys $ HM.filterWithKey (\k i' -> HS.member k fv && i' > i) vs
                  resE e'' = if needY then noContext $ noContext Y :@ noContext (Abs x e'') else e''
                  resFV = fv0 `mappend` HS.delete x fv
               in if F.null fv'
                     then return (resFV, ((x ,resE e'):bs, rm, newLbs))
                     else freshId x >>= \n ->
                       let replacement = noContext $ foldr' (\a b -> noContext b :@ noContext (V a)) (V n) (reverse fv')
                           e'' = foldr' (\v e -> noContext $ Abs v e) e' fv'
                        in insertWithReplace x replacement rm
                            >>= \rm' ->return (resFV, ((n ,resE e''):bs, rm', (x, replacement):newLbs))

freeVars :: ExtendedLambda -> HS.HashSet Var
freeVars el = execState (fvs' HS.empty el) HS.empty
  where fvs i (a :~ b) = fvs' i a >> fvs' i b
        fvs i (a :@ b) = fvs' i a >> fvs' i b
        fvs i (Abs v e) = fvs' (v `HS.insert` i) e
        fvs i (V v) = if v `HS.member` i then return () else modify (HS.insert v)
        fvs _ _ = return ()
        fvs' i (ls ::= e) = mapM_ (fvs' i') ls >> fvs i' e
          where i' = foldr HS.insert i $ HM.keys ls


renameBound :: MonadState Int m => HS.HashSet Var -> ExtendedLambda -> m ExtendedLambda
renameBound fv = impl HM.empty
  where impl m (ls ::= e) = m' >>= \m'' -> (::=) <$> (HM.fromList <$> mapM (implLB m'') (HM.toList ls)) <*> impl' m'' e
          where implLB m'' (v, e) = (,) (maybe v id $ v `HM.lookup` m'') <$> impl m'' e
                m' = foldM (\m v -> freshId v >>= \u -> return $ HM.insert v u m) m $ filter (flip HS.member fv) $ HM.keys ls
        impl' m (l :~ r) = (:~) <$> impl m l <*> impl m r
        impl' m (l :@ r) = (:@) <$> impl m l <*> impl m r
        impl' m (Abs v e) = if v `HS.member` fv
                               then freshId v >>= \u -> Abs u <$> impl (HM.insert v u m) e
                               else Abs v <$> impl m e
        impl' m (V v) = return $ V $ case v `HM.lookup` m of
                                 Just u -> u
                                 Nothing -> v
        impl' m e = return e

--trace' x y = \x y -> y
trace' x y = y >>= \y' -> trace (x ++ " ==> " ++ (show y')) (return y')

replaceAllFree :: MonadState Int m => HM.HashMap Var ExtendedLambda -> ExtendedLambda -> m ExtendedLambda
replaceAllFree vs e = impl =<< renameBound fv e
  where impl (ls ::= e) = trace' "replaceFree: let" $ do e' <- impl' e
                                                         ls' <- traverse impl ls
                                                         mergeContexts' ls' e'
        impl' (l :~ r) = trace' "replaceFree: pair" $ (\l' r' -> noContext $ l' :~ r') <$> impl l <*> impl r
        impl' (Abs v e) = trace' "replaceFree: abs" $ (noContext . Abs v) <$> impl e
        impl' (l :@ r) = trace' "replaceFree: app" $ (\l' r' -> noContext $ l' :@ r') <$> impl l <*> impl r
        impl' e@(V v) = trace' ("replaceFree: V " ++ v) $ return $ case HM.lookup v vs of
                          Just n -> n
                          Nothing -> noContext e
        impl' e = trace' ("replaceFree: other " ++ (show e)) $ return $ noContext e
        fv = foldr' (flip mappend . freeVars) (HS.fromList $ HM.keys vs) vs

type NormMonad a = EitherT a (StateT Int (Except String)) a

toRight :: Functor n => EitherT b n b -> EitherT e' n b
toRight = mapEitherT (fmap $ either Right Right)

runNormMonad :: NormMonad a -> Either String a
runNormMonad = fmap (either id id) . runNormMonad'

runNormMonad' :: NormMonad a -> Either String (Either a a)
runNormMonad' = runExcept . flip evalStateT 0 . runEitherT

testNormMonad :: (ExtendedLambda -> NormMonad a) -> String -> Either String (Either a a)
testNormMonad m s = runNormMonad' (testElParseSt s >>= normalizeRecursion >>= m)

--normalize1 :: ExtendedLambda -> Either String ExtendedLambda
--normalize1 = runNormMonad . (normalize')
--
-- normalizeNp :: ExtendedLambda -> Either String ExtendedLambda
-- normalizeNp = runNormMonad . (steps)
--   where steps = lift . normalizeRecursion >=> normalize' >=> steps
-- normalize :: ExtendedLambda -> Either String ExtendedLambda
-- normalize = runNormMonad . (toRight . steps >=> lift . propagateLets)
--   where steps = lift . normalizeRecursion >=> normalize' >=> steps

oneOf :: (Monad m) => (a -> a -> a) -> EitherT a m a -> EitherT a m a -> EitherT a m a
oneOf b l r = (l >>= \l' -> b l' <$> toRight r) `catchError` (\l' -> (b l' <$> r) `catchError` (left . b l'))

infixl 4 <?$>
(<?$>) :: Monad m => (a -> a) -> EitherT a m a -> EitherT a m a
(<?$>) f m = (f <$> m) `catchError` (left . f)

infixl 4 <?*>
(<?*>) :: Monad m => EitherT a m (a -> a) -> EitherT a m a -> EitherT a m a
(<?*>) f m = f >>= (<?$> m)

infixl 2 >>=+
(>>=+) :: NormMonad ExtendedLambda -> (ExtendedLambda -> NormMonad ExtendedLambda) -> NormMonad ExtendedLambda
ma >>=+ f = ma >>= \x -> toRight (if isWHNF x then f x else return x)
infixl 2 >>=!
(>>=!) :: NormMonad a -> (a -> NormMonad a) -> NormMonad a
ma >>=! f = ma >>= toRight . f

ordOp ord i j = compare i j == ord

isWHNF (_ ::= (_ :@ _)) = False
isWHNF _ = True

elIfTrue = noContext . Abs "x" . noContext . Abs "y" . noContext $ V "x"
elIfFalse = noContext . Abs "x" . noContext . Abs "y" . noContext $ V "y"

mkApp2 :: ExtendedLambdaBase -> ExtendedLambda -> ExtendedLambda
mkApp2 e = noContext . (noContext e :@)

mkApp3 :: ExtendedLambdaBase -> ExtendedLambdaBase -> ExtendedLambda -> ExtendedLambda
mkApp3 e1 e2 = noContext . ((:@) . noContext $ noContext e1 :@ noContext e2)

normalize' :: ExtendedLambda -> NormMonad ExtendedLambda
normalize' = impl HM.empty
  where impl :: HM.HashMap Var ExtendedLambda -> ExtendedLambda -> NormMonad ExtendedLambda
        impl m (ls ::= e) = (impl' m' e >>= lift . mergeContexts' ls) `catchError` (lift . mergeContexts' ls >=> left)
          where m' = foldr' (uncurry HM.insert) m $ HM.toList ls
        impl' :: HM.HashMap Var ExtendedLambda -> ExtendedLambdaBase -> NormMonad ExtendedLambda
        impl' m ((_ ::= If) :@ (_ ::= B b)) = trace "if1 " $ return $ if b then elIfTrue else elIfFalse
        impl' m ((_ ::= If) :@ p) = trace "if2 " $ mkApp2 If <?$> impl m p >>=+ impl m
        impl' m ((_ ::= (_ ::= IOp op) :@ (_ ::= I i)) :@ (_ ::= I j)) = trace "iop1 " $ return . noContext . I $ iop op i j
        impl' m ((_ ::= (_ ::= IOp op) :@ (_ ::= I i)) :@ p) = trace "iop2 " $ mkApp3 (IOp op) (I i) <?$> impl m p >>=+ impl m
        impl' m ((_ ::= IOp op) :@ p) = trace "iop3 " $ mkApp2 (IOp op) <?$> impl m p >>=+ impl m
        impl' m ((_ ::= (_ ::= OrdOp op) :@ (_ ::= I i)) :@ (_ ::= I j)) = trace "ordOp1 " $ return . noContext . B $ ordOp op i j
        impl' m ((_ ::= (_ ::= OrdOp op) :@ (_ ::= I i)) :@ p) = trace "ordOp2 " $ mkApp3 (OrdOp op) (I i) <?$> impl m p >>=+ impl m
        impl' m ((_ ::= OrdOp op) :@ p) = trace "ordOp3 " $ mkApp2 (OrdOp op) <?$> impl m p >>=+ impl m
        --impl' m ((_ ::= Y) :@ f) = trace "Y " $ return (f :@ (Y :@ f)) >>=! impl m
        impl' m ((_ ::= PrL) :@ (_ ::= a :~ b)) = trace "PrL1 " $ toRight $ impl m a
        impl' m ((_ ::= PrR) :@ (_ ::= a :~ b)) = trace "PrR1 " $ toRight $ impl m b
        impl' m ((_ ::= PrL) :@ p) = trace "PrL2 " $ mkApp2 PrL <?$> impl m p >>=+ impl m
        impl' m ((_ ::= PrR) :@ p) = trace "PrR2 " $ mkApp2 PrR <?$> impl m p >>=+ impl m
        impl' m ((ctx1 ::= (ctx2 ::= (_ ::= Case) :@ (xCtx ::= (_ ::= InL) :@ x)) :@ l) :@ r) = trace "Case1 " $ do
                  ctxX <- lift (mergeContexts ctx2 xCtx)
                  x' <- lift (mergeContexts' ctxX x)
                  toRight $ impl m $ ctx1 ::= x' :@ l
        impl' m ((ctx1 ::= (ctx2 ::= (_ ::= Case) :@ (xCtx ::= (_ ::= InR) :@ x)) :@ l) :@ r) = trace "Case2 " $ do
                  ctx12x <- lift (mergeContexts ctx1 ctx2 >>= mergeContexts xCtx)
                  x' <- lift (mergeContexts' ctx12x x)
                  toRight $ impl m $ noContext $ x' :@ r
        impl' m ((_ ::= Case) :@ p) = trace "Case3 " $ mkApp2 Case <?$> impl m p >>=+ impl m
        impl' m o@((_ ::= Abs v s) :@ e) = trace "Abs " $ toRight $ impl (HM.insert v e m) =<< lift (mergeContexts' (HM.singleton v e) s)
        impl' m e@(l :@ r) = trace "App1 " $ (noContext . (:@ r) <?$> impl m l) >>=+ impl m
        impl' m (V v) = trace ("Var " ++ (show $ (v, v `HM.lookup` m))) $ case v `HM.lookup` m of
                          Just e -> return e
                          _ -> left $ noContext (V v)
        impl' _ e = trace ("Other: " ++ (show e)) $ left $ noContext e




