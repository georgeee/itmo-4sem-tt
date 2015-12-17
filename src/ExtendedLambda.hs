{-# LANGUAGE PackageImports, FlexibleContexts #-}
module ExtendedLambda where

import Data.List
import Common
import Data.Foldable as F
import Data.Maybe
import Control.Monad.Except
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

infixl 1 ::=
data LetBinding = (::=) Var ExtendedLambda

infixl 3 :~
infixl 2 :@
data ExtendedLambda = Let [LetBinding] ExtendedLambda
                    | I Integer
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
    where p i s = (replicate (i*2) ' ') ++ s
          sps = flip replicate ' '
          show' :: Int -> ExtendedLambda -> String
          show' i (Let bs t) = let i' = i + 1 in
                      concat [ (sps $ i * 2) ++ "let " ++ (intercalate (",\n" ++ (sps $ i * 2 + 4)) $ map (showLB i') bs)
                             , (sps $ i' * 2) ++ "in " ++ (show' i' t)
                             ]
          show' _ (I x) = show x
          show' _ (B b) = if b then "T" else "F"
          show' _ Y = "Y"
          show' _ PrL = "PrL"
          show' _ PrR = "PrR"
          show' _ InL = "InL"
          show' _ InR = "InR"
          show' _ Case = "Case"
          show' _ If = "If"
          show' _ (IOp Add) = "Plus"
          show' _ (IOp Subtract) = "Minus"
          show' _ (OrdOp EQ) = "Eq"
          show' _ (OrdOp LT) = "Lt"
          show' _ (OrdOp GT) = "Gt"
          show' i (l :~ r) = let i' = i + 1 in "<" ++ (show' i' l) ++ ", " ++ (show' i' r) ++ ">"
          show' i (Abs v e) = let i' = i + 1 in "\\" ++ v ++ ". " ++ (show' i' e)
          show' i (e@(Abs _ _) :@ r) = let i' = i + 1 in "(" ++ (show' i' e) ++ ") " ++ (show'' i' r)
          show' i (l :@ r) = let i' = i + 1 in (show' i' l) ++ " " ++ (show'' i' r)
          show' _ (V v) = v

          show'' i r@(_ :@ _) = "(" ++ (show' i r) ++ ")"
          show'' i r = show' i r

          showLB i (v ::= s) = v ++ " = " ++ (show' i s)

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

elParse :: (Stream s m Char) => ParsecT s u m ExtendedLambda
elParse = expr
  where expr = letE <|> abs <|> (appsAbs <$> apps <*> ((Just <$> abs) <|> pure Nothing))
        abs = Abs <$> (char '\\' **> var')
                    <*> (spaces *> (string "." <|> string "->") **> expr)
        letE = Let <$> (try (string "let" *> space) **> sepBy1 letBind (spaces *> char ',' *> spaces) <* spaces)
                    <*> (try (string "in" *> space) **> expr)
        letBind = (::=) <$> var' <*> (spaces *> char '=' **> expr)
        apps = foldl1 (:@) <$> many1 (atom <* spaces)
        appsAbs e = maybe e (e :@)
        atom = parens' expr <|> (I <$> integer)
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
                           <|> (V <$> var')
        var' = try $ checkNotKeyWord =<< var

checkNotKeyWord :: (Monad m) => Var -> m Var
checkNotKeyWord x = if x `elem` ["in", "let"]
                       then fail $ x ++ " is reserved as a keyword"
                       else return x

testElParse = testParser elParse

type NMonad a = StateT Int (Except String) (HS.HashSet Var, a)
type RLBPair = ([LetBinding], HM.HashMap Var ExtendedLambda, [LetBinding])

lbVar (v ::= _) = v
lbExpr (_ ::= e) = e

infixl 4 <.$>
infixl 4 <.*>

(<.$>) :: (Functor f, Functor g) => (a -> b) -> g (f a) -> g (f b)
f <.$> g = fmap f <$> g

(<.*>) :: (Applicative f, Monad m) => m (f (a -> b)) -> m (f a) -> m (f b)
mf <.*> mg = mf >>= \fab -> mg >>= \fa -> return $ fab <*> fa

normalizeRecursion :: ExtendedLambda -> StateT Int (Except String) ExtendedLambda
normalizeRecursion e = snd <$> impl e
  where -- returns (expr with recursion replaced, set of free variables inside resulting expression)
        impl :: ExtendedLambda -> NMonad ExtendedLambda
        impl (Let ls e) = Let <.$> replaceLB' <.*> impl e
          where allLetVars = HM.fromList $ zip (map lbVar ls) [1..]
                replaceLB' = (\(ls, _, ls') -> reverse ls ++ ls') <.$> foldM (replaceLB allLetVars) (HS.empty, ([], HM.empty, [])) (zip [1..] ls)
        impl (a :~ b) = (:~) <.$> impl a <.*> impl b
        impl (a :@ b) = (:@) <.$> impl a <.*> impl b
        impl (Abs v e) = impl e >>= \(fv, e') -> return (HS.delete v fv, Abs v e')
        impl e@(V v) = return (HS.singleton v, e)
        impl e = return $ pure e


        replaceLB :: HM.HashMap Var Int -> (HS.HashSet Var, RLBPair) -> (Int, LetBinding) -> NMonad RLBPair
        replaceLB vs (fv0, (bs, rm, newLbs)) (i, x ::= e)
            = replaceAllFree rm e >>= impl >>= \(fv, e') ->
              let needY = x `HS.member` fv
                  -- fv' is a set of vars of same let, comming after current (if not empty, wee need to present new var x0)
                  fv' = HM.keys $ HM.filterWithKey (\k i' -> HS.member k fv && i' > i) vs
                  exprs n = (foldr' (flip (:@) . V) (V n) $ reverse fv', foldr' Abs e' fv')
                  resE e'' = if needY then Y :@ Abs x e'' else e''
                  resFV = fv0 `mappend` HS.delete x fv
               in if F.null fv'
                     then return (resFV, ((x ::= resE e'):bs, rm, newLbs))
                     else freshId x >>= \n ->
                       let (replacement, e'') = exprs n
                        in insertWithReplace x replacement rm
                            >>= \rm' ->return (resFV, ((n ::= resE e''):bs, rm', (x ::= replacement):newLbs))

freeVars :: ExtendedLambda -> HS.HashSet Var
freeVars (Let ls e) = (foldr' mappend HS.empty $ freeVars e : map (freeVars . lbExpr) ls) `HS.difference` (HS.fromList $ map lbVar ls)
freeVars (a :~ b) = freeVars a `mappend` freeVars b
freeVars (a :@ b) = freeVars a `mappend` freeVars b
freeVars (Abs v e) = v `HS.delete` freeVars e
freeVars e@(V v) = HS.singleton v
freeVars e = HS.empty

freshId x = (('_' : x) ++ ) . show <$> (get <* modify (+1))

replaceAllFree :: HM.HashMap Var ExtendedLambda -> ExtendedLambda -> StateT Int (Except String) ExtendedLambda
replaceAllFree vs = impl vs
  where impl :: HM.HashMap Var ExtendedLambda -> ExtendedLambda -> StateT Int (Except String) ExtendedLambda
        impl vs (Let ls e) = Let <$> (sequence $ map implLb ls) <*> impl vs' e
          where implLb (x ::= e) = (::=) x <$> impl vs' e
                lbVars = map lbVar ls
                vs' = foldr' HM.delete vs lbVars
        impl vs (l :~ r) = (:~) <$> impl vs l <*> impl vs r
        impl vs (Abs v e) = if v `HS.member` fv
                               then freshId v >>= \v' -> Abs v' <$> impl (HM.insert v' (V v') vs) e
                               else Abs v <$> impl (v `HM.delete` vs) e
        impl vs (l :@ r) = (:@) <$> impl vs l <*> impl vs r
        impl vs e@(V v) = case HM.lookup v vs of
                          Just n -> return n
                          Nothing -> return e
        impl _ e = return e
        fv = foldr' (\e a -> a `mappend` freeVars e) HS.empty vs


insertWithReplace :: Var -> ExtendedLambda -> HM.HashMap Var ExtendedLambda -> StateT Int (Except String) (HM.HashMap Var ExtendedLambda)
insertWithReplace x e m = HM.insert x e <$> mapM (replaceAllFree (HM.singleton x e)) m

type NormMonad a = EitherT a (StateT Int (Except String)) a

toRight :: Functor n => EitherT b n b -> EitherT e' n b
toRight = mapEitherT (fmap $ either Right Right)

elIfTrue = Abs "x" $ Abs "y" $ V "x"
elIfFalse = Abs "x" $ Abs "y" $ V "y"

runNormMonad :: NormMonad a -> Either String a
runNormMonad = fmap (either id id) . runNormMonad'

runNormMonad' :: NormMonad a -> Either String (Either a a)
runNormMonad' = runExcept . flip evalStateT 0 . runEitherT

normalize1 :: ExtendedLambda -> Either String ExtendedLambda
normalize1 = runNormMonad . (normalize')

normalizeNp :: ExtendedLambda -> Either String ExtendedLambda
normalizeNp = runNormMonad . (steps)
  where steps = lift . normalizeRecursion >=> normalize' >=> steps
normalize :: ExtendedLambda -> Either String ExtendedLambda
normalize = runNormMonad . (toRight . steps >=> lift . propagateLets)
  where steps = lift . normalizeRecursion >=> normalize' >=> steps

propagateLets :: ExtendedLambda -> StateT Int (Except String) ExtendedLambda
propagateLets = impl HM.empty
  where impl :: HM.HashMap Var ExtendedLambda -> ExtendedLambda -> StateT Int (Except String) ExtendedLambda
        impl vs (Let ls e) = flip impl e =<< vs'
          where vs' = foldM (\vs' (a ::= b) -> flip (HM.insert a) vs' <$> impl vs' b) vs ls
        impl vs (l :~ r) = (:~) <$> impl vs l <*> impl vs r
        impl vs (Abs v e) = if v `HM.member` vs
                               then freshId v >>= \v' -> Abs v' <$> impl (HM.insert v' (V v') vs) e
                               else Abs v <$> impl (v `HM.delete` vs) e
        impl vs (l :@ r) = (:@) <$> impl vs l <*> impl vs r
        impl vs e@(V v) = case HM.lookup v vs of
                          Just n -> return n
                          Nothing -> return e
        impl _ e = return e

oneOf :: (Monad m) => (a -> a -> a) -> EitherT a m a -> EitherT a m a -> EitherT a m a
oneOf b l r = (l >>= \l' -> b l' <$> toRight r) `catchError` (\l' -> (b l' <$> r) `catchError` (left . b l'))

infixl 4 <?$>
(<?$>) :: Monad m => (a -> a) -> EitherT a m a -> EitherT a m a
(<?$>) f m = (f <$> m) `catchError` (left . f)

ordOp ord i j = compare i j == ord

normalize' :: ExtendedLambda -> NormMonad ExtendedLambda
normalize' = impl HM.empty
  where impl m (Let ls e) = Let ls <?$> impl m' e
          where m' = foldr' (\(v ::= s) -> HM.insert v s) m ls
        impl m (If :@ B b) = return $ if b then elIfTrue else elIfFalse
        impl m (If :@ p) = (If :@) <?$> impl m p
        impl m (IOp op :@ I i :@ I j) = return . I $ iop op i j
        impl m (IOp op :@ I i :@ p) = ((IOp op :@ I i :@) <?$> impl m p) >>= impl m
        impl m (IOp op :@ p) = ((IOp op :@) <?$> impl m p) >>= impl m
        impl m (OrdOp ord :@ I i :@ I j) = return . B $ ordOp ord i j
        impl m (OrdOp op :@ I i :@ p) = ((OrdOp op :@ I i :@) <?$> impl m p) >>= impl m
        impl m (OrdOp op :@ p) = ((OrdOp op :@) <?$> impl m p) >>= impl m
        impl m (Y :@ f) = return $ f :@ (Y :@ f)
        impl m (PrL :@ a :~ b) = toRight $ impl m a
        impl m (PrR :@ a :~ b) = toRight $ impl m b
        impl m (PrL :@ p) = ((PrL :@) <?$> impl m p) >>= impl m
        impl m (PrR :@ p) = ((PrR :@) <?$> impl m p) >>= impl m
        impl m (Case :@ (InL :@ x) :@ l :@ r) = return $ l :@ x
        impl m (Case :@ (InR :@ y) :@ l :@ r) = return $ r :@ y
        impl m (Case :@ p) = (Case :@) <?$> impl m p
        impl m o@(Abs v s :@ e) = lift $ replaceAllFree (HM.singleton v e) s
        impl m e@(l :@ r) = (impl m l >>= \l' -> toRight (impl m (l' :@ r)))
                            `catchError` (const $ left e)
        impl m e@(l :~ r) = oneOf (:~) (impl m l) (impl m r)
        impl m (V v) = case v `HM.lookup` m of
                          Just e -> return e
                          _ -> left (V v)
        impl _ e = left e




