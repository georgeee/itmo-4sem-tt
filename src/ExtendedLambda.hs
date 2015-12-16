{-# LANGUAGE PackageImports, FlexibleContexts #-}
module ExtendedLambda where

import Data.List
import Common
import Data.Foldable as F
import Data.Maybe
import Control.Monad.Except
import Control.Monad.State.Strict
import Text.Parsec hiding ((<|>), many, State)
import Control.Applicative
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS

data IOp = Add | Subtract

infixl 1 ::=
data LetBinding = (::=) Var ExtendedLambda

infixl 2 :~
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
          show' i (l :@ r@(_ :@ _)) = let i' = i + 1 in (show' i' l) ++ " (" ++ (show' i' r) ++ ")"
          show' i (l :@ r) = let i' = i + 1 in (show' i' l) ++ " " ++ (show' i' r)
          show' _ (V v) = v

          showLB i (v ::= s) = v ++ " = " ++ (show' i s)

spaces1 :: Stream s m Char => ParsecT s u m ()
spaces1 = skipMany1 space

integer :: (Stream s m Char, Integral a, Read a) => ParsecT s u m a
integer = read <$> ((:) <$> (satisfy $ \p -> '1' <= p && p <= '9') <*> many digit)

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
        letE = Let <$> (string "let" !*> sepBy1 letBind (spaces *> char ',' *> spaces))
                    <*> (spaces *> string "in" **> expr)
        letBind = (::=) <$> var' <*> (spaces *> char '=' **> expr)
        apps = foldl1 (:@) <$> many1 (atom <* spaces)
        appsAbs e = maybe e (e :@)
        atom = parens' expr <|> (I <$> integer)
                           <|> (B <$> ((char 'T' *> pure True) <|> (char 'F' *> pure False)))
                           <|> (char 'Y' *> pure Y)
                           <|> (string "PrL" *> pure PrL)
                           <|> (string "PrR" *> pure PrR)
                           <|> (string "InL" *> pure InL)
                           <|> (string "InR" *> pure InR)
                           <|> (string "Case" *> pure Case)
                           <|> (string "If" *> pure If)
                           <|> (string "Plus" *> pure (IOp Add))
                           <|> (string "Minus" *> pure (IOp Subtract))
                           <|> (string "Eq" *> pure (OrdOp EQ))
                           <|> (string "Lt" *> pure (OrdOp LT))
                           <|> (string "Gt" *> pure (OrdOp GT))
                           <|> ((:~) <$> (char '<' **> expr) <*> (spaces *> char ',' **> expr <** char '>'))
                           <|> (V <$> var')
        var' = try $ checkNotKeyWord =<< var

checkNotKeyWord :: (Monad m) => Var -> m Var
checkNotKeyWord x = if x `elem` ["in", "let"]
                       then fail $ x ++ " is reserved as a keyword"
                       else return x

testElParse = testParser elParse

--toRight = lift . either pure pure
--left' = left . Left

type NormalizationStep = ExtendedLambda -> ExceptT String (Either ExtendedLambda) ExtendedLambda
type NMonad a = State Int (HS.HashSet Var, a)
type RLBPair = ([LetBinding], HM.HashMap Var ExtendedLambda, [LetBinding])

lbVar (v ::= _) = v

infixl 4 <.$>
infixl 4 <.*>

(<.$>) :: (Functor f, Functor g) => (a -> b) -> g (f a) -> g (f b)
f <.$> g = fmap f <$> g

(<.*>) :: (Applicative f, Monad m) => m (f (a -> b)) -> m (f a) -> m (f b)
mf <.*> mg = mf >>= \fab -> mg >>= \fa -> return $ fab <*> fa

normalizeRecursion :: ExtendedLambda -> ExtendedLambda
normalizeRecursion = snd . flip evalState 0 . impl
  where -- returns (expr with recursion replaced, set of free variables inside resulting expression)
        impl :: ExtendedLambda -> NMonad ExtendedLambda
        impl (Let ls e) = Let <.$> replaceLB' <.*> impl e
          where allLetVars = HM.fromList $ zip (map lbVar ls) [1..]
                replaceLB' = (\(ls, _, ls') -> reverse ls ++ ls') <.$> foldM (replaceLB allLetVars) (HS.empty, ([], HM.empty, [])) (zip [1..] ls)
        impl (a :~ b) = (:~) <.$> impl a <.*> impl b
        impl (a :@ b) = (:@) <.$> impl a <.*> impl b
        impl e@(V v) = return (HS.singleton v, e)
        impl e = return $ pure e

        freshId x = (('_' : x) ++ ) . show <$> (get <* modify (+1))

        replaceLB :: HM.HashMap Var Int -> (HS.HashSet Var, RLBPair) -> (Int, LetBinding) -> NMonad RLBPair
        replaceLB vs (fv0, (bs, rm, newLbs)) (i, x ::= e)
            = impl (replaceAllFree rm e) >>= \(fv, e') ->
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
                        in return (resFV, ((n ::= resE e''):bs, insertWithReplace x replacement rm, (x ::= replacement):newLbs))

replaceAllFree :: HM.HashMap Var ExtendedLambda -> ExtendedLambda -> ExtendedLambda
replaceAllFree = impl
  where impl vs (Let ls e) = Let (map implLb ls) $ impl vs' e
          where implLb (x ::= e) = x ::= impl vs' e
                lbVars = map lbVar ls
                vs' = foldr' HM.delete vs lbVars
        impl vs (l :~ r) = impl vs l :~ impl vs r
        impl vs (Abs v e) = Abs v $ impl (v `HM.delete` vs) e
        impl vs (l :@ r) = impl vs l :@ impl vs r
        impl vs (V v) = case HM.lookup v vs of
                          Just n -> n
                          Nothing -> V v
        impl _ e = e

insertWithReplace x e = HM.insert x e . HM.map (replaceAllFree (HM.singleton x e))
