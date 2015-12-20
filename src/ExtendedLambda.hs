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

infixl 3 :~
infixl 3 :@

type ELContext = HM.HashMap Var ExtendedLambda

infixl 2 ::=
data ExtendedLambda = ELContext ::= ExtendedLambdaBase

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

mergeContexts :: ELContext -> ELContext -> State Int ELContext
mergeContexts l1 l2 = HM.fromList <$> modifyLs HM.empty (l2' ++ l1')
  where l1' = HM.toList l1
        l2' = HM.toList l2
        modifyLs _ [] = return []
        modifyLs vs ((v, e):as) = if v `HM.member` vs
                                     then freshId v >>= \v' -> let vs' = HM.insert v (HM.empty ::= V v') vs
                                                                in (:) . (,) v' <$> repl vs' e <*> modifyLs vs' as
                                     else let vs' = HM.insert v (HM.empty ::= V v) vs
                                           in (:) . (,) v <$> repl vs' e <*> modifyLs vs' as
        repl = replaceAllFree

elParse :: (Stream s m Char) => ParsecT s Int m ExtendedLambda
elParse = expr
  where expr = letE <|> (abs <|> appsAbs)
        abs = (\v e -> HM.empty ::= Abs v e) <$> (char '\\' **> var')
                    <*> (spaces *> (string "." <|> string "->") **> expr)
        letE = do ls <- (try (string "let" *> space) **> (HM.fromList <$> sepBy1 letBind (spaces *> char ',' *> spaces)) <* spaces)
                  e <- (try (string "in" *> space) **> expr)
                  letE' ls e
        letE' ls (ls' ::= e) = (::= e) <$> mergeContexts' ls ls'
        mergeContexts' l1 l2 = getState >>= \s -> let (lm, s') = runState (mergeContexts l1 l2) s
                                                   in putState s' >> return lm
        letBind = (,) <$> var' <*> (spaces *> char '=' **> expr)
        apps = many1 (atom <* spaces)
        appsAbs = impl <$> apps <*> ((Just <$> abs) <|> pure Nothing)
          where impl :: [ExtendedLambda] -> Maybe ExtendedLambda -> ExtendedLambda
                impl es m = impl' $ maybe id (:) m es
                impl' (a:[]) = a
                impl' (a:as) = foldl (\b e -> HM.empty ::= b :@ e) a as
        atom = letE <|> parens' expr
             <|> ((HM.empty ::=) <$> ((I <$> integer)
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

freshId :: (Num s, Show s, MonadState s f) => String -> f String
freshId x = (('_' : x) ++ ) . show <$> (get <* modify (+1))

-- type NMonad a = StateT Int (Except String) (HS.HashSet Var, a)
-- type RLBPair = ([(Var, ExtendedLambda)], HM.HashMap Var ExtendedLambda, [(Var, ExtendedLambda)])
--
-- infixl 4 <.$>
-- infixl 4 <.*>
--
-- (<.$>) :: (Functor f, Functor g) => (a -> b) -> g (f a) -> g (f b)
-- f <.$> g = fmap f <$> g
--
-- (<.*>) :: (Applicative f, Monad m) => m (f (a -> b)) -> m (f a) -> m (f b)
-- mf <.*> mg = mf >>= \fab -> mg >>= \fa -> return $ fab <*> fa
--
-- normalizeRecursion :: ExtendedLambda -> StateT Int (Except String) ExtendedLambda
-- normalizeRecursion e = snd <$> impl e
--   where -- returns (expr with recursion replaced, set of free variables inside resulting expression)
--         impl :: ExtendedLambda -> NMonad ExtendedLambda
--         impl (ls ::= e) = (::=) <.$> replaceLB' <.*> impl' e
--           where allLetVars = HM.fromList $ zip (map fst ls) [1..]
--                 replaceLB' = (\(ls, _, ls') -> reverse ls ++ ls') <.$> foldM (replaceLB allLetVars) (HS.empty, ([], HM.empty, [])) (zip [1..] ls)
--         impl' (a :~ b) = (:~) <.$> impl' a <.*> impl' b
--         impl' (a :@ b) = (:@) <.$> impl' a <.*> impl' b
--         impl' (Abs v e) = impl' e >>= \(fv, e') -> return (HS.delete v fv, Abs v e')
--         impl' e@(V v) = return (HS.singleton v, e)
--         impl' e = return $ pure e
--
--
--         replaceLB :: HM.HashMap Var Int -> (HS.HashSet Var, RLBPair) -> (Int, (Var, ExtendedLambda)) -> NMonad RLBPair
--         replaceLB vs (fv0, (bs, rm, newLbs)) (i, (x, e))
--             = replaceAllFree rm e >>= impl >>= \(fv, e') ->
--               let needY = x `HS.member` fv
--                   -- fv' is a set of vars of same let, comming after current (if not empty, wee need to present new var x0)
--                   fv' = HM.keys $ HM.filterWithKey (\k i' -> HS.member k fv && i' > i) vs
--                   exprs n = (foldr' (flip (:@) . V) (V n) $ reverse fv', foldr' Abs e' fv')
--                   resE e'' = if needY then Y :@ Abs x e'' else e''
--                   resFV = fv0 `mappend` HS.delete x fv
--                in if F.null fv'
--                      then return (resFV, ((x ,resE e'):bs, rm, newLbs))
--                      else freshId x >>= \n ->
--                        let (replacement, e'') = exprs n
--                         in insertWithReplace x replacement rm
--                             >>= \rm' ->return (resFV, ((n ,resE e''):bs, rm', (x, replacement):newLbs))
--
freeVars :: ExtendedLambda -> HS.HashSet Var
freeVars el = execState (fvs' HS.empty el) HS.empty
  where fvs i (a :~ b) = fvs' i a >> fvs' i b
        fvs i (a :@ b) = fvs' i a >> fvs' i b
        fvs i (Abs v e) = fvs' (v `HS.insert` i) e
        fvs i (V v) = if v `HS.member` i then return () else modify (HS.insert v)
        fvs _ _ = return ()
        fvs' i (ls ::= e) = mapM_ (fvs' i') ls >> fvs i' e
          where i' = foldr HS.insert i $ HM.keys ls


renameBound :: HS.HashSet Var -> ExtendedLambda -> State Int ExtendedLambda
renameBound fv = impl HM.empty
  where impl :: HM.HashMap Var Var -> ExtendedLambda -> State Int ExtendedLambda
        impl m (ls ::= e) = m' >>= \m'' -> (::=) <$> (HM.fromList <$> mapM (implLB m'') (HM.toList ls)) <*> impl' m'' e
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

replaceAllFree :: HM.HashMap Var ExtendedLambda -> ExtendedLambda -> State Int ExtendedLambda
replaceAllFree vs e = impl =<< renameBound fv e
  where impl (ls ::= e) = trace' "replaceFree: let" $ impl' e >>= \(lsN ::= e') ->
                                                          (::= e') <$> (flip mergeContexts lsN =<< traverse impl ls)
        impl' (l :~ r) = trace' "replaceFree: pair" $ (\l' r' -> HM.empty ::= l' :~ r') <$> impl l <*> impl r
        impl' (Abs v e) = trace' "replaceFree: abs" $ ((HM.empty ::=) . Abs v) <$> impl e
        impl' (l :@ r) = trace' "replaceFree: app" $ (\l' r' -> HM.empty ::= l' :@ r') <$> impl l <*> impl r
        impl' e@(V v) = trace' ("replaceFree: V " ++ v) $ return $ case HM.lookup v vs of
                          Just n -> n
                          Nothing -> HM.empty ::= e
        impl' e = trace' ("replaceFree: other " ++ (show e)) $ return $ HM.empty ::= e
        fv = foldr' (\e a -> a `mappend` freeVars e) (HS.fromList $ HM.keys vs) vs

-- propagateLets :: ExtendedLambda -> StateT Int (Except String) ExtendedLambda
-- propagateLets = impl HM.empty
--   where impl :: HM.HashMap Var ExtendedLambda -> ExtendedLambda -> StateT Int (Except String) ExtendedLambda
--         impl vs (ls ::= e) = flip impl' e =<< vs'
--           where vs' = foldM (\vs' (a, b) -> flip (HM.insert a) vs' <$> impl' vs' b) vs ls
--         impl' vs (l :~ r) = (:~) <$> impl vs l <*> impl vs r
--         impl' vs (Abs v e) = if v `HM.member` vs
--                                then freshId v >>= \v' -> Abs v' <$> impl (HM.insert v (V v') vs) e
--                                else Abs v <$> impl (v `HM.delete` vs) e
--         impl' vs (l :@ r) = (:@) <$> impl vs l <*> impl vs r
--         impl' vs e@(V v) = case HM.lookup v vs of
--                           Just n -> return n
--                           Nothing -> return e
--         impl' _ e = return e
--
-- insertWithReplace :: Var -> ExtendedLambda -> HM.HashMap Var ExtendedLambda -> StateT Int (Except String) (HM.HashMap Var ExtendedLambda)
-- insertWithReplace x e m = HM.insert x e <$> mapM (replaceAllFree (HM.singleton x e)) m
--
-- type NormMonad a = EitherT a (StateT Int (Except String)) a
--
-- toRight :: Functor n => EitherT b n b -> EitherT e' n b
-- toRight = mapEitherT (fmap $ either Right Right)
--
-- runNormMonad :: NormMonad a -> Either String a
-- runNormMonad = fmap (either id id) . runNormMonad'
--
-- runNormMonad' :: NormMonad a -> Either String (Either a a)
-- runNormMonad' = runExcept . flip evalStateT 0 . runEitherT
--
-- normalize1 :: ExtendedLambda -> Either String ExtendedLambda
-- normalize1 = runNormMonad . (normalize')
--
-- normalizeNp :: ExtendedLambda -> Either String ExtendedLambda
-- normalizeNp = runNormMonad . (steps)
--   where steps = lift . normalizeRecursion >=> normalize' >=> steps
-- normalize :: ExtendedLambda -> Either String ExtendedLambda
-- normalize = runNormMonad . (toRight . steps >=> lift . propagateLets)
--   where steps = lift . normalizeRecursion >=> normalize' >=> steps
--
-- oneOf :: (Monad m) => (a -> a -> a) -> EitherT a m a -> EitherT a m a -> EitherT a m a
-- oneOf b l r = (l >>= \l' -> b l' <$> toRight r) `catchError` (\l' -> (b l' <$> r) `catchError` (left . b l'))
--
-- infixl 4 <?$>
-- (<?$>) :: Monad m => (a -> a) -> EitherT a m a -> EitherT a m a
-- (<?$>) f m = (f <$> m) `catchError` (left . f)
--
-- infixl 4 <?*>
-- (<?*>) :: Monad m => EitherT a m (a -> a) -> EitherT a m a -> EitherT a m a
-- (<?*>) f m = f >>= (<?$> m)
--
-- infixl 2 >>=+
-- (>>=+) :: NormMonad ExtendedLambda -> (ExtendedLambda -> NormMonad ExtendedLambda) -> NormMonad ExtendedLambda
-- ma >>=+ f = ma >>= \x -> toRight (if isWHNF x then f x else return x)
-- infixl 2 >>=!
-- (>>=!) :: NormMonad a -> (a -> NormMonad a) -> NormMonad a
-- ma >>=! f = ma >>= toRight . f
--
-- ordOp ord i j = compare i j == ord
--
-- isWHNF (_ ::= (_ :@ _)) = False
-- isWHNF _ = True
--
-- elIfTrue = [] ::= Abs "x" $ [] ::= Abs "y" $ V "x"
-- elIfFalse = [] ::= Abs "x" $ [] ::= Abs "y" $ V "y"
-- normalize' :: ExtendedLambda -> NormMonad ExtendedLambda
-- normalize' = impl HM.empty
--   where impl m l@(ls ::= e) = trace "let " $ (::=) <$> lift (ls' l m) <?*> impl' (m' l m) e
--         impl' m (If :@ B b) = trace "if1 " $ return $ if b then elIfTrue else elIfFalse
--         impl' m (If :@ p) = trace "if2 " $ (If :@) <?$> impl m p >>=+ impl m
--         impl' m (IOp op :@ I i :@ I j) = trace "iop1 " $ return . I $ iop op i j
--         impl' m (IOp op :@ I i :@ p) = trace "iop2 " $ ((IOp op :@ I i :@) <?$> impl m p) >>=+ impl m
--         impl' m (IOp op :@ p) = trace "iop3 " $ ((IOp op :@) <?$> impl m p) >>=+ impl m
--         impl' m (OrdOp op :@ I i :@ I j) = trace "ordOp1 " $ return . B $ ordOp op i j
--         impl' m (OrdOp op :@ I i :@ p) = trace "ordOp2 " $ ((OrdOp op :@ I i :@) <?$> impl m p) >>=+ impl m
--         impl' m (OrdOp op :@ p) = trace "ordOp3 " $ ((OrdOp op :@) <?$> impl m p) >>=+ impl m
--         impl' m (Y :@ f) = trace "Y " $ return (f :@ (Y :@ f)) >>=! impl m
--         impl' m (PrL :@ a :~ b) = trace "PrL1 " $ toRight $ impl m a
--         impl' m (PrR :@ a :~ b) = trace "PrR1 " $ toRight $ impl m b
--         impl' m (PrL :@ p) = trace "PrL2 " $ ((PrL :@) <?$> impl m p) >>=+ impl m
--         impl' m (PrR :@ p) = trace "PrR2 " $ ((PrR :@) <?$> impl m p) >>=+ impl m
--         impl' m (Case :@ (InL :@ x) :@ l :@ r) = trace "Case1 " $ return $ l :@ x
--         impl' m (Case :@ (InR :@ y) :@ l :@ r) = trace "Case2 " $ return $ r :@ y
--         impl' m (Case :@ p) = trace "Case3 " $ (Case :@) <?$> impl m p >>=+ impl m
--         impl' m o@(Abs v s :@ e) = trace "Abs " $ impl (HM.insert v e m) s
--         impl' m e@(l :@ r) = trace "App1 " $ ((:@ r) <?$> impl m l) >>=+ impl m
--         impl' m (V v) = trace "Var " $ case v `HM.lookup` m of
--                           Just e -> return e
--                           _ -> left (V v)
--         impl' _ e = trace ("Other: " ++ (show e)) $ left e
--         --trace = \x y -> y
--         m' (ls ::= _) m = foldr' (\v s -> HM.insert v s) m ls
--         ls' l@(ls ::= e) m = traverse (\(x, e) -> ((,) x) <$> replaceAllFree (m' l m) e) ls
--
--
--

