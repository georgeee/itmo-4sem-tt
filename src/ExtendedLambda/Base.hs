{-# LANGUAGE PackageImports, FlexibleContexts #-}
module ExtendedLambda.Base (elParse, testElParse, testElParseSt, mergeContexts, mergeContexts'
                           , freshId, insertWithReplace, normalizeRecursion, freeVars, renameBound, replaceAllFree) where

import ExtendedLambda.Types

import Debug.Trace
import Data.List
import Common
import Data.Foldable as F
import Data.Maybe
import Control.Monad.State.Strict
import Text.Parsec hiding ((<|>), many, State, oneOf)
import Control.Applicative
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS
import qualified Data.LinkedHashMap.IntMap as LHM

infixl 4 <**
infixl 4 **>
x <** y = x <* spaces  <* y
x **> y = x *> spaces  *> y

parsecRunState m = getState >>= \s -> let (a, s') = runState m s
                                       in putState s' >> return a

elParse :: (Stream s m Char) => ParsecT s Int m ExtendedLambda
elParse = expr
  where expr = letE <|> (abs <|> appsAbs)
        abs = (\v e -> noContext $ Abs v e) <$> (char '\\' **> var')
                    <*> (spaces *> (string "." <|> string "->") **> expr)
        letE = do ls <- (try (string "let" *> space) **> (LHM.fromList <$> sepBy1 letBind (spaces *> char ',' *> spaces)) <* spaces)
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

freshId :: (Num s, Show s, MonadState s f) => f String
freshId = ("_x" ++ ) . show <$> (get <* modify (+1))

infixl 4 <.$>
infixl 4 <.*>

mergeContexts :: MonadState Int m => ELContext -> ELContext -> m ELContext
mergeContexts l1 l2 = LHM.fromList <$> modifyLs LHM.empty (reverse $ l1' ++ l2')
  where l1' = LHM.toList l1
        l2' = LHM.toList l2
        modifyLs _ [] = return []
        modifyLs vs ((v, e):as) = if v `LHM.member` vs
                                     then freshId >>= \v' -> modifyLs' v' $ LHM.insert v (noContext $ V v') vs
                                     else modifyLs' v $ LHM.insert v (noContext $ V v) vs
          where modifyLs' v' vs' = (:) . (,) v' <$> replaceAllFree vs' e <*> modifyLs vs' as

mergeContexts' l1 (l2 ::= e) = (::= e) <$> mergeContexts l1 l2

(<.$>) :: (Functor f, Functor g) => (a -> b) -> g (f a) -> g (f b)
f <.$> g = fmap f <$> g

(<.*>) :: (Applicative f, Monad m) => m (f (a -> b)) -> m (f a) -> m (f b)
mf <.*> mg = mf >>= \fab -> mg >>= \fa -> return $ fab <*> fa

insertWithReplace :: MonadState Int m => Var -> ExtendedLambda -> ELContext -> m ELContext
insertWithReplace x e m = LHM.insert x e <$> mapM (replaceAllFree (LHM.singleton x e)) m

normalizeRecursion :: MonadState Int m => ExtendedLambda -> m ExtendedLambda
normalizeRecursion e = snd <$> impl e
  where -- returns (expr with recursion replaced, set of free variables inside resulting expression)
        impl (ls ::= e) = (::=) <.$> replaceLB' <.*> impl' e
          where allLetVars = HM.fromList $ zip (LHM.keys ls) [1..]
                replaceLB' = (\(ls, _, ls') -> LHM.fromList $ reverse ls ++ ls')
                   <.$> foldM (replaceLB allLetVars) (HS.empty, ([], LHM.empty, [])) (zip [1..] $ LHM.toList ls)
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
                     else freshId >>= \n ->
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
          where i' = foldr HS.insert i $ LHM.keys ls


renameBound :: MonadState Int m => HS.HashSet Var -> ExtendedLambda -> m ExtendedLambda
renameBound fv = impl HM.empty
  where impl m (ls ::= e) = m' >>= \m'' -> (::=) <$> (LHM.fromList <$> mapM (implLB m'') (LHM.toList ls)) <*> impl' m'' e
          where implLB m'' (v, e) = (,) (maybe v id $ v `HM.lookup` m'') <$> impl m'' e
                m' = foldM (\m v -> freshId >>= \u -> return $ HM.insert v u m) m $ filter (flip HS.member fv) $ LHM.keys ls
        impl' m (l :~ r) = (:~) <$> impl m l <*> impl m r
        impl' m (l :@ r) = (:@) <$> impl m l <*> impl m r
        impl' m (Abs v e) = if v `HS.member` fv
                               then freshId >>= \u -> Abs u <$> impl (HM.insert v u m) e
                               else Abs v <$> impl m e
        impl' m (V v) = return $ V $ case v `HM.lookup` m of
                                 Just u -> u
                                 Nothing -> v
        impl' m e = return e

traceM' x y = y
--traceM' x y = y >>= \y' -> trace (x ++ " ==> " ++ (show y')) (return y')

replaceAllFree :: MonadState Int m => ELContext -> ExtendedLambda -> m ExtendedLambda
replaceAllFree vs e = impl =<< renameBound fv e
  where impl (ls ::= e) = traceM' "replaceFree: let" $ do e' <- impl' e
                                                          ls' <- traverse impl ls
                                                          mergeContexts' ls' e'
        impl' (l :~ r) = traceM' "replaceFree: pair" $ (\l' r' -> noContext $ l' :~ r') <$> impl l <*> impl r
        impl' (Abs v e) = traceM' "replaceFree: abs" $ (noContext . Abs v) <$> impl e
        impl' (l :@ r) = traceM' "replaceFree: app" $ (\l' r' -> noContext $ l' :@ r') <$> impl l <*> impl r
        impl' e@(V v) = traceM' ("replaceFree: V " ++ v) $ return $ case LHM.lookup v vs of
                          Just n -> n
                          Nothing -> noContext e
        impl' e = traceM' ("replaceFree: other " ++ (show e)) $ return $ noContext e
        fv = foldr' (flip mappend . freeVars) (HS.fromList $ LHM.keys vs) vs
