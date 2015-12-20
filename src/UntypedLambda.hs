{-# LANGUAGE PackageImports, FlexibleContexts #-}
module UntypedLambda where

import qualified Debug.Trace as DT
import Common
import Data.Char
import Data.Maybe
import Control.Monad.State.Strict
import Text.Parsec hiding ((<|>), many, State)
import Control.Applicative
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS

data UntypedLambda = ULVar { ulVarName :: Var }
                   | ULAbs { ulVarName :: Var, ulExpr :: UntypedLambda }
                   | ULApp { ulLeft :: UntypedLambda, ulRight :: UntypedLambda }

data Substitution = Substitution { sExpr :: UntypedLambda
                                 , sVar :: Var
                                 , sSubst :: UntypedLambda
                                 }

instance Show UntypedLambda where
  show = show'
    where show' (ULVar name) = name
          show' (ULAbs v e) = "(\\" ++ v ++ ". " ++ (show' e) ++ ")"
          show' (ULApp l r) = (show' l) ++ " " ++ (show'' r)

          show'' r@(ULApp _ _) = "(" ++ (show' r) ++ ")"
          show'' r = show' r

showUlWithParens (ULVar name) = name
showUlWithParens (ULAbs name e) = "(\\" ++ name ++ " -> " ++ (showUlWithParens e) ++ ")"
showUlWithParens (ULApp l r) = "(" ++ (showUlWithParens l) ++ " " ++ (showUlWithParens r) ++ ")"
ulParse :: (Stream s m Char) => ParsecT s u m UntypedLambda
ulParse = expr
  where expr = (app >>= \a -> (ULApp a <$> abs <|> pure a))
                    <|> abs <?> "expr"
        abs = char '\\' >> spaces
                     >> ULAbs <$> var <*> (spaces >> (string "." <|> string "->") >> spaces >> expr)
        app = foldl1 ULApp <$> many1 (atom <* spaces)
        atom = parens' expr <|> ULVar <$> var

testUlParse = testParser ulParse

sParse :: (Stream s m Char) => ParsecT s u m Substitution
sParse = Substitution <$> ulParse
                      <*> (spaces >> char '[' >> spaces >> var)
                      <*> (spaces >> string ":=" >> spaces >> ulParse)
                      <* spaces <* char ']'

freeVars :: UntypedLambda -> HS.HashSet Var
freeVars = impl HS.empty HS.empty
  where impl i s (ULVar v) = if v `HS.member` i
                                then s
                                else HS.insert v s
        impl i s (ULAbs v e) = impl (HS.insert v i) s e
        impl i s (ULApp l r) = impl i (impl i s l) r

performSubst :: Substitution -> Either Var UntypedLambda
performSubst subst = impl HS.empty $ sExpr subst
  where fv = freeVars $ sSubst subst
        impl i e@(ULVar v) = if (v == sVar subst) && (not $ v `HS.member` i)
                                then let is = HS.intersection fv i
                                      in if not . HS.null $ is
                                            then Left . head . HS.toList $ is
                                            else Right $ sSubst subst
                                else Right e
        impl i (ULAbs v e) = ULAbs v <$> impl (HS.insert v i) e
        impl i (ULApp l r) = ULApp <$> impl i l <*> impl i r

collectAllAbsVars :: UntypedLambda -> HS.HashSet Var
collectAllAbsVars = impl
  where impl e@(ULVar v) = HS.empty
        impl (ULAbs v e) = v `HS.insert` impl e
        impl (ULApp l r) = impl l `HS.union` impl r

renameFree = impl
  where impl (ULVar v) rmap  = case v `HM.lookup` rmap of
                                Just n -> ULVar n
                                Nothing -> ULVar v
        impl (ULAbs v e) rmap = ULAbs v $ impl e (v `HM.delete` rmap)
        impl (ULApp l r) rmap = ULApp (impl l rmap) (impl r rmap)

renameBound :: HS.HashSet Var -> UntypedLambda -> State Int UntypedLambda
renameBound fv e = trace' ("renameBound " ++ show (e, fv)) $ impl HM.empty e
  where impl m (ULVar v) = return $ impl' (HM.lookup v m)
          where impl' (Just n) = ULVar n
                impl' _ = ULVar v
        impl m (ULAbs v e) = if v `HS.member` fv
                              then upd v >>= \u -> ULAbs u <$> impl (HM.insert v u m) e
                              else ULAbs v <$> impl m e
        impl m (ULApp l r) = ULApp <$> (impl m l) <*> (impl m r)
        upd v = get >>= \i -> let u = 'x' : (show i) in put (i + 1) >> return u

--renameBound fv = impl HM.empty 0
--  where impl m _ (ULVar v) = case v `HM.lookup` m of
--                                Just n -> ULVar n
--                                Nothing -> ULVar v
--        impl m i (ULAbs v e) = if v `HS.member` fv
--                                  then ULAbs u $ impl (HM.insert v u m) (i + 1) e
--                                  else ULAbs v $ impl m i e
--                where u = 'x' : (show i)
--        impl m i (ULApp l r) = ULApp (impl m i l) (impl m i r)
--

--substFreeNoCheck :: var -> s -> t -> t [v := s]
substFreeNoCheck :: Var -> UntypedLambda -> UntypedLambda -> UntypedLambda
substFreeNoCheck v s eInit = impl eInit
  where impl e@(ULVar u) = if v == u
                            then s
                            else e
        impl e@(ULAbs u g) = if v == u
                              then e
                              else ULAbs u $ impl g
        impl (ULApp l r) = ULApp (impl l) (impl r)

trace' = \x y -> y
--trace' x y = y >>= \y' -> DT.trace (x ++ " ==> " ++ (show y')) (return y')

findAllVars :: UntypedLambda -> HS.HashSet Var
findAllVars e = execState (find e) HS.empty
  where find (ULVar u) = modify (HS.insert u)
        find (ULAbs u g) = modify (HS.insert u) >> find g
        find (ULApp l r) = find l >> find r

normalize :: UntypedLambda -> UntypedLambda
normalize e = evalState (normalize' e) maxI
  where maxI = (+1) . maximum . (:) 0 . map (read . tail) . filter pred . HS.toList $ findAllVars e
        pred (_:[]) = False
        pred ('x':xs) = all isAlphaNum xs
        pred _ = False

normalize' :: UntypedLambda -> State Int UntypedLambda
normalize' e = trace' ("normalize' " ++ (show e)) $ maybe (rightRedux e) rightRedux =<< whnf e

rightRedux :: UntypedLambda -> State Int UntypedLambda
rightRedux e@(ULAbs v s) = trace' ("rightRedux " ++ (show e)) $ ULAbs v <$> normalize' s
rightRedux e@(ULApp l r) = trace' ("rightRedux " ++ (show e)) $ ULApp <$> rightRedux l <*> normalize' r
rightRedux v = trace' ("rightRedux " ++ (show v)) $ return v

whnf :: UntypedLambda -> State Int (Maybe UntypedLambda)
whnf e@(ULVar _) = trace' ("whnf " ++ (show e)) $ return Nothing
whnf e@(ULAbs _ _) = trace' ("whnf " ++ (show e)) $ return Nothing
whnf e@(ULApp (ULAbs v t) s) = trace' ("whnf " ++ (show e)) $ t' >>= \t'' -> maybe (Just t'') Just <$> whnf t''
  where t' = substFreeNoCheck v s <$> renameBound (freeVars s) t
whnf e@(ULApp l r) = trace' ("whnf " ++ (show e)) $ whnf'' =<< whnf l
  where whnf'' Nothing = return Nothing
        whnf'' (Just l') = maybe (Just $ ULApp l' r) Just <$> whnf (ULApp l' r)
