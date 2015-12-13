{-# LANGUAGE FlexibleContexts #-}
module UntypedLambda where

import Control.Monad.State.Strict
import Text.Parsec hiding ((<|>), many, State)
import Control.Applicative
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM

type Var = String

data UntypedLambda = ULVar { ulVarName :: Var }
                   | ULAbs { ulVarName :: Var, ulExpr :: UntypedLambda }
                   | ULApp { ulLeft :: UntypedLambda, ulRight :: UntypedLambda }

data Substitution = Substitution { sExpr :: UntypedLambda
                                 , sVar :: Var
                                 , sSubst :: UntypedLambda
                                 }

instance Show UntypedLambda where
  show (ULVar name) = name
  show (ULAbs name e) = "(\\" ++ name ++ ". " ++ (show e) ++ ")"
  show (ULApp l r) = "(" ++ (show l) ++ " " ++ (show r) ++ ")"

ulParse :: (Stream s m Char) => ParsecT s u m UntypedLambda
ulParse = expr
  where expr = (app >>= \a -> (ULApp a <$> abs <|> pure a))
                    <|> abs <?> "expr"
        abs = char '\\' >> spaces
                     >> ULAbs <$> var <*> (spaces >> char '.' >> spaces >> expr)
        app = foldl1 ULApp <$> many1 (atom <* spaces)
        atom = parens expr <|> ULVar <$> var
        parens e = char '(' *> expr <* spaces <* char ')'

var :: (Stream s m Char) => ParsecT s u m Var
var = (:) <$> letter <*> many (alphaNum <|> char '\'')

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

renameFree s rmap = impl s
  where impl (ULVar v) = case v `HM.lookup` rmap of
                                Just n -> ULVar n
                                Nothing -> ULVar v
        impl (ULAbs v e) = case v `HM.lookup` rmap of
                                   Just n -> ULAbs v e
                                   Nothing -> ULAbs v $ impl e
        impl (ULApp l r) = ULApp (impl l) (impl r)

substFreeNoCheck v eInit s = impl eInit
  where impl e@(ULVar u) = if v == u
                            then s
                            else e
        impl e@(ULAbs u g) = if v == u
                              then e
                              else ULAbs u $ impl g
        impl (ULApp l r) = ULApp (impl l) (impl r)

normalize :: UntypedLambda -> UntypedLambda
normalize eInit = evalState (impl HS.empty eInit) 0
  where impl :: HS.HashSet Var -> UntypedLambda -> State Int UntypedLambda
        impl i e@(ULVar _) = pure e
        impl i (ULAbs v e) = ULAbs v <$> impl (HS.insert v i) e
        impl i (ULApp l r) = impl i l >>= \l' -> (impl i r >>= impl' l')
          where impl' :: UntypedLambda -> UntypedLambda -> State Int UntypedLambda
                impl' (ULAbs v e) s = let vs = collectAllAbsVars e `HS.intersection` freeVars s
                                          rmap = foldM (\m v -> HM.insert v <$> updState <*> pure m) HM.empty vs
                                       in substFreeNoCheck v e . renameFree s <$> rmap >>= impl i
                impl' l' r' = pure $ ULApp l' r'
                updState :: State Int Var
                updState = gets ((:) '_' . show) <* modify' (+1)

