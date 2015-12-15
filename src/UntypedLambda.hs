{-# LANGUAGE PackageImports, FlexibleContexts #-}
module UntypedLambda where

import Data.Maybe
import Control.Monad.State.Strict
import Text.Parsec hiding ((<|>), many, State)
import Control.Applicative
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS

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
                     >> ULAbs <$> var <*> (spaces >> (string "." <|> string "->") >> spaces >> expr)
        app = foldl1 ULApp <$> many1 (atom <* spaces)
        atom = parens expr <|> ULVar <$> var
        parens e = char '(' *> expr <* spaces <* char ')'

testUlParse :: String -> UntypedLambda
testUlParse = either (error.show) id . parse ulParse ""

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

renameFree = impl
  where impl (ULVar v) rmap  = case v `HM.lookup` rmap of
                                Just n -> ULVar n
                                Nothing -> ULVar v
        impl (ULAbs v e) rmap = ULAbs v $ impl e (v `HM.delete` rmap)
        impl (ULApp l r) rmap = ULApp (impl l rmap) (impl r rmap)

renameBound fv = impl HM.empty 0
  where impl m _ (ULVar v) = case v `HM.lookup` m of
                                Just n -> ULVar n
                                Nothing -> ULVar v
        impl m i (ULAbs v e) = if v `HS.member` fv
                                  then ULAbs u $ impl (HM.insert v u m) (i + 1) e
                                  else ULAbs v $ impl m i e
                where u = 'x' : (show i)
        impl m i (ULApp l r) = ULApp (impl m i l) (impl m i r)

substFreeNoCheck v eInit s = impl eInit
  where impl e@(ULVar u) = if v == u
                            then s
                            else e
        impl e@(ULAbs u g) = if v == u
                              then e
                              else ULAbs u $ impl g
        impl (ULApp l r) = ULApp (impl l) (impl r)

normalize :: UntypedLambda -> UntypedLambda
normalize = implDeep'
  where
    impl (ULAbs v e) = ULAbs v <$> impl e
    impl e@(ULApp l r) = let l' = implDeep l
                             r' = implDeep r
                             l'' = extract l l'
                             r'' = extract r r'
                             e' = ULApp l'' r''
                             e'' = impl' l'' r''
                          in if isJust l' || isJust r'
                              then Just $ extract e' e''
                              else e''
    impl _ = Nothing
    impl' (ULAbs v e) s = Just $ substFreeNoCheck v (renameBound (freeVars s) e) s
    impl' _ _ = Nothing
    implDeep e = maybe Nothing (Just . implDeep') $ impl e
    implDeep' e = maybe e implDeep' $ impl e
    extract = flip maybe id
