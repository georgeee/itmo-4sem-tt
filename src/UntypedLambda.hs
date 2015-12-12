{-# LANGUAGE FlexibleContexts #-}
module UntypedLambda where

import Text.Parsec hiding ((<|>), many)
import Control.Applicative
import qualified Data.HashSet as HS

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
