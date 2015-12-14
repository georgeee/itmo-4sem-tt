{-# LANGUAGE PackageImports, FlexibleContexts #-}
module Unification where

import Data.List
import Text.Parsec hiding ((<|>), many, State)
import Control.Applicative hiding (Const)

data Equation = Equation Term Term
type Name = String
data Term = Var Name | Function Name [Term] | Const Name

instance Show Equation where
  show (Equation l r) = (show l) ++ " = " ++ (show r)

instance Show Term where
  show (Var n) = n
  show (Const n) = n
  show (Function n ts) = n ++ "(" ++ (intercalate ", " $ map show ts) ++ ")"

eqsParse :: (Stream s m Char) => ParsecT s u m [Equation]
eqsParse = sepBy eqParse spaces

eqParse :: (Stream s m Char) => ParsecT s u m Equation
eqParse = eq
  where eq = Equation <$> term <*> (spaces *> char '=' *> spaces *> term)
        termList = sepBy1 term (spaces *> char ',' <* spaces)
        term = (Const <$> cName) <|> (vName >>= \n -> spaces *> ((Function n <$> parens termList) <|> (pure $ Var n)))
        parens e = char '(' *> e <* spaces <* char ')'
        vName = (:) <$> lower <*> many (alphaNum <|> char '\'')
        cName = (:) <$> upper <*> many (alphaNum <|> char '\'')

testEqsParse :: String -> [Equation]
testEqsParse = either (error.show) id . parse eqsParse ""
