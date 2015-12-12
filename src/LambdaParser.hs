{-# LANGUAGE FlexibleContexts #-}
module LambdaParser where

import LambdaTypes
--import Text.ParserCombinators.Parsec hiding ((<|>))
import Text.Parsec hiding ((<|>), many)
import Control.Applicative

ulParse :: (Stream s m Char) => ParsecT s u m UntypedLambda
ulParse = spaces >> expr
  where expr = (app >>= \a -> (ULApp a <$> abs <|> pure a))
                    <|> abs <?> "expr"
        abs = char '\\' >> spaces
                     >> ULAbs <$> var <*> (spaces >> char '.' >> spaces >> expr)
        app = foldl1 ULApp <$> many1 (atom <* spaces)
        atom = parens expr <|> ULVar <$> var
        var = (:) <$> letter <*> many (alphaNum <|> char '\'')
        parens e = char '(' *> expr <* spaces <* char ')'
