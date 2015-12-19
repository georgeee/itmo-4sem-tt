{-# LANGUAGE FlexibleContexts #-}
module Common where
import Text.Parsec hiding ((<|>), many, State)
import Control.Applicative
import Control.Monad.List

type Var = String

var :: (Stream s m Char) => ParsecT s u m Var
var = (:) <$> letter <*> many (alphaNum <|> char '\'')

parens' :: (Stream s m Char) => ParsecT s u m a -> ParsecT s u m a
parens' e = char '(' *> spaces *> e <* spaces <* char ')'

testParser :: Parsec String () a -> String -> a
testParser f = either (error . show) id . parse f ""

retList :: Monad m => [a] -> ListT m a
retList = ListT . return
