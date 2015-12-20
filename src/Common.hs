{-# LANGUAGE FlexibleContexts #-}
module Common where
import Text.Parsec hiding ((<|>), many, State)
import Control.Applicative
import Control.Monad.List
import Control.Monad.State.Class

type Var = String

var :: (Stream s m Char) => ParsecT s u m Var
var = (:) <$> letter <*> many (alphaNum <|> char '\'')

parens' :: (Stream s m Char) => ParsecT s u m a -> ParsecT s u m a
parens' e = char '(' *> spaces *> e <* spaces <* char ')'

testParser :: Parsec String u a -> u -> String -> a
testParser p u = either (error . show) id . runParser p u ""

testParser' :: Parsec String u a -> u -> String -> (a, u)
testParser' p u = either (error . show) id . runParser p' u ""
  where p' = (,) <$> p <*> getState

testParserSt :: MonadState u m => Parsec String u a -> String -> m a
testParserSt p str = get >>= \s -> let (a, s') = testParser' p s str
                                    in put s' >> return a

retList :: Monad m => [a] -> ListT m a
retList = ListT . return
