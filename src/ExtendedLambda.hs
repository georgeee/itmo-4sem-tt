{-# LANGUAGE PackageImports, FlexibleContexts #-}
module ExtendedLambda where

import Data.List
import Common
import Data.Maybe
import Control.Monad.State.Strict
import Text.Parsec hiding ((<|>), many, State)
import Control.Applicative
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS

data IOp = Add | Subtract

infixl 1 ::=
data LetBinding = (::=) Var ExtendedLambda

infixl 1 :~
infixl 1 :@
data ExtendedLambda = Let [LetBinding] ExtendedLambda
                    | I Integer
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
    where p i s = (replicate (i*2) ' ') ++ s
          sps = flip replicate ' '
          show' :: Int -> ExtendedLambda -> String
          show' i (Let bs t) = let i' = i + 1 in
                      concat [ (sps $ i * 2) ++ "let " ++ (intercalate (",\n" ++ (sps $ i * 2 + 4)) $ map (showLB i') bs)
                             , (sps $ i' * 2) ++ "in " ++ (show' i' t)
                             ]
          show' _ (I x) = show x
          show' _ (B b) = if b then "T" else "F"
          show' _ Y = "Y"
          show' _ PrL = "PrL"
          show' _ PrR = "PrR"
          show' _ InL = "InL"
          show' _ InR = "InR"
          show' _ Case = "Case"
          show' _ If = "If"
          show' _ (IOp Add) = "Plus"
          show' _ (IOp Subtract) = "Minus"
          show' _ (OrdOp EQ) = "Eq"
          show' _ (OrdOp LT) = "Lt"
          show' _ (OrdOp GT) = "Gt"
          show' i (l :~ r) = let i' = i + 1 in "<" ++ (show' i' l) ++ ", " ++ (show' i' r) ++ ">"
          show' i (Abs v e) = let i' = i + 1 in "\\" ++ v ++ ". " ++ (show' i' e)
          show' i (l :@ r@(_ :@ _)) = let i' = i + 1 in (show' i' l) ++ " (" ++ (show' i' r) ++ ")"
          show' i (l :@ r) = let i' = i + 1 in (show' i' l) ++ " " ++ (show' i' r)
          show' _ (V v) = v

          showLB i (v ::= s) = v ++ " = " ++ (show' i s)

spaces1 :: Stream s m Char => ParsecT s u m ()
spaces1 = skipMany1 space

integer :: (Stream s m Char, Integral a, Read a) => ParsecT s u m a
integer = read <$> ((:) <$> (satisfy $ \p -> '1' <= p && p <= '9') <*> many digit)

infixl 4 <*!
infixl 4 <**
infixl 4 **>
infixl 4 !*>
x <*! y = x <* spaces1 <* y
x <** y = x <* spaces  <* y
x !*> y = x *> spaces1 *> y
x **> y = x *> spaces  *> y

elParse :: (Stream s m Char) => ParsecT s u m ExtendedLambda
elParse = expr
  where expr = letE <|> abs <|> (appsAbs <$> apps <*> ((Just <$> abs) <|> pure Nothing))
        abs = Abs <$> (char '\\' **> var')
                    <*> (spaces *> (string "." <|> string "->") **> expr)
        letE = Let <$> (string "let" !*> sepBy1 letBind (spaces *> char ',' *> spaces))
                    <*> (spaces *> string "in" **> expr)
        letBind = (::=) <$> var' <*> (spaces *> char '=' **> expr)
        apps = foldl1 (:@) <$> many1 (atom <* spaces)
        appsAbs e = maybe e (e :@)
        atom = parens' expr <|> (I <$> integer)
                           <|> (B <$> ((char 'T' *> pure True) <|> (char 'F' *> pure False)))
                           <|> (char 'Y' *> pure Y)
                           <|> (string "PrL" *> pure PrL)
                           <|> (string "PrR" *> pure PrR)
                           <|> (string "InL" *> pure InL)
                           <|> (string "InR" *> pure InR)
                           <|> (string "Case" *> pure Case)
                           <|> (string "If" *> pure If)
                           <|> (string "Plus" *> pure (IOp Add))
                           <|> (string "Minus" *> pure (IOp Subtract))
                           <|> (string "Eq" *> pure (OrdOp EQ))
                           <|> (string "Lt" *> pure (OrdOp LT))
                           <|> (string "Gt" *> pure (OrdOp GT))
                           <|> ((:~) <$> (char '<' **> expr) <*> (spaces *> char ',' **> expr <** char '>'))
                           <|> (V <$> var')
        var' = try $ checkNotKeyWord =<< var

checkNotKeyWord :: (Monad m) => Var -> m Var
checkNotKeyWord x = if x `elem` ["in", "let"]
                       then fail $ x ++ " is reserved as a keyword"
                       else return x

testElParse = testParser elParse
