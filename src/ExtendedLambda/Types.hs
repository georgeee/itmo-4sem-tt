{-# LANGUAGE PackageImports, FlexibleContexts #-}
module ExtendedLambda.Types (IOp(..), iop, ordOp, ELContext, noContext, ExtendedLambdaBase(..), ExtendedLambda(..)) where

import Common
import Data.Maybe
import Data.List
import qualified "unordered-containers" Data.HashMap.Strict as HM

data IOp = Add | Subtract

ordOp ord i j = compare i j == ord

iop :: IOp -> Integer -> Integer -> Integer
iop Add = (+)
iop Subtract = (-)

infixl 4 :~
infixl 3 :@

type ELContext = HM.HashMap Var ExtendedLambda

infixl 2 ::=
data ExtendedLambda = ELContext ::= ExtendedLambdaBase

noContext = (HM.empty ::=)

data ExtendedLambdaBase = I Integer
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

instance Show ExtendedLambdaBase where
  show = show'' 0

p i s = (replicate (i*2) ' ') ++ s
sps = flip replicate ' '
show' :: Int -> ExtendedLambda -> String
show' i (bs ::= t) = if HM.null bs then show'' i t else let i' = i + 1 in
            concat [ "\n" ++ (sps $ i * 2) ++ "(let " ++ (intercalate (",\n" ++ (sps $ i * 2 + 4)) $ showLBs i' bs)
                   , "\n" ++ (sps $ i' * 2 - 1) ++ "in " ++ (show'' i' t) ++ ")"
                   ]
show'' _ (I x) = show x
show'' _ (B b) = if b then "T" else "F"
show'' _ Y = "Y"
show'' _ PrL = "PrL"
show'' _ PrR = "PrR"
show'' _ InL = "InL"
show'' _ InR = "InR"
show'' _ Case = "Case"
show'' _ If = "If"
show'' _ (IOp Add) = "Plus"
show'' _ (IOp Subtract) = "Minus"
show'' _ (OrdOp EQ) = "Eq"
show'' _ (OrdOp LT) = "Lt"
show'' _ (OrdOp GT) = "Gt"
show'' i (l :~ r) = let i' = i + 1 in "<" ++ (show' i' l) ++ ", " ++ (show' i' r) ++ ">"
show'' i (Abs v e) = let i' = i + 1 in "(\\" ++ v ++ ". " ++ (show' i' e) ++ ")"
show'' i (l :@ r) = let i' = i + 1 in (show' i' l) ++ " " ++ (show''' i' r)
show'' _ (V v) = v

show''' i r@(_ ::= _ :@ _) = "(" ++ (show' i r) ++ ")"
show''' i r = show' i r

showLBs i = map (\(v, s) -> v ++ " = " ++ (show' i s)) . HM.toList
