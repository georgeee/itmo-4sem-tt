{-# LANGUAGE PackageImports, FlexibleContexts #-}
module ExtendedLambda.Types (IOp(..), iop, ordOp, ELContext, noContext, ExtendedLambdaBase(..), ExtendedLambda(..), IdentShow(..), ELambdaContainer(..)) where

import Common
import Data.Maybe
import Data.List
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified Data.LinkedHashMap.IntMap as LHM

data IOp = Add | Subtract

ordOp ord i j = compare i j == ord

iop :: IOp -> Integer -> Integer -> Integer
iop Add = (+)
iop Subtract = (-)

infixl 4 :~
infixl 3 :@

type ELContext = LHM.LinkedHashMap Var ExtendedLambda

infixl 2 ::=
data ExtendedLambda = ELContext ::= ExtendedLambdaBase ExtendedLambda

noContext = (LHM.empty ::=)

data ExtendedLambdaBase container
     = I Integer
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
     | container :~ container --pair
     | container :@ container --application
     | Abs Var container
     | V Var

class ELambdaContainer e where
  extractEl :: e -> ExtendedLambdaBase e

instance ELambdaContainer ExtendedLambda where
  extractEl (_ ::= e) = e

instance Show ExtendedLambda where
  show = showIdent 0

class IdentShow a where
  showIdent :: Int -> a -> String

instance (IdentShow c, ELambdaContainer c) => Show (ExtendedLambdaBase c) where
  show = showIdent 0

instance (IdentShow c, ELambdaContainer c) => IdentShow (ExtendedLambdaBase c) where
  showIdent _ (I x) = show x
  showIdent _ (B b) = if b then "T" else "F"
  showIdent _ Y = "Y"
  showIdent _ PrL = "PrL"
  showIdent _ PrR = "PrR"
  showIdent _ InL = "InL"
  showIdent _ InR = "InR"
  showIdent _ Case = "Case"
  showIdent _ If = "If"
  showIdent _ (IOp Add) = "Plus"
  showIdent _ (IOp Subtract) = "Minus"
  showIdent _ (OrdOp EQ) = "Eq"
  showIdent _ (OrdOp LT) = "Lt"
  showIdent _ (OrdOp GT) = "Gt"
  showIdent i (l :~ r) = let i' = i + 1 in "<" ++ (showIdent i' l) ++ ", " ++ (showIdent i' r) ++ ">"
  showIdent i (Abs v e) = let i' = i + 1 in "(\\" ++ v ++ ". " ++ (showIdent i' e) ++ ")"
  showIdent i (l :@ r) = let i' = i + 1 in (showIdent i' l) ++ " " ++ (show' i' r)
    where show' i r = case extractEl r of
                        (_ :@ _) -> "(" ++ (showIdent i r) ++ ")"
                        _ -> showIdent i r
  showIdent _ (V v) = v

instance IdentShow ExtendedLambda where
  showIdent i (bs ::= t) = if LHM.null bs then showIdent i t else let i' = i + 1 in
              concat [ "\n" ++ (sps $ i * 2) ++ "(let " ++ (intercalate (",\n" ++ (sps $ i * 2 + 4)) $ showLBs i' bs)
                     , "\n" ++ (sps $ i' * 2 - 1) ++ "in " ++ (showIdent i' t) ++ ")"
                     ]
    where showLBs i = map (\(v, s) -> v ++ " = " ++ (showIdent i s)) . LHM.toList

p i s = (replicate (i*2) ' ') ++ s
sps = flip replicate ' '

