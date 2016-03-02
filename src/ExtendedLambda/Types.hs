{-# LANGUAGE PackageImports, FlexibleContexts, MultiParamTypeClasses, FlexibleInstances #-}
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

instance Show (ExtendedLambdaBase ExtendedLambda) where
  show = showIdent 0 ()

instance Show ExtendedLambda where
  show = showIdent 0 ()

class Monoid u => IdentShow a u where
  showIdent :: Int -> u -> a -> String

instance (IdentShow c u, ELambdaContainer c) => IdentShow (ExtendedLambdaBase c) u where
  showIdent _ _ (I x) = show x
  showIdent _ _ (B b) = if b then "T" else "F"
  showIdent _ _ Y = "Y"
  showIdent _ _ PrL = "PrL"
  showIdent _ _ PrR = "PrR"
  showIdent _ _ InL = "InL"
  showIdent _ _ InR = "InR"
  showIdent _ _ Case = "Case"
  showIdent _ _ If = "If"
  showIdent _ _ (IOp Add) = "Plus"
  showIdent _ _ (IOp Subtract) = "Minus"
  showIdent _ _ (OrdOp EQ) = "Eq"
  showIdent _ _ (OrdOp LT) = "Lt"
  showIdent _ _ (OrdOp GT) = "Gt"
  showIdent i u (l :~ r) = let i' = i + 1 in "<" ++ (showIdent i' u l) ++ ", " ++ (showIdent i' u r) ++ ">"
  showIdent i u (Abs v e) = let i' = i + 1 in "(\\" ++ v ++ ". " ++ (showIdent i' u e) ++ ")"
  showIdent i u (l :@ r) = let i' = i + 1 in (showIdent i' u l) ++ " " ++ (show' i' u r)
    where show' i u r = case extractEl r of
                        (_ :@ _) -> "(" ++ (showIdent i u r) ++ ")"
                        _ -> showIdent i u r
  showIdent _ _ (V v) = v

instance IdentShow ExtendedLambda () where
  showIdent i u (bs ::= t) = if LHM.null bs then showIdent i u t else let i' = i + 1 in
              concat [ "\n" ++ (sps $ i * 2) ++ "(let " ++ (intercalate (",\n" ++ (sps $ i * 2 + 4)) $ showLBs i' u bs)
                     , "\n" ++ (sps $ i' * 2 - 1) ++ "in " ++ (showIdent i' u t) ++ ")"
                     ]
    where showLBs i u = map (\(v, s) -> v ++ " = " ++ (showIdent i u s)) . LHM.toList

p i s = (replicate (i*2) ' ') ++ s
sps = flip replicate ' '

