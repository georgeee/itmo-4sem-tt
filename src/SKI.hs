{-# LANGUAGE PackageImports, FlexibleContexts #-}
module SKI where

import Debug.Trace
import Data.Either(isRight)
import Data.Maybe (isJust)
import UntypedLambda
import Common
import qualified "unordered-containers" Data.HashSet as HS

infixl 1 :@
data SKI = V Var | S | K | I | SKI :@ SKI

instance Show SKI where
  show (V v) = ' ' : (v ++ " ")
  show S = "S"
  show K = "K"
  show I = "I"
  show (l :@ r@(_ :@ _)) = show l ++ "(" ++ (show r) ++ ")"
  show (l :@ r) = show l ++ (show r)

convertToLambda :: SKI -> UntypedLambda
convertToLambda (V v) = ULVar v
convertToLambda I = ULAbs "x" $ ULVar "x"
convertToLambda K = ULAbs "x" . ULAbs "y" $ ULVar "x"
convertToLambda S = ULAbs "x" . ULAbs "y" . ULAbs "z"
                  $ ULApp (ULApp (ULVar "x") (ULVar "z")) (ULApp (ULVar "y") (ULVar "z"))
convertToLambda (l :@ r) = ULApp (convertToLambda l) (convertToLambda r)

-- convertToSKI' :: UntypedLambda -> SKI
-- convertToSKI' = impl
--   where
--     impl (ULVar v) = V v
--     impl (ULApp l r) = impl l :@ impl r
--     impl (ULAbs x (ULVar y)) = if x ==y then I else K :@ V y
--     impl (ULAbs x p) = if x `HS.member` freeVars p
--                           then case p of
--                                 ULAbs y s -> S :@ (K :@ I) :@ (impl $ ULAbs y s)
--                                 (ULApp p q) -> S :@ (impl $ ULAbs x p) :@ (impl $ ULAbs x q)
--                           else K :@ (impl p)

testSKIUlParse :: String -> UntypedLambda
testSKIUlParse = testUlParse . (\s -> "(\\S.\\K.\\I. " ++ s ++ ") (\\x.\\y.\\z.x z (y z)) (\\x.\\y.x) (\\x.x)") . foldr insertSpaces ""
  where insertSpaces c = (++) [c, ' ']

convertToSKI :: UntypedLambda -> SKI
convertToSKI = impl
 where
  impl (ULVar v) = trace ("ULVar v : " ++ (show v)) $ V v
  impl (ULApp l r) = trace ("ULApp : " ++ (show (l,r,res))) $ res
      where res = impl l :@ impl r
  impl (ULAbs v e) = trace ("ULAbs : " ++ (show (v,e,e',lifted))) $ close e' lifted
    where e' = impl e
          lifted = liftUp v e'
  liftUp v (V u) = trace ("V v : " ++ (show (v, u))) $ if u == v then Just I else Nothing
  liftUp v (l :@ r) = let l' = liftUp v l
                          r' = liftUp v r
                       in trace ("l :@ r : " ++ (show (v, l, l', r, r'))) $ if isJust l' || isJust r'
                             then Just $ s (open l l') (open r r')
                             else Nothing
      where s (K :@ K) I = K
            s (K :@ I) K = K
            s (K :@ I) I = I
            s x y = S :@ x :@ y
  liftUp v e = trace ("other " ++ (show (v, e))) $ Nothing
  open e = maybe (K :@ e) id
  close e = maybe (K :@ e) s
    where --s I = I
          --s K = K
          s e = S :@ (K:@I) :@ e
          --s e = if leftIsS e
          --         then e
          --         else S :@ (K:@I) :@ e
          leftIsS (e :@ _) = leftIsS e
          leftIsS S = True
          leftIsS _ = False


prettify :: SKI -> SKI
prettify = implDeep'
  where impl (I :@ x) = Just $ implDeep' x
        impl (S :@ K :@ _) = Just $ I
        impl (S :@ y :@ (K :@ I) :@ x) = Just $ y' :@ x' :@ I
          where x' = implDeep' x
                y' = implDeep' y
        impl (S :@ y :@ I :@ x) = Just $ y' :@ x' :@ x'
          where x' = implDeep' x
                y' = implDeep' y
        impl (S :@ (K :@ (S :@ (K :@ I))) :@ x) = Just $ S :@ (K :@ x')
          where x' = implDeep' x
        impl (S :@ (K :@ I) :@ I) = Just I
        impl (S :@ (K :@ K) :@ I) = Just K
        impl (S :@ (K :@ I) :@ K) = Just K
        impl (S :@ (K :@ I) :@ e) = if leftIsS e
                                       then Just $ implDeep' e
                                       else Nothing
          where leftIsS (e :@ _) = leftIsS e
                leftIsS S = True
                leftIsS _ = False
        impl (K :@ x :@ _) = Just $ implDeep' x
        impl (l :@ r) = let l' = implDeep l
                            r' = implDeep r
                            e' = (extract l l' :@ extract r r')
                         in if isJust l' || isJust r'
                            then Just $ implDeep' e'
                            else Nothing
        impl _ = Nothing
        extract = flip maybe id
        implDeep e = maybe Nothing (Just . implDeep') $ impl e
        implDeep' e = maybe e implDeep' $ impl e
