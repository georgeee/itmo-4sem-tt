{-# LANGUAGE PackageImports, FlexibleContexts #-}
module Unification(Name, Equation(..), Term(..), eqsParse, eqParse, testEqsParse, unify, SolvedSystem) where

import Common
import Data.Either
import Data.List
import Control.Monad.List
import Control.Monad.State.Strict
import Text.Parsec hiding ((<|>), many, State)
import Control.Applicative hiding (Const)
import qualified "unordered-containers" Data.HashMap.Strict as HM

infixl 1 :=
data Equation = (:=) Term Term
type Name = String
data Term = Var Name | Function Name [Term] | Const Name

isVar (Var _) = True
isVar _ = False

instance Show Equation where
  show (l := r) = (show l) ++ " = " ++ (show r)

instance Show Term where
  show (Var n) = n
  show (Const n) = n
  show (Function n ts) = n ++ "(" ++ (intercalate ", " $ map show ts) ++ ")"

eqsParse :: (Stream s m Char) => ParsecT s u m [Equation]
eqsParse = sepBy eqParse spaces

eqParse :: (Stream s m Char) => ParsecT s u m Equation
eqParse = eq
  where eq = (:=) <$> term <*> (spaces *> char '=' *> spaces *> term)
        termList = sepBy1 term (spaces *> char ',' <* spaces)
        term = (Const <$> cName) <|> (vName >>= \n -> spaces *> ((Function n <$> parens' termList) <|> (pure $ Var n)))
        vName = (:) <$> lower <*> many (alphaNum <|> char '\'')
        cName = (:) <$> upper <*> many (alphaNum <|> char '\'')

testEqsParse :: String -> [Equation]
testEqsParse = testParser eqsParse ()

type SolvedSystem = HM.HashMap Name Term
type UnMonad = ListT (StateT SolvedSystem (Either Equation))

left' = lift . lift . Left

-- Easy syntactic reductions and checking (deeping not more then two-three levels into term)
ac1 :: Equation -> UnMonad Equation
ac1 e@(Const c := Const d) = if c == d
                                 then pure e
                                 else left' e
ac1 e@(Function _ _ := Const _) = left' e
ac1 e@(Const _ := Function _ _) = left' e
ac1 e@(Function f _ := Function g _) = if f == g
                                          then pure e
                                          else left' e
ac1 (Var x := e@(Var y)) = if x == y
                              then retList [] -- eliminate t = t
                              else ac1V x e
ac1 (Var x := e) = ac1V x e
acl (e := Var x) = ac1V x e

ac1V v s = gets (HM.lookup v) >>= impl -- v = s, where v is a var
  where impl Nothing = insertToMap v s >> retList []
        impl (Just (Var _)) = pure $ Var v := s --leave to ac2
        impl (Just t) = pure (t := s) >>= ac1

insertToMap :: Name -> Term -> UnMonad ()
insertToMap n t = get >>= \m -> let t' = substitute m t
                                    m' = HM.map (substitute $ HM.singleton n t') m
                                    m'' = HM.insert n t' m'
                                 in mapM_ (uncurry checker) (HM.toList m'')
                                      >> put m'' >> retList []
  where checker x e = if containsVar x e
                         then left' $ Var x := e
                         else return ()

substitute vars (Var n) = case n `HM.lookup` vars of
                            Just s -> s
                            _ -> Var n
substitute vars (Function n as) = Function n $ map (substitute vars) as
substitute vars (Const n) = Const n

-- Inconsistency check #1 : check case x = f (..., g(x) , ...) (x -variable from left part is a subterm of right part)
ic1 :: Equation -> UnMonad Equation
ic1 (Function f as := Var x) = ic1 $ Var x := Function f as
ic1 eq@(Var x := e@(Function f as)) = if containsVar x e
                                      then left' eq
                                      else return eq
ic1 e = return e

containsVar :: Name -> Term -> Bool
containsVar x (Var y) = x == y
containsVar _ (Const _) = False
containsVar x (Function _ as) = any (containsVar x) as

-- Reduction  "f(u1, u2, ..., uk) = f(v1, v2, ..., vk)" to set of equations "ui = vi"
ac2 :: Equation -> UnMonad Equation
ac2 e@(Function f as := Function g bs) = if f /= g || length as /= length bs
                                          then left' e
                                          else retList (zipWith (:=) as bs) >>= ic1 >>= ac1
ac2 e = return e

-- Subtitution of all known vars into all equations
ac3 :: Equation -> UnMonad Equation
ac3 (r := s) = get >>= (\m -> return $ substitute m r := substitute m s) >>= ic1 >>= ac1

unify' :: Equation -> UnMonad Equation
unify' = ac1 >=> ac2 >=> ac3 >=> unify'

unify :: [Equation] -> Either Equation SolvedSystem
unify es = snd <$> runStateT (runListT $ retList es >>= unify') HM.empty
