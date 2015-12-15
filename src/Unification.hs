{-# LANGUAGE PackageImports, FlexibleContexts #-}
module Unification(Name, Equation(..), Term(..), eqsParse, eqParse, testEqsParse, unify, SolvedSystem) where

import Common
import Data.Either
import Data.List
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
testEqsParse = testParser eqsParser

--type UnState = State SolvedSystem
--performBasic :: [Equation] -> UnState [Equation]
--performBasic es = concat <$> mapM impl' es
--  where impl :: Term -> Term -> UnState [Equation]
--        -- Eliminate t = t
--        impl (Var x) (Var y) = return $ if x == y
--                                  then []
--                                  else [Var x := Var y]
--        -- x = t, x = s => x = t, t = s (where t isn't a variable)
--        -- first equation is to be taken from state
--        impl (Var x) s = gets (HM.lookup x) >>= impl'
--            where impl' (Just (Var _)) = return [Var x := s]
--                  impl' (Just t) = impl s t
--                  impl' _ = return [Var x := s]
--        -- t = x => x = t
--        impl t (Var x) = impl (Var x) t
--        impl x y = return [x := y]
--        impl' (x := y) = impl x y

--checkInconsistent


type SolvedSystem = HM.HashMap Name Term
type UnMonad a = StateT SolvedSystem (Either Equation) [a]

left' = lift . Left

-- Easy syntactic reductions and checking (deeping not more then two-three levels into term)
ac1 :: Equation -> UnMonad Equation
ac1 e@(Const c := Const d) = if c == d
                                 then return [e]
                                 else left' e
ac1 e@(Function _ _ := Const _) = left' e
ac1 e@(Const _ := Function _ _) = left' e
ac1 e@(Function f _ := Function g _) = if f == g
                                          then return [e]
                                          else left' e
ac1 (Var x := e@(Var y)) = if x == y
                              then return [] -- eliminate t = t
                              else ac1V x e
ac1 (Var x := e) = ac1V x e
acl (e := Var x) = ac1V x e

ac1V v s = gets (HM.lookup v) >>= impl -- v = s, where v is a var
  where impl Nothing = insertToMap v s >> return []
        impl (Just (Var _)) = return [Var v := s] --leave to ac2
        impl (Just t) = return [(t := s)] ~~> ac1

insertToMap :: Name -> Term -> UnMonad ()
insertToMap n t = get >>= \m -> let t' = substitute m t
                                    m' = HM.map (substitute $ HM.singleton n t') m
                                    m'' = HM.insert n t' m'
                                 in mapM_ (uncurry checker) (HM.toList m'')
                                      >> put m'' >> return []
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
                                      else return [eq]
ic1 e = return [e]

containsVar :: Name -> Term -> Bool
containsVar x (Var y) = x == y
containsVar _ (Const _) = False
containsVar x (Function _ as) = any (containsVar x) as

infixl 1 ~~>
(~~>) :: Monad m => m [a] -> (a -> m [b]) -> m [b]
ma ~~> f = ma >>= fmap concat . sequence . map f

(>~>) :: Monad m => (a -> m [b]) -> (b -> m [c]) -> a -> m [c]
(>~>) f g a = f a ~~> g

-- Reduction  "f(u1, u2, ..., uk) = f(v1, v2, ..., vk)" to set of equations "ui = vi"
ac2 :: Equation -> UnMonad Equation
ac2 e@(Function f as := Function g bs) = if f /= g || length as /= length bs
                                          then left' e
                                          else return (zipWith (:=) as bs) ~~> ic1 ~~> ac1
ac2 e = return [e]

-- Subtitution of all known vars into all equations
ac3 :: Equation -> UnMonad Equation
ac3 (r := s) = get >>= (\m -> return [substitute m r := substitute m s]) ~~> ic1 ~~> ac1

--unify' :: [Equation] -> Either Equation SolvedSystem
--unify' = run HM.empty . (NoEq :)
--chain = ac1 >=> ac2 >=> ac3
--exec st = runEitherT . flip runStateT st
--impl :: [Either Equation (Equation, SolvedSystem)] -> Either Equation SolvedSystem
--impl (s:[]) = snd <$> s
--impl l@(s:as) = impl' (lefts l) (rights l)
--impl' :: [Equation] -> [(Equation, SolvedSystem)] -> Either Equation SolvedSystem
--impl' (l:_) _ = Left l
--impl' _ rs@(r:_) = run (snd r) $ map fst rs
--run st = impl . exec st . (lift2 >=> chain)

unify' :: Equation -> UnMonad Equation
unify' = chain >=> unify''
  where chain = ac1 >~> ac2 >~> ac3
        unify'' [] = return []
        unify'' xs = return xs ~~> unify'

unify :: [Equation] -> Either Equation SolvedSystem
unify es = snd <$> runStateT (return es ~~> unify') HM.empty

--unify :: [Equation] -> Either Equation SolvedSystem
--unify es = snd <$> (head $ runEitherT $ runStateT (lift2 es >>= unify' >> lift2 [Var "x" := Var "y"]) HM.empty)
