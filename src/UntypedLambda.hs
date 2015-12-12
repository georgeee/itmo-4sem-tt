module UntypedLambda where

type Var = String

data UntypedLambda = ULVar { ulVarName :: Var }
                   | ULAbs { ulVarName :: Var, ulExpr :: UntypedLambda }
                   | ULApp { ulLeft :: UntypedLambda, ulRight :: UntypedLambda }


instance Show UntypedLambda where
  show (ULVar name) = name
  show (ULAbs name e) = "(\\" ++ name ++ ". " ++ (show e) ++ ")"
  show (ULApp l r) = "(" ++ (show l) ++ " " ++ (show r) ++ ")"
