{-# LANGUAGE PackageImports #-}
module Main where
import Text.Parsec
import Control.Monad.State.Strict
import Control.Monad.Trans.Either
import ExtendedLambda.Base
import ExtendedLambda.AlgorithmW as EL
import System.Console.GetOpt
import UntypedLambda as UL
import qualified "unordered-containers" Data.HashMap.Strict as HM
import qualified "unordered-containers" Data.HashSet as HS
import Unification
import SimpleTypedLambda as STL
import SKI
import Data.List
import Control.Monad
import Data.List
import System.Environment
import System.IO

data Options = Options { optInput :: Maybe FilePath
                       , optTask :: Int
                       }

defaultOptions = Options { optInput = Nothing
                         , optTask = 0
                         }


options :: [ OptDescr (Options -> IO Options) ]
options = [ Option "i" ["input"] (ReqArg (\f os -> return $ os { optInput = Just f }) "FILE") "Input file"
          , Option "t" ["task"] (ReqArg (\f os -> return $ os { optTask = read f }) "INT") "Task id"
          ]

splitBy _ [] = []
splitBy p xs = impl . span (not . p) $ xs
  where impl ([], _) = []
        impl (l, rest) = l : splitBy p (dropWhile p rest)

type BasicRW = Options -> ([Char] -> IO String) -> IO ()

multilineReader :: BasicRW
multilineReader opts algo = case optInput opts of
                   Just fname -> readFile fname
                          >>= mapM algo . splitBy (== '\n')
                          >>= mapM_ putStrLn
                   Nothing -> forever $ getLine >>= algo >>= putStrLn

fullReader :: BasicRW
fullReader opts algo = case optInput opts of
                         Just fname -> readFile fname >>= algo >>= putStrLn
                         Nothing -> getContents >>= algo >>= putStrLn

basicRunner :: BasicRW -> Options -> (Parsec String () b) -> (b -> String) -> IO ()
basicRunner rw opts parser f = rw opts $ return . either (("Error: " ++) . show) f . parse (spaces >> parser) ""

perLine = basicRunner multilineReader
full = basicRunner fullReader

main = do
  args <- getArgs
  let (actions, nonOptions, errors) = getOpt Permute options args
  opts <- foldl (>>=) (return defaultOptions) actions

  case optTask opts of
    1 -> perLine opts ulParse showUlWithParens
    2 -> perLine opts ulParse $ show . sort . HS.toList . UL.freeVars
    3 -> perLine opts sParse $ either (++ " isn't free for substitution") show . performSubst
    4 -> perLine opts ulParse $ show . normalize
    -1 -> perLine opts ulParse $ show . prettify . convertToSKI
    5 -> perLine opts ulParse $ show . convertToSKI
    6 -> full opts eqsParse $ showUnifyResult . unify
    7 -> perLine opts ulParse $ showSTResult . STL.findType
    13 -> fullReader opts $ \s -> return $ either ("Error " ++) id $ (\(t,e) -> show t ++ "\n" ++ show e) <$> evalState (runEitherT $ testElParseSt s >>= normalizeRecursion >>= EL.findType) 0

showSTResult (Left e) = "Lamda has no type, failed on equation " ++ (show e)
showSTResult (Right (l, t, m)) = (show l) ++ " :: " ++ (show t) ++ "\nContext:\n" ++ (showMap " :: " m)

showUnifyResult (Left e) = "System is inconsistent, stopped on equation: " ++ (show e)
showUnifyResult (Right m) = showMap " = " m

showMap del = intercalate "\n" . map (\(x, t) -> x ++ del ++ (show t)) . HM.toList
