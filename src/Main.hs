module Main where
import Text.Parsec
import System.Console.GetOpt
import UntypedLambda
import qualified Data.HashSet as HS
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

multiline opts algo = case optInput opts of
                   Just fname -> readFile fname
                          >>= mapM algo . splitBy (== '\n')
                          >>= mapM_ putStrLn
                   Nothing -> forever $ getLine >>= algo >>= putStrLn

main = do
  args <- getArgs
  let (actions, nonOptions, errors) = getOpt Permute options args
  opts <- foldl (>>=) (return defaultOptions) actions

  let perLine parser f = multiline opts $ return . either (("Error: " ++) . show) f . parse (spaces >> parser) ""

  case optTask opts of
    1 -> perLine ulParse show
    2 -> perLine ulParse $ show . sort . HS.toList . freeVars
    3 -> perLine sParse $ either (++ " isn't free for substitution") show . performSubst
    4 -> perLine ulParse $ show . normalize
