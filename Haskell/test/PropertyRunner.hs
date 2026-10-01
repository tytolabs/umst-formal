-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Runs QuickCheck properties so that a falsified property, or one that gives up on its
-- preconditions, fails the test executable. Plain 'quickCheck' only prints its verdict.
module PropertyRunner
  ( Runner
  , newRunner
  , check
  , finish
  ) where

import Control.Monad (unless, when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List (stripPrefix)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Test.QuickCheck (Args (..), Testable, isSuccess, quickCheckWithResult, stdArgs)
import Text.Read (readMaybe)

data Runner = Runner
  { runnerArgs     :: Args
  , runnerFailures :: IORef Int
  }

-- | A runner whose test count comes from @--qc-max-success=N@ (default 100).
newRunner :: IO Runner
newRunner = do
  argv <- getArgs
  n <- case [v | a <- argv, Just v <- [stripPrefix "--qc-max-success=" a]] of
    [] -> pure 100
    vs -> maybe (fail ("--qc-max-success: not a count: " ++ concat vs)) pure
            (readMaybe (foldr const "" (reverse vs)))
  Runner stdArgs {maxSuccess = n} <$> newIORef 0

-- | Check one property, recording it when it does not succeed.
check :: Testable p => Runner -> p -> IO ()
check r p = do
  result <- quickCheckWithResult (runnerArgs r) p
  unless (isSuccess result) (modifyIORef' (runnerFailures r) (+ 1))

-- | Report the verdict; any recorded failure exits non-zero.
finish :: Runner -> IO ()
finish r = do
  failures <- readIORef (runnerFailures r)
  when (failures > 0) $ do
    putStrLn (show failures ++ " properties did not pass.")
    exitFailure
  putStrLn "All properties passed."
