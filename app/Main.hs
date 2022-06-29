{-# LANGUAGE ExistentialQuantification #-}

module Main where

data Worker = forall b.
      (Show b) =>
    Worker
    { builder :: b
    }

test :: Worker -> String
test (Worker b) = show b

main :: IO ()
main = putStrLn . test $ Worker 123

-- $> main
