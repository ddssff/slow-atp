{-# LANGUAGE CPP #-}
module Types where

import Text.PrettyPrint
import Data.List
import Data.Maybe
import Data.Char
import qualified Data.Set as S
import qualified Data.Map as M
import Failing
import Control.Monad (foldM)

data PrologRule = Prolog [Formula FOL] (Formula FOL)   deriving (Eq,Ord)

data Formula a = FF
               | TT
               | Atom a
               | Not !(Formula a)
               | And !(Formula a) !(Formula a)
               | Or !(Formula a) !(Formula a)
               | Imp !(Formula a) !(Formula a)
               | Iff !(Formula a) !(Formula a)
               | Forall String !(Formula a)
               | Exists String !(Formula a)
               deriving (Eq, Ord)

data Term = Var String | Fn String [Term]  deriving (Eq,Ord)

data FOL = R String [Term]  deriving (Eq,Ord)

tryfind :: (t -> Failing b) -> [t] -> Failing b
tryfind _ [] = failure "tryfind"
tryfind f (h:t) = tryM (f h) (tryfind f t) --either (const (tryfind f t)) return (f h)

flatten :: S.Set (S.Set a) -> [[a]]
flatten = (map S.toList) . S.toList
