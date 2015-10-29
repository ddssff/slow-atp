{-# LANGUAGE OverloadedLists #-}
module Types where

import Text.PrettyPrint
import Data.List
import Data.Maybe
import Data.Char
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Sequence
import Failing
import Control.Monad (foldM)

data PrologRule =
  Prolog (S.Set (Formula FOL)) (Formula FOL)
  deriving (Eq, Ord)

data Formula a = FF
               | TT
               | Atom a
               | Not !(Formula a)
               | And !(Formula a) !(Formula a)
               | Or  !(Formula a) !(Formula a)
               | Imp !(Formula a) !(Formula a)
               | Iff !(Formula a) !(Formula a)
               | Forall String !(Formula a)
               | Exists String !(Formula a)
               deriving (Eq, Ord)

data Term =
    Var String
  | Fn String (Seq Term)
  deriving (Eq, Ord)

data FOL =
  R String (Seq Term)
  deriving (Eq, Ord)

tryfind :: (t -> Failing b) -> Seq t -> Failing b
tryfind f s =
    case viewl s of
      EmptyL -> failure "tryfind"
      h :< t -> tryM (f h) (tryfind f t)

settryfind :: (t -> Failing b) -> S.Set t -> Failing b
settryfind f s =
    case S.minView s of
      Nothing -> failure "tryfind"
      Just (h, t) -> tryM (f h) (settryfind f t) -- either (const (tryfind f t)) return (f h)

setToSeq :: S.Set a -> Seq a
setToSeq = foldr (<|) mempty . S.toAscList

setFromSeq :: Ord a => Seq a -> S.Set a
setFromSeq = foldr S.insert mempty

setUnions :: Ord a => Seq (S.Set a) -> S.Set a
setUnions = foldr S.union mempty
