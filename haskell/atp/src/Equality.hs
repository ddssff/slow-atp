{-# LANGUAGE CPP #-}
module Equality where

import Prelude hiding (negate,sum,pred)
import qualified Data.Set as S
import Data.List (intercalate,minimumBy,maximumBy,find,partition,delete)
import Data.Maybe
import qualified Data.Map as M
import Debug.Trace

import PropositionalLogic hiding (nnf)
import FirstOrderLogic hiding (replace)
import Types
import Failing

mk_eq s t = Atom (R "=" [s,t])

predicates fm = atom_union (\(R p a) -> (p,length a)) fm

function_congruence :: (String, Int) -> Maybe (Formula FOL)
function_congruence (f,0) = Nothing
function_congruence (f,n) = Just (foldr Forall (Imp ant con) (argnames_x ++ argnames_y))
 where
  argnames_x = map (\k -> "x" ++ (show k)) [1..n]
  argnames_y = map (\k -> "y" ++ (show k)) [1..n]
  args_x = map Var argnames_x
  args_y = map Var argnames_y
  ant = foldr1 And (zipWith mk_eq args_x args_y)
  con = mk_eq (Fn f args_x) (Fn f args_y)

predicate_congruence :: (String, Int) -> Maybe (Formula FOL)
predicate_congruence (p,0) = Nothing
predicate_congruence (p,n) = Just (foldr Forall (Imp ant con) (argnames_x ++ argnames_y))
 where
  argnames_x = map (\k -> "x" ++ (show k)) [1..n]
  argnames_y = map (\k -> "y" ++ (show k)) [1..n]
  args_x = map Var argnames_x
  args_y = map Var argnames_y
  ant = foldr1 And (zipWith mk_eq args_x args_y)
  con = Imp (Atom (R p args_x)) (Atom (R p args_y))

equivalence_axioms :: [Formula FOL]
-- equivalence_axioms = map parseFOL ["forall x. x = x", "forall x y z. x = y & x = z ==> y = z"]
equivalence_axioms = [Forall "x" (Atom (R "=" [Var "x", Var "x"])),
                      Forall "x" (Forall "y" (Forall "z" (Imp (And (Atom (R "=" [Var "x", Var "y"]))
                                                                   (Atom (R "=" [Var "x", Var "z"])))
                                                              (Atom (R "=" [Var "y", Var "z"])))))
                     ]

equalitize :: Formula FOL -> Formula FOL
equalitize fm
  | (S.notMember ("=",2) allpreds) = fm
  | otherwise = Imp (foldr1 And axioms) fm
 where
  allpreds = predicates fm
  preds = S.delete ("=",2) allpreds
  funcs = functions fm
  axioms = equivalence_axioms ++ (catMaybes$S.toList ((S.map function_congruence funcs) `S.union` (S.map predicate_congruence preds)))
