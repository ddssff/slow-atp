{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE CPP #-}

import Prelude hiding (negate,sum,pred)
import qualified Data.Set as S
import Data.List (intercalate,minimumBy,maximumBy,find,partition,delete)
import Data.Maybe
import qualified Data.Map as M
import Data.Time.Clock
import Debug.Trace

import PropositionalLogic hiding (nnf)
import FirstOrderLogic hiding (replace)
import Types
import Failing
import Equality

main = (time . putStrLn . show . meson . equalitize) wishnu {- ewd -}

-- ∃x. (x=f[g[x]] ∧ ∀x'. (x'=f[g[x']] ⇒ x=x')) ⇔ ∃y. (y=g[f[y]] ∧ ∀y'. (y'=g[f[y']] ⇒ y=y'))
wishnu :: Formula FOL
wishnu = (Iff (Exists "x" (And (Atom (R "=" [Var "x", (Fn "f" [Fn "g" [Var "x"]])]))
                               (Forall "x'" (Imp (Atom (R "=" [Var "x'", (Fn "f" [Fn "g" [Var "x'"]])]))
                                                 (Atom (R "=" [Var "x", Var "x'"]))))))
              (Exists "y" (And (Atom (R "=" [Var "y", (Fn "g" [Fn "f" [Var "y"]])]))
                               (Forall "y'" (Imp (Atom (R "=" [Var "y'", (Fn "g" [Fn "f" [Var "y'"]])]))
                                                 (Atom (R "=" [Var "y", Var "y'"])))))))

-- (∀x. (f[x] ⇒ g[x])) ∧
-- (∃x. f[x]) ∧
-- (∀x. (∀y. (g[x] ∧ g[y] ⇒ x .=. y))) ⇒
-- (∀y. (g[y] ⇒ f[y]))
ewd :: Formula FOL
ewd = Imp (And (And (Forall "x" (Imp (Atom (R "f" [Var "x"])) (Atom (R "g" [Var "x"]))))
                    (Exists "x" (Atom (R "f" [Var "x"]))))
               (Forall "x" (Forall "y" (Imp (And (Atom (R "g" [Var "x"])) (Atom (R "g" [Var "y"])))
                                            (Atom (R "=" [Var "x", Var "y"]))))))
          (Forall "y" (Imp (Atom (R "g" [Var "y"])) (Atom (R "f" [Var "y"]))))

time :: IO t -> IO t
time a = do
  start <- getCurrentTime
  v <- a
  end <- getCurrentTime
  putStrLn $ "Computation time: " ++ show (diffUTCTime end start)
  return v
