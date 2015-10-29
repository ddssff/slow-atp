{-# LANGUAGE CPP #-}
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
import Equality

main = putStrLn . show . meson . equalitize $ wishnu

wishnu :: Formula FOL
wishnu = (Iff (Exists "x" (And (Atom (R "=" [Var "x", (Fn "f" [Fn "g" [Var "x"]])]))
                               (Forall "x'" (Imp (Atom (R "=" [Var "x'", (Fn "f" [Fn "g" [Var "x'"]])]))
                                                 (Atom (R "=" [Var "x", Var "x'"]))))))
              (Exists "y" (And (Atom (R "=" [Var "y", (Fn "g" [Fn "f" [Var "y"]])]))
                               (Forall "y'" (Imp (Atom (R "=" [Var "y'", (Fn "g" [Fn "f" [Var "y'"]])]))
                                                 (Atom (R "=" [Var "y", Var "y'"])))))))
