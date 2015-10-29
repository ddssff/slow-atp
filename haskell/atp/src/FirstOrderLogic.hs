{-# LANGUAGE CPP #-}
module FirstOrderLogic where

import Prelude hiding (negate,sum,pred)
import qualified Data.Set as S
import Data.List (delete)
import Data.Maybe
import qualified Data.Map as M
import Debug.Trace

import PropositionalLogic hiding (nnf)
import Types
import Failing

meson :: Formula FOL -> S.Set Int
meson fm =
  let fm1 = askolemize (Not (generalize fm)) in
  S.map (puremeson . list_conj) (simpdnf fm1)

puremeson :: Formula FOL -> Int
puremeson fm = deepen (\n -> mexpand rules [] FF return (M.empty,n,0) >> return n) 0
 where
  cls = simpcnf (specialize (pnf fm))
  rules = foldr ((++) . contrapositives) [] (flatten cls)

mexpand :: [PrologRule]
        -> [Formula FOL]
        -> Formula FOL
        -> ((M.Map String Term, Int, Int) -> Failing a)
        -> (M.Map String Term, Int, Int)
        -> Failing a
mexpand rules ancestors g cont (env,n,k)
  | n < 0 = failure "Too deep"
  | otherwise = tryM (tryfind firstCheck ancestors) (tryfind secondCheck rules)
   where
     firstCheck a = do
       ul <- unifyLiterals env (g,negate a)
       cont (ul,n,k)
     secondCheck rule = do
       let (Prolog asm c, k') = renamerule k rule
       ul <- unifyLiterals env (g,c)
       foldr (mexpand rules (g:ancestors)) cont asm (ul, n - length asm, k')


contrapositives :: [Formula FOL] -> [PrologRule]
contrapositives cls =
  let base = map (\c -> Prolog (map negate (delete c cls)) c) cls in
  if all negative cls then Prolog (map negate cls) FF : base else base

renamerule
  :: Int
     -> PrologRule
     -> (PrologRule, Int)
renamerule k (Prolog asm c) = (Prolog (map inst asm) (inst c),k+n)
 where
  fvs = fv (list_conj (c:asm))
  n = length fvs
  vvs = map (\i -> "_" ++ show i) [k .. (k+n-1)]
  inst = subst (fpf (S.toList fvs) (map Var vvs))

deepen :: (Num a, Show a) => (a -> Failing r) -> a -> r
deepen f n = trace ("Searching with depth limit " ++ show n)
   (try (f n) (deepen f (n + 1)))

unifyLiterals
  :: M.Map String Term
     -> (Formula FOL, Formula FOL) -> Failing (M.Map String Term)
unifyLiterals env (Atom (R p1 a1),Atom (R p2 a2)) = unify env [(Fn p1 a1,Fn p2 a2)]
unifyLiterals env (Not p,Not q) = unifyLiterals env (p,q)
unifyLiterals env (FF,FF) = return env
unifyLiterals _ _ = failure "Can't unify literals"

unify :: M.Map String Term -> [(Term, Term)] -> Failing (M.Map String Term)
unify env [] = return env
unify env ((Fn f fargs,Fn g gargs) : oth) =
   if f == g && length fargs == length gargs
   then unify env (zip fargs gargs ++ oth)
   else failure "impossible unification"
unify env ((Var x,t) : oth) =
   if M.member x env then unify env ((env M.! x,t) : oth)
   else do
     z <- istriv env x t
     unify (if z then env else M.insert x t env) oth
unify env ((t,Var x) : oth) = unify env ((Var x,t) : oth)

istriv :: M.Map String Term -> String -> Term -> Failing Bool
istriv env x (Var y)
 | y == x = return True
 | M.member y env = istriv env x (env M.! y)
 | otherwise = return False
istriv env x (Fn _ args) = do
   a <- mapM (istriv env x) args
   if or a then failure "cyclic" else return False

fpf :: Ord k => [k] -> [a] -> M.Map k a
fpf xs ys = M.fromList $ zip xs ys

specialize :: Formula t -> Formula t
specialize (Forall _ p) = specialize p
specialize fm = fm

askolemize :: Formula FOL -> Formula FOL
askolemize fm = fst (skolem (nnf (simplify fm)) (S.map fst (functions fm)))

funcs :: Term -> S.Set (String, Int)
funcs (Var _) = S.empty
funcs (Fn f args) = S.insert (f,length args) (S.unions (map funcs args))

functions :: Formula FOL -> S.Set (String, Int)
functions fm = S.fold S.union S.empty (atom_union (\(R _ a) -> S.unions (map funcs a)) fm)

skolem :: Formula FOL -> S.Set String -> (Formula FOL, S.Set String)
skolem fm@(Exists y p) fns = skolem (subst (M.singleton y fx) p) (S.insert f fns)
 where
  xs = fv fm
  f = variant (if S.null xs then "c_"++y else "f_"++y) fns
  fx = Fn f (map Var (S.toList xs))
skolem (Forall x p) fns = (Forall x p',fns')
 where
  (p',fns') = skolem p fns
skolem (And p q) fns = skolem2 (uncurry And) (p,q) fns
skolem (Or p q) fns = skolem2 (uncurry Or) (p,q) fns
skolem fm fns = (fm,fns)

skolem2 :: ((Formula FOL, Formula FOL) -> t)
        -> (Formula FOL, Formula FOL)
        -> S.Set String
        -> (t, S.Set String)
skolem2 cons (p,q) fns = (cons (p',q'),fns'')
 where
  (p',fns') = skolem p fns
  (q',fns'') = skolem q fns'

pnf fm = prenex (nnf (simplify fm))

prenex :: Formula FOL -> Formula FOL
prenex (Forall x p) = Forall x (prenex p)
prenex (Exists x p) = Exists x (prenex p)
prenex (And p q) = pullquants (And (prenex p) (prenex q))
prenex (Or p q) = pullquants (Or (prenex p) (prenex q))
prenex fm = fm

pullquants :: Formula FOL -> Formula FOL
pullquants fm@(And (Forall x p) (Forall y q)) = pullq (True,True) fm Forall And x y p q
pullquants fm@(Or (Exists x p) (Exists y q)) = pullq (True,True) fm Exists Or x y p q
pullquants fm@(And (Forall x p) q) = pullq (True,False) fm Forall And x x p q
pullquants fm@(And p (Forall y q)) = pullq (False,True) fm Forall And y y p q
pullquants fm@(Or (Forall x p) q) = pullq (True,False) fm Forall Or x x p q
pullquants fm@(Or p (Forall y q)) = pullq (False,True) fm Forall Or y y p q
pullquants fm@(And (Exists x p) q) = pullq (True,False) fm Exists And x x p q
pullquants fm@(And p (Exists y q)) = pullq (False,True) fm Exists And y y p q
pullquants fm@(Or (Exists x p) q) = pullq (True,False) fm Exists Or x x p q
pullquants fm@(Or p (Exists y q)) = pullq (False,True) fm Exists Or y y p q
pullquants fm = fm

pullq (l,r) fm quant op x y p q = quant z (pullquants (op p' q'))
 where
  z = variant x (fv fm)
  p' = if l then subst (M.singleton x (Var z)) p else p
  q' = if r then subst (M.singleton y (Var z)) q else q

nnf (And p q) = And (nnf p) (nnf q)
nnf (Or p q) = Or (nnf p) (nnf q)
nnf (Imp p q) = Or (nnf (Not p)) (nnf q)
nnf (Iff p q) = Or (And (nnf p) (nnf q)) (And (nnf (Not p)) (nnf (Not q)))
nnf (Not (Not p)) = nnf p
nnf (Not (And p q)) = Or (nnf (Not p)) (nnf (Not q))
nnf (Not (Or p q)) = And (nnf (Not p)) (nnf (Not q))
nnf (Not (Imp p q)) = And (nnf p) (nnf (Not q))
nnf (Not (Iff p q)) = Or (And (nnf p) (nnf (Not q))) (And (nnf (Not p)) (nnf q))
nnf (Forall x p) = Forall x (nnf p)
nnf (Exists x p) = Exists x (nnf p)
nnf (Not (Forall x p)) = Exists x (nnf (Not p))
nnf (Not (Exists x p)) = Forall x (nnf (Not p))
nnf fm = fm

simplify :: Formula FOL -> Formula FOL
simplify (Not p) = simplify1 (Not (simplify p))
simplify (And p q) = simplify1 (And (simplify p) (simplify q))
simplify (Or p q) = simplify1 (Or (simplify p) (simplify q))
simplify (Imp p q) = simplify1 (Imp (simplify p) (simplify q))
simplify (Iff p q) = simplify1 (Iff (simplify p) (simplify q))
simplify (Forall x p) = simplify1 (Forall x (simplify p))
simplify (Exists x p) = simplify1 (Exists x (simplify p))
simplify fm = fm

simplify1 :: Formula FOL -> Formula FOL
simplify1 fm@(Forall x p)
 | S.member x (fv p) = fm
 | otherwise = p
simplify1 fm@(Exists x p)
 | S.member x (fv p) = fm
 | otherwise = p
simplify1 fm = psimplify1 fm

-- Section 3.4

subst :: M.Map String Term -> Formula FOL -> Formula FOL
subst subfn FF = FF
subst subfn TT = TT
subst subfn (Atom (R p args)) = Atom (R p (map (tsubst subfn) args))
subst subfn (Not p) = Not (subst subfn p)
subst subfn (And p q) = And (subst subfn p) (subst subfn q)
subst subfn (Or p q) = Or (subst subfn p) (subst subfn q)
subst subfn (Imp p q) = Imp (subst subfn p) (subst subfn q)
subst subfn (Iff p q) = Iff (subst subfn p) (subst subfn q)
subst subfn (Forall x p) = substq subfn Forall x p
subst subfn (Exists x p) = substq subfn Exists x p

substq subfn quant x p = quant x' (subst (M.insert x (Var x') subfn) p)
 where x' = if (any (\y -> S.member x (fvt (maybe (Var y) id (M.lookup y subfn))))
                    (S.delete x (fv p)))
            then variant x (fv (subst (M.delete x subfn) p)) else x

variant :: String -> S.Set String -> String
variant x vars
 | S.member x vars = variant (x ++ "'") vars
 | otherwise = x

tsubst :: M.Map String Term -> Term -> Term
tsubst sfn tm@(Var x) = maybe tm id (M.lookup x sfn)
tsubst sfn (Fn f args) = Fn f (map (tsubst sfn) args)

generalize :: Formula FOL -> Formula FOL
generalize fm = foldr Forall fm (fv fm)

-- Section 3.3

fv :: Formula FOL -> S.Set String
fv FF = S.empty
fv TT = S.empty
fv (Atom (R _ args)) = S.unions (map fvt args)
fv (Not p) = fv p
fv (And p q) = S.union (fv p) (fv q)
fv (Or p q) = S.union (fv p) (fv q)
fv (Imp p q) = S.union (fv p) (fv q)
fv (Iff p q) = S.union (fv p) (fv q)
fv (Forall x p) = S.delete x (fv p)
fv (Exists x p) = S.delete x (fv p)

fvt :: Term -> S.Set String
fvt (Var x) = S.singleton x
fvt (Fn f args) = S.unions (map fvt args)
