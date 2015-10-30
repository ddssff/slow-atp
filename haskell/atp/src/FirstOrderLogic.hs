{-# LANGUAGE OverloadedLists #-}
module FirstOrderLogic where

import Prelude hiding (negate,sum,pred,zip,length)
import qualified Data.Set as S
import Data.List (delete)
import Data.Maybe
import qualified Data.Map as M
import Data.Sequence as Seq -- (Seq, viewl, zip, (<|))
import Debug.Trace

import PropositionalLogic hiding (nnf)
import Types
import Failing

meson1 :: Formula FOL -> S.Set Int
meson1 fm =
  let fm1 = askolemize (Not (generalize fm)) in
  S.map (puremeson1 . list_conj) (simpdnf fm1)

puremeson1 :: Formula FOL -> Int
puremeson1 fm = deepen (\n -> mexpand1 rules mempty FF return (mempty,n,0) >> return n) 0
 where
  cls :: S.Set (S.Set (Formula FOL))
  cls = simpcnf (specialize (pnf fm))
  rules :: S.Set PrologRule
  rules = foldr (S.union . contrapositives) mempty cls

mexpand1 :: S.Set PrologRule
        -> S.Set (Formula FOL)
        -> Formula FOL
        -> ((M.Map V Term, Int, Int) -> Failing a)
        -> (M.Map V Term, Int, Int)
        -> Failing a
mexpand1 rules ancestors g cont (env,n,k)
  | n < 0 = failure "Too deep"
  | otherwise = tryM (settryfind firstCheck ancestors) (settryfind secondCheck rules)
   where
     firstCheck a = do
       ul <- unifyLiterals env (g,negate a)
       cont (ul,n,k)
     secondCheck rule = do
       let (Prolog asm c, k') = renamerule k rule
       ul <- unifyLiterals env (g,c)
       foldr (mexpand1 rules (S.insert g ancestors)) cont asm (ul, n - S.size asm, k')

meson2 :: Formula FOL -> S.Set Int
meson2 fm =
  let fm1 = askolemize (Not (generalize fm)) in
  S.map (puremeson2 . list_conj) (simpdnf fm1)

equal :: M.Map V Term -> Formula FOL -> Formula FOL -> Bool
equal env fm1 fm2 =
    case unifyLiterals env (fm1,fm2) of
      Success env' | env == env' -> True
      _ -> False

expand2 :: (S.Set (Formula FOL) ->
            ((M.Map V Term, Int, Int) -> Failing (M.Map V Term, Int, Int)) ->
            (M.Map V Term, Int, Int) -> Failing (M.Map V Term, Int, Int))
        -> S.Set (Formula FOL)
        -> Int
        -> S.Set (Formula FOL)
        -> Int
        -> Int
        -> ((M.Map V Term, Int, Int) -> Failing (M.Map V Term, Int, Int))
        -> M.Map V Term
        -> Int
        -> Failing (M.Map V Term, Int, Int)
expand2 expfn goals1 n1 goals2 n2 n3 cont env k =
    expfn goals1 (\(e1,r1,k1) ->
                      expfn goals2 (\(e2,r2,k2) ->
                                        if n2 + n1 <= n3 + r2 then Failure "pair" else cont (e2,r2,k2))
                                   (e1,n2+r1,k1))
                 (env,n1,k)

puremeson2 :: Formula FOL -> Int
puremeson2 fm = deepen (\n -> mexpand2 rules mempty FF return (mempty,n,0) >> return n) 0
 where
  cls :: S.Set (S.Set (Formula FOL))
  cls = simpcnf (specialize (pnf fm))
  rules :: S.Set PrologRule
  rules = foldr (S.union . contrapositives) mempty cls

mexpand2 :: S.Set PrologRule
         -> S.Set (Formula FOL)
         -> Formula FOL
         -> ((M.Map V Term, Int, Int) -> Failing (M.Map V Term, Int, Int))
         -> (M.Map V Term, Int, Int)
         -> Failing (M.Map V Term, Int, Int)
mexpand2 rules ancestors g cont (env,n,k)
  | n < 0 = failure "Too deep"
  | otherwise =
      if any (equal env g) ancestors
      then Failure "repetition"
      else tryM (settryfind doAncestor ancestors) (settryfind doRule rules)
   where
     doAncestor a = do
       ul <- unifyLiterals env (g,negate a)
       cont (ul,n,k)
     doRule :: PrologRule -> Failing (M.Map V Term, Int, Int)
     doRule rule = do
       let (Prolog asm c, k') = renamerule k rule
       ul <- unifyLiterals env (g,c)
       mexpands rules (S.insert g ancestors) asm cont (ul, n - S.size asm, k')

mexpands :: S.Set PrologRule
         -> S.Set (Formula FOL)
         -> S.Set (Formula FOL)
         -> ((M.Map V Term, Int, Int) -> Failing (M.Map V Term, Int, Int))
         -> (M.Map V Term, Int, Int)
         -> Failing (M.Map V Term, Int, Int)
mexpands rules ancestors gs cont (env,n,k) =
    if fromEnum n < 0
    then Failure "Too deep"
    else let m = S.size gs in
         if m <= 1
         then S.foldr (mexpand2 rules ancestors) cont gs (env,n,k)
         else let n1 = n `div` 2
                  n2 = n - n1 in
              let (goals1, goals2) = setSplitAt (m `div` 2) gs in
              let expfn = expand2 (mexpands rules ancestors) in
              case expfn goals1 n1 goals2 n2 (-1) cont env k of
                Success r -> Success r
                Failure _ -> expfn goals2 n1 goals1 n2 n1 cont env k

setSplitAt :: Ord a => Int -> S.Set a -> (S.Set a, S.Set a)
setSplitAt n s = go n (mempty, s)
    where
      go 0 (s1, s2) = (s1, s2)
      go i (s1, s2) = case S.minView s2 of
                         Nothing -> (s1, s2)
                         Just (x, s2') -> go (i - 1) (S.insert x s1, s2')

contrapositives :: S.Set (Formula FOL) -> S.Set PrologRule
contrapositives cls =
  let base = S.map (\c -> Prolog (S.map negate (S.delete c cls)) c) cls in
  if all negative cls then S.insert (Prolog (S.map negate cls) FF) base else base

renamerule :: Int
           -> PrologRule
           -> (PrologRule, Int)
renamerule k (Prolog asm c) = (Prolog (S.map inst asm) (inst c),k+n)
 where
  fvs = fv (list_conj (S.insert c asm))
  n = S.size fvs
  vvs :: Seq V
  vvs = fmap (\i -> V ("_" ++ show i)) [k .. (k+n-1)]
  inst = subst (fpf (setToSeq fvs) (fmap Var vvs))

deepen :: (Num a, Show a) => (a -> Failing r) -> a -> r
deepen f n = trace ("Searching with depth limit " ++ show n)
   (try (f n) (deepen f (n + 1)))

meson :: Formula FOL -> S.Set Int
meson = meson2

unifyLiterals
  :: M.Map V Term
     -> (Formula FOL, Formula FOL) -> Failing (M.Map V Term)
unifyLiterals env (Atom (R (P p1) a1),Atom (R (P p2) a2)) =
    unify env [(Fn (F p1) a1,Fn (F p2) a2)] -- a cheat here
unifyLiterals env (Not p,Not q) = unifyLiterals env (p,q)
unifyLiterals env (FF,FF) = return env
unifyLiterals _ _ = failure "Can't unify literals"

unify :: M.Map V Term -> Seq (Term, Term) -> Failing (M.Map V Term)
unify env pairs =
    case viewl pairs of
      EmptyL -> return env
      (Fn f fargs,Fn g gargs) :< oth ->
          if f == g && length fargs == length gargs
          then unify env (zip fargs gargs >< oth)
          else failure "impossible unification"
      (Var x,t) :< oth ->
          if M.member x env then unify env ((env M.! x,t) <| oth)
          else do
            z <- istriv env x t
            unify (if z then env else M.insert x t env) oth
      (t, Var x) :< oth -> unify env ((Var x,t) <| oth)

istriv :: M.Map V Term -> V -> Term -> Failing Bool
istriv env x (Var y)
 | y == x = return True
 | M.member y env = istriv env x (env M.! y)
 | otherwise = return False
istriv env x (Fn _ args) = do
   a <- mapM (istriv env x) args
   if or a then failure "cyclic" else return False

fpf :: Ord k => Seq k -> Seq a -> M.Map k a
fpf xs ys = foldr (\(x, y) mp -> M.insert x y mp) mempty (zip xs ys)

specialize :: Formula t -> Formula t
specialize (Forall _ p) = specialize p
specialize fm = fm

askolemize :: Formula FOL -> Formula FOL
askolemize fm = fst (skolem (nnf (simplify fm)) (S.map fst (functions fm)))

funcs :: Term -> S.Set (F, Int)
funcs (Var _) = mempty
funcs (Fn f args) = S.insert (f,length args) (setUnions (fmap funcs args))

functions :: Formula FOL -> S.Set (F, Int)
functions fm = S.fold S.union mempty (atom_union (\(R _ a) -> setUnions (fmap funcs a)) fm)

skolem :: Formula FOL -> S.Set F -> (Formula FOL, S.Set F)
skolem fm@(Exists y@(V s) p) fns = skolem (subst (M.singleton y fx) p) (S.insert f fns)
 where
  xs = fv fm
  f = variantF (F (if S.null xs then "c_"++s else "f_"++s)) fns
  fx = Fn f (fmap Var (setToSeq xs))
skolem (Forall x p) fns = (Forall x p',fns')
 where
  (p',fns') = skolem p fns
skolem (And p q) fns = skolem2 (uncurry And) (p,q) fns
skolem (Or p q) fns = skolem2 (uncurry Or) (p,q) fns
skolem fm fns = (fm,fns)

skolem2 :: ((Formula FOL, Formula FOL) -> t)
        -> (Formula FOL, Formula FOL)
        -> S.Set F
        -> (t, S.Set F)
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

pullq :: (Bool, Bool)
      -> Formula FOL
      -> (V -> Formula FOL -> Formula FOL)
      -> (Formula FOL -> Formula FOL -> Formula FOL)
      -> V -> V -> Formula FOL -> Formula FOL -> Formula FOL
pullq (l,r) fm quant op x y p q = quant z (pullquants (op p' q'))
 where
  z = variantVar x (fv fm)
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

subst :: M.Map V Term -> Formula FOL -> Formula FOL
subst subfn FF = FF
subst subfn TT = TT
subst subfn (Atom (R p args)) = Atom (R p (fmap (tsubst subfn) args))
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
            then variantVar x (fv (subst (M.delete x subfn) p)) else x

variantVar :: V -> S.Set V -> V
variantVar x@(V s) vars
 | S.member x vars = variantVar (V (s ++ "'")) vars
 | otherwise = x

variantF :: F -> S.Set F -> F
variantF x@(F s) vars
 | S.member x vars = variantF (F (s ++ "'")) vars
 | otherwise = x

tsubst :: M.Map V Term -> Term -> Term
tsubst sfn tm@(Var x) = maybe tm id (M.lookup x sfn)
tsubst sfn (Fn f args) = Fn f (fmap (tsubst sfn) args)

generalize :: Formula FOL -> Formula FOL
generalize fm = foldr Forall fm (fv fm)

-- Section 3.3

fv :: Formula FOL -> S.Set V
fv FF = mempty
fv TT = mempty
fv (Atom (R _ args)) = setUnions (fmap fvt args)
fv (Not p) = fv p
fv (And p q) = S.union (fv p) (fv q)
fv (Or p q) = S.union (fv p) (fv q)
fv (Imp p q) = S.union (fv p) (fv q)
fv (Iff p q) = S.union (fv p) (fv q)
fv (Forall x p) = S.delete x (fv p)
fv (Exists x p) = S.delete x (fv p)

fvt :: Term -> S.Set V
fvt (Var x) = S.singleton x
fvt (Fn f args) = setUnions (fmap fvt args)
