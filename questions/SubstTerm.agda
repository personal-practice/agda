module SubstTerm where

open import Prelude.Init
open import Prelude.Functor
open import Prelude.Semigroup
open import Prelude.Monad
open import Prelude.Show
open Meta
open import Prelude.Generics

patternArgsVars : List (Arg Pattern) → ℕ

patternVars : Pattern → ℕ
patternVars (con _ ps) = patternArgsVars ps
patternVars dot = 1
patternVars (var _) = 1
patternVars (lit x) = 0
patternVars (proj _) = 0
patternVars absurd = 0

patternArgsVars [] = 0
patternArgsVars (arg _ p ∷ ps) = patternVars p + patternArgsVars ps

Isubst : Set → Set
Isubst A = ℕ → List Term → A → A

isubstTerm : Isubst Term
isubstArgs : Isubst (List (Arg Term))
isubstArg : Isubst (Arg Term)
isubstAbs : Isubst (Abs Term)
isubstSort : Isubst Sort
isubstClauses : Isubst (List Clause)
isubstClause : Isubst Clause
{-# TERMINATING #-}
applyTerm : Term → List (Arg Term) → Term


applyTerm v [] = v
applyTerm (var x args) args₁ = var x (args ++ args₁)
applyTerm (con c args) args₁ = con c (args ++ args₁)
applyTerm (def f args) args₁ = def f (args ++ args₁)
applyTerm (meta x args) args₁ = meta x (args ++ args₁)
applyTerm (lam v (abs _ t)) (arg _ x ∷ args) = applyTerm (isubstTerm 0 [ x ] t) args
applyTerm (pat-lam cs args) args₁ = pat-lam cs (args ++ args₁)
applyTerm (pi a b) _ = pi a b
applyTerm (agda-sort s) _ = agda-sort s
applyTerm (lit l)  _ = lit l
applyTerm unknown _ = unknown


isubstTerm n σ (var x args) =
  case (n ≤? x) of
  λ { true →
       case index σ (x - n) of λ
        { nothing  → var (x - length σ) (isubstArgs n σ args)
        ; (just v) → applyTerm v (isubstArgs n σ args) }
    ; false → var x (isubstArgs n σ args) }
isubstTerm n σ (con c args) = con c (isubstArgs n σ args)
isubstTerm n σ (def f args) = def f (isubstArgs n σ args)
isubstTerm n σ (meta x args) = meta x (isubstArgs n σ args)
isubstTerm n σ (lam v b) = lam v (isubstAbs n σ b)
isubstTerm n σ (pat-lam cs args) = pat-lam (isubstClauses n σ cs) (isubstArgs n σ args)
isubstTerm n σ (pi a b) = pi (isubstArg n σ a) (isubstAbs n σ b)
isubstTerm n σ (agda-sort s) = agda-sort (isubstSort n σ s)
isubstTerm n σ (lit l) = lit l
isubstTerm n σ unknown = unknown

isubstSort n σ (set t) = set (isubstTerm n σ t)
isubstSort n σ (lit ln) = lit ln
isubstSort n σ unknown = unknown

isubstClauses n σ [] = []
isubstClauses n σ (c ∷ cs) = isubstClause n σ c ∷ isubstClauses n σ cs

isubstClause n σ (clause ps b) =
  case patternArgsVars ps of λ
  { zero    → clause ps (isubstTerm n σ b)
  ; (suc ln) → clause ps (isubstTerm (suc ln + n) (weaken (suc ln) σ) b)
  }
isubstClause n σ (absurd-clause ps) = absurd-clause ps

isubstArgs n σ [] = []
isubstArgs n σ (x ∷ args) = isubstArg n σ x ∷ isubstArgs n σ args
isubstArg n σ (arg i x) = arg i (isubstTerm n σ x)
isubstAbs n σ (abs x v) = abs x $ isubstTerm (suc n) (weaken 1 σ) v


Subst : Set → Set
Subst A = List Term → A → A

substTerm : Subst Term
substTerm = isubstTerm 0

substArgs : Subst (List (Arg Term))
substArgs = isubstArgs 0

substArg : Subst (Arg Term)
substArg = isubstArg 0

substAbs : Subst (Abs Term)
substAbs = isubstAbs 0

substSort : Subst Sort
substSort = isubstSort 0

substClauses : Subst (List Clause)
substClauses = isubstClauses 0

substClause : Subst Clause
substClause = isubstClause 0
