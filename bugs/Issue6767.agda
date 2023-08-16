-- {-# OPTIONS --no-forcing #-}
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

-- predicates P and Q
data P : Nat → Set where
  mkP : Nat → P 0

Q : Nat → Set
Q n = P (go n)
  where go : Nat → Nat
        go _ = 0

substQ : ∀ {n} → 0 ≡ n → Q 0 → Q n
substQ refl q = q

-- relation between predicates
data _~_ : P 0 → (Σ Nat λ n → P n) → Set where
  mk : ∀ {n} {p : Q 0} (eq : 0 ≡ n) → mkP n ~ (_ , substQ eq p)

-- simple pattern match causes internal error, but goes away with `--no-forcing`
testPatternMatch-~ : ∀ {p q} → p ~ q → Nat
testPatternMatch-~ (mk eq) = 0
{-
An internal error has occurred. Please report this as a bug.
Location of the error: __IMPOSSIBLE__, called at src/full/Agda/TypeChecking/Rules/LHS/Unify.hs:1003:24 in Agda-2.6.3-9e071f84265c43e7e112975b042b5fc260f5975b6fa7ddedbcdfbab1a60fa0a7:Agda.TypeChecking.Rules.LHS.Unify
-}
