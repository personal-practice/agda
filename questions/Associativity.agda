module Associativity where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List

module Left where
  data X : Set where
    `_ : Nat → X
    _∣_ : X → X → X

  infixr 0 _∣_

  head : X → X
  head = λ where
    (` n)   → ` n
    (l ∣ _) → l

  last : X → X
  last = λ where
    (` n)   → ` n
    (_ ∣ r) → last r

module Right where
  data X : Set where
    `_ : Nat → X
    _∣_ : X → X → X

  infixl 0 _∣_

  head : X → X
  head = λ where
    (` n)   → ` n
    (l ∣ _) → head l

  last : X → X
  last = λ where
    (` n)   → ` n
    (_ ∣ r) → r

  _ : head (` 1 ∣ ` 2 ∣ ` 3) ≡ ` 1
  _ = refl

  _ : last (` 1 ∣ ` 2 ∣ ` 3) ≡ ` 3
  _ = refl
