module Reordering where

open import Prelude.Init
open import Prelude.Setoid
open import Prelude.Closures
open import Prelude.DecEq
open import Prelude.DecLists
open import Prelude.Decidable

-- Configurations: collections of numbers
infixr 4 _∣_
data ℂ : Set where
  -- left, right, and completed inputs
  ⟨_ _⟩ ⟪_⟫ : ℕ → ℂ
  -- putting together configurations
  _∣_ : Op₂ ℂ

variable
  c c′ C C′ Γ Γ′ Δ Δ′ : ℂ
  n : ℕ

toList : ℂ → List ℕ
toList = λ where
  (l ∣ r) → toList l ++ toList r
  (⟨ x)   → [ x ]
  (x ⟩)   → [ x ]
  ⟪ x ⟫   → [ x ]

instance
  Setoid-ℂ : ISetoid ℂ
  Setoid-ℂ ._≈_ c c′ = toList c ↭ toList c′

  DecSetoid-ℂ : IDecSetoid ℂ
  DecSetoid-ℂ ._≈?_ c c′ = toList c ↭? toList c′

infixr 3 _—→_
data _—→_ : Rel₀ ℂ where

  CLOSE : ∀ n →
    ⟨ n ∣ n ⟩ ∣ Γ
    —→
    ⟪ n ⟫ ∣ Γ

open UpToReflexiveTransitiveClosure _—→_

_ :  2 ⟩ ∣ ⟨ 0 ∣ ⟨ 2 ∣ 0 ⟩ ∣ 1 ⟩
  —↠ ⟪ 0 ⟫ ∣ ⟪ 2 ⟫ ∣ 1 ⟩
_ = begin
  2 ⟩ ∣ ⟨ 0 ∣ ⟨ 2 ∣ 0 ⟩ ∣ 1 ⟩ —→⟨ CLOSE {Γ = 2 ⟩ ∣ ⟨ 2 ∣ 1 ⟩} 0 ⟩
  ⟪ 0 ⟫ ∣ 2 ⟩ ∣ ⟨ 2 ∣ 1 ⟩     —→⟨ CLOSE {Γ = ⟪ 0 ⟫ ∣ 1 ⟩} 2 ⟩
  ⟪ 0 ⟫ ∣ ⟪ 2 ⟫ ∣ 1 ⟩         ∎
