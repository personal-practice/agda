module Reordering3 where

open import Prelude.Init
open import Prelude.Closures
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Ord

open L.Mem hiding (_─_)
_─_ : ∀ {n} (ns : List ℕ) → n ∈ ns → List ℕ
_─_ = L.Any._─_

-- Canonicity expressed as a predicate.
record Canonical (A : Set ℓ) : Set (lsuc ℓ) where
  field IsCanonical : Pred₀ A
open Canonical ⦃ ... ⦄

infix 0 _∶-_
record ℂ (A : Set) ⦃ _ : Canonical A ⦄ : Set where
  constructor _∶-_
  field
    c : A
    .can : IsCanonical c
open ℂ

private variable A : Set ℓ

record DecCanonical (A : Set ℓ) ⦃ _ : Canonical A ⦄ : Set (lsuc ℓ) where
  field IsCanonical? : Decidable¹ IsCanonical
open DecCanonical ⦃ ... ⦄

infix 0 _∶-∙
_∶-∙ : ⦃ _ : Canonical A ⦄ → ⦃ _ : DecCanonical A ⦄ → ∀ c → {True $ IsCanonical? c} → ℂ A
_∶-∙ c {p} = c ∶- toWitness p

-- Configurations: collections of numbers
infix 5 _∙_
record C : Set where
  constructor _∙_
  field
    left  : List ℕ
    right : List ℕ
open C

instance
  Can-L : Canonical (List ℕ)
  Can-L .IsCanonical xs = Unique xs × Sorted xs

  DCan-L : DecCanonical (List ℕ)
  DCan-L .IsCanonical? xs = dec ×-dec dec

  Can-C : Canonical C
  Can-C .IsCanonical c = IsCanonical (c .left) × IsCanonical (c .right)

  DCan-C : DecCanonical C
  DCan-C .IsCanonical? c = IsCanonical? (c .left) ×-dec IsCanonical? (c .right)

infixr -1 _—→_
data _—→_ : Rel₀ (ℂ C) where

  CLOSE : ∀ {i o} n {c : True $ IsCanonical? (i ∙ o)}
    → (pᵢ : n ∈ i)
    → (pₒ : n ∈ o)
    → {c′ : True $ IsCanonical? $ (i ─ pᵢ) ∙ (o ─ pₒ)}
      --————————————————————————————————————————
    → (i ∙ o ∶- toWitness c)
      —→
      ((i ─ pᵢ) ∙ (o ─ pₒ) ∶- toWitness c′)

open ReflexiveTransitiveClosure _—→_

open import Prelude.Nary
_ :  ⟦ 0 , 2 ⟧ ∙ ⟦ 0 , 1 , 2 ⟧ ∶-∙
  —↠ []        ∙ [ 1 ]         ∶-∙
_ = begin
  (⟦ 0 , 2 ⟧ ∙ ⟦ 0 , 1 , 2 ⟧ ∶- _) —→⟨ CLOSE 2 auto auto ⟩
  ([ 0 ]     ∙ ⟦ 0 , 1 ⟧     ∶- _) —→⟨ CLOSE 0 auto auto ⟩
  ([]        ∙ [ 1 ]         ∶- _) ∎
