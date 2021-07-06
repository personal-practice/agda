module Reordering4 where

open import Prelude.Init hiding (_≤_)
open import Prelude.General
open import Prelude.Closures
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Ord

open L.Mem hiding (_─_)

variable
  n : ℕ
  ns : List ℕ

_─_ : ∀ {n} (ns : List ℕ) → n ∈ ns → List ℕ
_─_ = L.Any._─_

length/─ : (n∈ : n ∈ ns) → length (ns ─ n∈) < length ns
length/─ (here px) = s≤s ≤-refl
length/─ (there n∈) = s≤s (length/─ n∈)

-- Configurations: collections of numbers
infix 5 _∙_
record C : Set where
  constructor _∙_
  field
    left  : List ℕ
    right : List ℕ
open C

IsCanonical : Pred₀ C
IsCanonical c = can (c .left) × can (c .right)
  module ∣IsCanonical∣ where
    can : Pred₀ (List ℕ)
    can xs = Unique xs × Sorted xs

IsCanonical? : Decidable¹ IsCanonical
IsCanonical? c = can? (c .left) ×-dec can? (c .right)
  where
    can? : Decidable¹ (∣IsCanonical∣.can c)
    can? = dec¹

infix 0 _∶-_
record ℂ : Set where
  constructor _∶-_
  field
    witness : C
    .can : IsCanonical witness
open ℂ

infix 0 _∶-∙
_∶-∙ : ∀ c → {True $ IsCanonical? c} → ℂ
_∶-∙ c {p} = c ∶- toWitness p

infixr -1 _—→_
data _—→_ : Rel₀ ℂ where

  CLOSE : ∀ {i o} n
    → {c : True $ IsCanonical? (i ∙ o)}
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

size : C → ℕ
size c = length (c .left) + length (c .right)

lemma : ∀ c c′ → c —→ c′ → size (c′ .witness) < size (c .witness)
lemma (i ∙ o ∶- _) .(_ ∙ _ ∶- _) (CLOSE n pᵢ pₒ) = juxtapose-+/< i< o<
  where
    i< : length (i ─ pᵢ) < length i
    i< = length/─ pᵢ

    o< : length (o ─ pₒ) < length o
    o< = length/─ pₒ

lemma∗ : ∀ c c′ → c —↠ c′ → size (c′ .witness) ≤ size (c .witness)
lemma∗ c .c (.c ∎) = ≤-refl
lemma∗ c c′ (.c —→⟨ x ⟩ p) = Nat.<⇒≤ $ Nat.<-transʳ (lemma∗ _ c′ p) (lemma c _ x)
