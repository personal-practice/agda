module Reordering2 where

open import Prelude.Init
open import Prelude.Setoid
open import Prelude.Closures
open import Prelude.DecEq
open import Prelude.DecLists
open import Prelude.Decidable
open import Prelude.Sets
open import Prelude.Nary

-- Configurations: collections of numbers
infix 4 _∙_
record ℂ : Set where
  constructor _∙_
  field
    left : ⟨ ℕ ⟩
    right : Set⟨ ℕ ⟩
open ℂ

variable
  c c′ C C′ Γ Γ′ Δ Δ′ : ℂ
  n : ℕ

infixr 3 _—→_
data _—→_ : Rel₀ ℂ where

  CLOSE : ∀ {i o} n
    → n ∈ˢ i
    → n ∈ˢ o
      --————————————————————————————————————————
    → i ∙ o
      —→
      (i ─ singleton n) ∙ (o ─ singleton n)

open ReflexiveTransitiveClosure _—→_

-- _ : (fromList ⟦ 0 , 2 ⟧ ─ singleton 0) ≈ˢ (singleton 2)
-- _ = auto

-- -- _ :  fromList ⟦ 0 , 2 ⟧ ∙ fromList ⟦ 2 , 0 , 1 ⟧
-- --   —↠ ∅ ∙ singleton 1
-- -- _ = begin
-- --   fromList ⟦ 0 , 2 ⟧ ∙ fromList ⟦ 2 , 0 , 1 ⟧ —→⟨ CLOSE 2 ? ? ⟩
-- --   singleton 0        ∙ fromList ⟦ 0 , 1 ⟧     —→⟨ CLOSE 0 ? ? ⟩
-- --   ∅                  ∙ singleton 1            ∎
