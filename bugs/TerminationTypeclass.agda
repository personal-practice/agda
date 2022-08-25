open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Setoid

module TerminationTypeclass (Atom : Set) ⦃ _ : DecEq Atom ⦄ where

record Swap (A : Set ℓ) : Set ℓ where
  infixr 10 ⦅_↔_⦆_
  field ⦅_↔_⦆_  : Atom → Atom → A → A
open Swap ⦃...⦄ public

private variable
  A : Set ℓ
  𝕒 𝕓 𝕔 𝕕 : Atom
  x y : A

record SwapLaws
  (A : Set ℓ) ⦃ _ : Swap A ⦄ ⦃ ls : Lawful-Setoid A ⦄ : Set (ℓ ⊔ₗ relℓ)
  where field
    cong-swap : ∀ {x y : A} → x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ 𝕒 ↔ 𝕓 ⦆ y
    swap-comm : ∀ {x : A} → ⦅ 𝕒 ↔ 𝕓 ⦆ ⦅ 𝕔 ↔ 𝕕 ⦆ x ≈ ⦅ 𝕔 ↔ 𝕕 ⦆ ⦅ 𝕒 ↔ 𝕓 ⦆ x
open SwapLaws ⦃...⦄ public

postulate TODO : ∀ {A : Set ℓ} → A

instance
  Setoid-Atom : ISetoid Atom
  Setoid-Atom = λ where
    .relℓ → 0ℓ
    ._≈_  → _≡_

  SetoidLaws-Atom : Setoid-Laws Atom
  SetoidLaws-Atom .isEquivalence = PropEq.isEquivalence

  Swap-Atom : Swap Atom
  Swap-Atom .⦅_↔_⦆_ a₁ a₂ a =
    if      a == a₁ then a₂
    else if a == a₂ then a₁
    else                 a

  SwapLaws-Atom : SwapLaws Atom
  -- SwapLaws-Atom .cong-swap refl = refl
  SwapLaws-Atom .cong-swap = λ where refl → refl
  SwapLaws-Atom .swap-comm {a}{b}{c}{d}{x}
    with a ≟ b
  ... | yes refl = begin
    ⦅ a ↔ b ⦆ ⦅ c ↔ d ⦆ x ≈⟨ TODO ⟩
    ⦅ c ↔ d ⦆ x           ≈⟨ cong-swap TODO ⟩
    ⦅ c ↔ d ⦆ ⦅ a ↔ b ⦆ x ∎ where open ≈-Reasoning
  ... | no _ = TODO
