open import Level
open import Function
open import Relation.Binary.PropositionalEquality

postulate
  ℓ ℓ′ : Level
  ℓ≡ℓ′ : ℓ ≡ ℓ′
  X    : Set ℓ

Set⟨_⟩ : ∀ ℓ → Set (suc ℓ)
Set⟨ ℓ ⟩ = Set ℓ

f : Set⟨ ℓ ⟩ → Set⟨ ℓ′ ⟩
f rewrite ℓ≡ℓ′ = id

Y : Set⟨ ℓ′ ⟩
-- Y rewrite sym ℓ≡ℓ′ = X
-- Y = subst {!λ (x : Level) → Set⟨ x ⟩!} {!!} {!X!}
Y = f X

-- Y =
--   ? ⊣
--   begin

--   ∎ where open ≡-Reasoning
