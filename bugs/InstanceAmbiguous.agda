open import Prelude.Init; open SetAsType

-- record Empty (A : Type) : Type where
--   field ε : A
-- open Empty ⦃...⦄ public

-- record Abs (A B : Type) : Type where
--   -- constructor _,_
--   field var : A
--         term : B
-- open Abs public

-- private variable A B : Type
-- instance
--   Empty-Abs : ⦃ Empty A ⦄ → ⦃ Empty B ⦄ → Empty (Abs A B)
--   Empty-Abs .ε = record {var = ε; term = ε}

--   Empty-× : ⦃ Empty A ⦄ → ⦃ Empty B ⦄ → Empty (A × B)
--   Empty-× .ε = ε , ε

-- instance _ = Empty ℕ ∋ λ where .ε → 0

-- _ : Abs ℕ ℕ
-- _ = ε


open import Prelude.Setoid

postulate
  Atom : Type
  -- Swap : Type → Type

private variable
  A B : Type
  𝕒 𝕓 : Atom

record Swap (A : Type) : Type where
  field ⦅_↔_⦆_ : Atom → Atom → A → A
open Swap ⦃...⦄ public

record Abs (A : Type) : Type where
  constructor abs
  field atom : Atom
        term : A
open Abs public

module _ (A : Type) ⦃ _ : ISetoid A ⦄ ⦃ _ : Swap A ⦄ where
  FinSupp : Pred A relℓ
  FinSupp x = ∀ y → x ≈ y

  record Laws : Type relℓ where
    field law : ∀ {x y : A} → x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ 𝕒 ↔ 𝕓 ⦆ y
  open Laws ⦃...⦄ public

module _ (A : Type) ⦃ _ : ISetoid A ⦄ ⦃ _ : Swap A ⦄ ⦃ _ : Laws A ⦄ where
  record ∀FinSupp : Type relℓ where
    field ∀fin : ∀ (x : A) → FinSupp A x
  open ∀FinSupp ⦃...⦄ public

postulate instance
  _ : ISetoid Atom
  _ : Swap Atom
  _ : Laws Atom
  _ : ∀FinSupp Atom

  _ : ⦃ Swap A ⦄ → ⦃ Swap B ⦄ → Swap (A × B)
  _ : ⦃ ISetoid A ⦄ → ⦃ ISetoid B ⦄ → ISetoid (A × B)
  _ : ⦃ _ : ISetoid A ⦄ ⦃ _ : ISetoid B ⦄
      ⦃ _ : Swap A ⦄ ⦃ _ : Swap B ⦄
    → ⦃ Laws A ⦄ → ⦃ Laws B ⦄
    → Laws (A × B)
  _ : ⦃ _ : ISetoid A ⦄ ⦃ _ : Swap A ⦄ ⦃ _ : Laws A ⦄
      ⦃ _ : ISetoid B ⦄ ⦃ _ : Swap B ⦄ ⦃ _ : Laws B ⦄
    → ⦃ ∀FinSupp A ⦄ → ⦃ ∀FinSupp B ⦄ → ∀FinSupp (A × B)

  _ : ⦃ Swap A ⦄ → Swap (Abs A)
  _ : ⦃ ISetoid A ⦄ → ISetoid (Abs A)
  _ : ⦃ _ : ISetoid A ⦄ ⦃ _ : Swap A ⦄
    → ⦃ Laws A ⦄ → Laws (Abs A)
  _ : ⦃ _ : ISetoid A ⦄ ⦃ _ : Swap A ⦄ ⦃ _ : Laws A ⦄
    → ⦃ ∀FinSupp A ⦄ → ∀FinSupp (Abs A)

_ : ∀FinSupp Atom
_ = it

_ : ∀FinSupp (Atom × Atom)
_ = it

_ : ∀FinSupp (Abs Atom)
_ = it

_ : ∀ {x y : Atom × Atom} → x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ 𝕒 ↔ 𝕓 ⦆ y
_ = law

_ : ∀ {x y : Abs Atom} → x ≈ y → ⦅ 𝕒 ↔ 𝕓 ⦆ x ≈ ⦅ 𝕒 ↔ 𝕓 ⦆ y
_ = law
