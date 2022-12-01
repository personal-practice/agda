open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.LiftOmega

{-
infixr -100 _⊗₀_ _⊗₁_ _⊗₂_ _⊗_
postulate
  _⊗₀_ : Type  → Type  → Typeω
  _⊗₁_ : Typeω → Type  → Typeω
  _⊗₂_ : Type  → Typeω → Typeω
  _⊗_  : Typeω → Typeω → Typeω

  B   : Type
  𝔸 ℂ : Typeω

_ : Typeω
_ = 𝔸 ⊗ ↑ B ⊗ ℂ

data 𝕃ist : Typeω where
  [] : 𝕃ist
  _∷_ : ∀ {A : Type ℓ} →
    𝔸 → 𝕃ist → 𝕃ist

data 𝕃ist₁ : Typeω₁ where
  [] : 𝕃ist₁
  _∷_ : ∀ {A : Typeω} →
    A → 𝕃ist₁ → 𝕃ist₁

data 𝕃ist₂ : Typeω₂ where
  [] : 𝕃ist₂
  _∷_ : ∀ {A : Typeω₁} →
    A → 𝕃ist₂ → 𝕃ist₂

open import Level
postulate B₁ : Type₁

xs : 𝕃ist₂
xs = 𝔸 ∷ ↑ B ∷ ℂ ∷ []

fs : 𝕃ist₂
fs = _⊗₀_ ∷ _⊗₁_ ∷ _⊗₂_ ∷ _⊗_ ∷ []
-}

private variable A : Type ℓ; Aω Bω Cω : Typeω

record X (A : Type) : Type where
  field x : A
open X ⦃...⦄
record Y (A : Type) : Type where
  field y : A
open Y ⦃...⦄
record Z (A : Type) : Type where
  field z : A
open Z ⦃...⦄
record Xω (Aω : Typeω) : Typeω where
  field xω : Aω
open Xω ⦃...⦄
record Yω (Aω : Typeω) : Typeω where
  field yω : Aω
open Yω ⦃...⦄
record Zω (Aω : Typeω) : Typeω where
  field zω : Aω
open Zω ⦃...⦄


infixr -100 _⊗_
record _⊗_ (A : Typeω) (B : Typeω) : Typeω where
  field ⦃ ↜ ⦄ : A; ⦃ ↝ ⦄ : B
instance
  mk⊗ : ⦃ Aω ⦄ → ⦃ Bω ⦄ → Aω ⊗ Bω
  mk⊗ = record {}
open _⊗_ ⦃...⦄ hiding (↜; ↝)

module _ ⦃ _ : Xω Aω ⊗ Yω Bω ⦄ where
  _ : Aω; _ = xω
  _ : Bω; _ = yω
module _ ⦃ _ : ↑ X A ⊗ Yω Bω ⦄ where
  _ : A; _ = x
  _ : Bω; _ = yω
module _ ⦃ _ : Xω Aω ⦄ ⦃ _ : Yω Aω ⦄ where
  _ : Xω Aω ⊗ Yω Aω
  _ = itω
module _ ⦃ _ : Xω Aω ⦄ ⦃ _ : Yω Aω ⦄ ⦃ _ : Zω Aω ⦄ where
  _ : Xω Aω ⊗ Yω Aω ⊗ Zω Aω
  _ = itω
module _ ⦃ _ : X A ⦄ ⦃ _ : Yω Aω ⦄ ⦃ _ : Zω Aω ⦄ where
  _ : ↑ X A ⊗ Yω Aω ⊗ Zω Aω
  _ = itω
module _ ⦃ _ : X A ⦄ ⦃ _ : Yω Aω ⦄ ⦃ _ : Z A ⦄ where
  _ : ↑ X A ⊗ Yω Aω ⊗ ↑ Z A
  _ = itω
module _ ⦃ _ : X A ⦄ ⦃ _ : Y A ⦄ ⦃ _ : Zω Aω ⦄ where
  _ : ↑ X A ⊗ ↑ Y A ⊗ Zω Aω
  _ = itω
