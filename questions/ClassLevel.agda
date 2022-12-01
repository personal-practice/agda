open import Agda.Primitive; open import Agda.Builtin.Equality
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥); open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)

-- #1. relℓ as a parameter
-- Jesper prefers this over #2: "proof is data, know the level they live in"
record Ord₁ {ℓ} (A : Set ℓ) {relℓ} : Set (ℓ ⊔ lsuc relℓ) where
  field _<₁_ : A → A → Set relℓ
open Ord₁ ⦃...⦄

_≤₁_ : ∀ {ℓ}{A : Set ℓ} {relℓ} ⦃ _ : Ord₁ A {relℓ} ⦄ → (A → A → Set _)
x ≤₁ y = (x <₁ y) ⊎ (x ≡ y)

postulate
  _ : ∀ {ℓ}{A : Set ℓ} {relℓ} ⦃ _ : Ord₁ A {relℓ} ⦄ {x y z : A}
    → x <₁ y → y <₁ z → x <₁ z

module _ {ℓ}{A : Set ℓ} {relℓ} ⦃ _ : Ord₁ A {relℓ} ⦄ where
  postulate _ : ∀ {x y z : A} → x <₁ y → y <₁ z → x <₁ z

instance
  i₁ : Ord₁ Bool
  i₁ ._<₁_ = λ where
    true  true  → ⊥
    true  false → ⊥
    false true  → ⊤
    false false → ⊥

  m₁ : ∀ {ℓ}{A : Set ℓ} → ⦃ Ord₁ A ⦄ → Ord₁ (Maybe A)
  m₁ ._<₁_ = λ where
    (just x) (just y) → x <₁ y
    (just _) nothing  → ⊥
    nothing  (just _) → ⊤
    nothing  nothing  → ⊥

-- #2. relℓ as a field + bump level to ω
record Ord₂ {ℓ} (A : Set ℓ) : Setω where
  field
    {relℓ} : Level
    _<₂_ : A → A → Set relℓ
open Ord₂ ⦃...⦄

_≤₂_ : ∀ {ℓ}{A : Set ℓ} ⦃ _ : Ord₂ A ⦄ → (A → A → Set _)
x ≤₂ y = (x <₂ y) ⊎ (x ≡ y)

postulate
  _ : ∀ {ℓ}{A : Set ℓ} ⦃ _ : Ord₂ A ⦄ {x y z : A}
    → x <₂ y → y <₂ z → x <₂ z

instance
  i₂ : Ord₂ Bool
  i₂ .relℓ = _
  i₂ ._<₂_ = λ where
    true  true  → ⊥
    true  false → ⊥
    false true  → ⊤
    false false → ⊥

  open import Level using (Lift)

  m₂ : ∀ {ℓ}{A : Set ℓ} → ⦃ Ord₂ A ⦄ → Ord₂ (Maybe A)
  m₂ .relℓ = _
  m₂ ._<₂_ = λ where
    (just x) (just y) → x <₂ y
    (just _) nothing  → Lift _ ⊥
    nothing  (just _) → Lift _ ⊤
    nothing  nothing  → Lift _ ⊥
