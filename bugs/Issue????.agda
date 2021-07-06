module Issue???? where

open import Prelude.Init

open import Prelude.Collections
open import Prelude.Setoid
open import Prelude.Membership

private variable A B X Z Z′ : Set

-- _has_ = _has_
-- inst : ⦃ A has B ⦄
--   → (∀ {X} → ⦃ X has B ⦄ → X → B)
--   → (A → B)
-- inst f x = f x

_⟨_on_⟩_ : ⦃ A has Z ⦄ → ⦃ B has Z ⦄
  → A
  → Rel₀ Z′
  → (∀ {X} → ⦃ X has Z ⦄ → X → Z′) → B → Set
a ⟨ _~_ on f ⟩ b = f a ~ f b

Name = ℕ ⊎ String

postulate
  𝔸 𝔹 : Set

  instance
    Sa : ISetoid 𝔸
    Sb : ISetoid 𝔹
    Ia : 𝔸 has Name
    Ib : 𝔹 has Name

names : ⦃ X has Name ⦄ → X → List Name
names = collect

namesʳ : ⦃ X has Name ⦄ → X → List String
namesʳ = mapMaybe isInj₂ ∘ names

-- name𝔸 : 𝔸 → Maybe String
-- name𝔸 = {!inst {A = 𝔸} (λ{ ⦃ I ⦄ x → nameʳ ⦃ I ⦄ x })!}

liftʳ : ∀ {a : 𝔸} {b : 𝔹}
  → a ⟨ _≡_ on namesʳ ⟩ b
  → ⊤
liftʳ = const tt

-- _⟨_on_⟩ᶜ_ : ∀ {X : Set} → Cfg → Rel₀ (List X) → (Cfg → List X) → Cfg → Set
-- Γ ⟨ _~_ on f ⟩ᶜ Γ′ = f Γ ~ f Γ′

postulate
  ≈⇒names↭ : ∀ {a a′ : 𝔸} → a ≈ a′ → a ⟨ _↭_ on names ⟩ a′
  ≈⇒namesʳ↭ : ∀ {a a′ : 𝔸} → a ≈ a′ → a ⟨ _↭_ on namesʳ ⟩ a′

∈-resp-≈ : ∀ {A : Set} → ⦃ _ : A has Z ⦄ → ⦃ _ : ISetoid A ⦄
  → (f : ∀ {X} → ⦃ X has Z ⦄ → X → List Z′)
  → (∀ {a a′ : A} → a ≈ a′ → a ⟨ _↭_ on f ⟩ a′)
  → ∀ (z : Z′) → (λ ◆ → z ∈ f ◆) Respects _≈_
∈-resp-≈ _ ≈⇒↭ x = L.Perm.∈-resp-↭ ∘ ≈⇒↭

∈names-resp-≈  = ∈-resp-≈ names  ≈⇒names↭
∈namesʳ-resp-≈ = ∈-resp-≈ namesʳ ≈⇒namesʳ↭

-- module SimplyTypedApplication where
--   _$$_ : ∀ {A : Set ℓ} {B : Set ℓ′}
--     → (A → B) → A → B
--   f $$ x = f x

--   postulate
--     f : ℕ → String
--     x : ℕ

--   _ = String has f x

-- module ApplyingSetωFunctions where
--   record Class (A : Set ℓ) : Set (lsuc ℓ) where
--     field give : A
--   open Class ⦃...⦄

--   _ : Set₁
--   _ = ∀ {A : Set} → ⦃ Class A ⦄ → A

--   open import Agda.Primitive using (Setω)

--   _ : Setω
--   _ = ∀ {ℓ} {A : Set ℓ} → ⦃ Class A ⦄ → A

--   _$$_ : ∀ {A : Setω} {B : Set ℓ}
--     → (A → B) → A → B
--   f $$ x = f x

--   record ℂ : Setω where
--     constructor ℂ[_,_,_]
--     field
--       lvl : Level
--       ty  : Set lvl
--       wit : ty
--       ⦃ cls ⦄ : Class ty
--   open ℂ
--   -- ℂ = ∃ λ ℓ → Σ (Set ℓ) λ A → Class A

--   instance
--     Cℕ : Class ℕ
--     Cℕ .give = 0

--     C⊤ : Class ⊤
--     C⊤ .give = tt

--   _ : ℂ
--   _ = ℂ[ 0ℓ , ℕ , 0 ]

--   postulate
--     f : (𝕔 : ℂ) → String
--     -- f : (∀ {ℓ} {X : Set ℓ} → ⦃ Class X ⦄ → X) → String
--     x : ℕ
--     y : ⊤

--   _ : Set₁
--   _ = ∀ {A : Set} → ⦃ Class A ⦄ → A

--   _ : String
-- -- _ = _$$_ {A = ∀ {ℓ} {X : Set ℓ} → ⦃ Class X ⦄ → X}
-- --          {B = String}
-- --          f
-- --          {!y!}
-- --          -- ((∀ {ℓ} {X : Set ℓ} → ⦃ Class X ⦄ → X → String) has f) y
--   _ = _$$_ {A = ℂ}
--           {B = String}
--           f
--           ℂ[ 0ℓ , ℕ , x ]
