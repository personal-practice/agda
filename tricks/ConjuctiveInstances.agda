open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.Decidable

-- ** motivation
record X (A : Type) : Type where
  field x : A
open X ⦃...⦄
record Y (A : Type) : Type where
  field y : A
open Y ⦃...⦄

private variable A B C : Type

module _ ⦃ _ : X A ⦄ ⦃ _ : Y B ⦄ where
  _ : A × B
  _ = x , y

-- ** non-dependent basic setup
infixr -100 _·⊗·_
record _·⊗·_ (A B : Type) : Type where
  field ⦃ ↜ ⦄ : A; ⦃ ↝ ⦄ : B
instance
  mk·⊗· : ⦃ A ⦄ → ⦃ B ⦄ → A ·⊗· B
  mk·⊗· = record {}
open _·⊗·_ ⦃...⦄ hiding (↜; ↝)

module _ ⦃ _ : X A ·⊗· Y B ⦄ where
  _ : A × B
  _ = x , y
module _ ⦃ _ : X A ⦄ ⦃ _ : Y A ⦄ where
  _ : X A ·⊗· Y A
  _ = it

-- ** n-ary
record Z (A : Type) : Type where
  field z : A
open Z ⦃...⦄

module _ ⦃ _ : X A ·⊗· Y B ·⊗· Z C ⦄ where
  _ : A × B × C
  _ = x , y , z
module _ ⦃ _ : X A ⦄ ⦃ _ : Y A ⦄ ⦃ _ : Z A ⦄ where
  _ : X A ·⊗· Y A ·⊗· Z A
  _ = it

-- ** Typeω
private variable Aω Bω Cω : Typeω

infixr -100 _⊗ω_
record _⊗ω_ (Aω Bω : Typeω) : Typeω where
  field ⦃ ↜ ⦄ : Aω; ⦃ ↝ ⦄ : Bω
instance
  mk⊗ω : ⦃ Aω ⦄ → ⦃ Bω ⦄ → Aω ⊗ω Bω
  mk⊗ω = record {}
open _⊗ω_ ⦃...⦄ hiding (↜; ↝)

record Xω (Aω : Typeω) : Typeω where
  field xω : Aω
open Xω ⦃...⦄
record Yω (Aω : Typeω) : Typeω where
  field yω : Aω
open Yω ⦃...⦄
record Zω (Aω : Typeω) : Typeω where
  field zω : Aω
open Zω ⦃...⦄

module _ ⦃ _ : Xω Aω ⊗ω Yω Bω ⦄ where
  _ : Aω; _ = xω
  _ : Bω; _ = yω
module _ ⦃ _ : Xω Aω ⦄ ⦃ _ : Yω Aω ⦄ where
  _ : Xω Aω ⊗ω Yω Aω
  _ = itω

-- ** Type/Typeω combinations

-- data 𝕌 : Type where
--   TYPE : Level → 𝕌
--   TYPEω : 𝕌
-- El : 𝕌 → ????
-- El = λ where
--   (TYPE ℓ) → Type ℓ
--   TYPEω → Typeω

infixr -100 _·⊗ω_
record _·⊗ω_ (A : Type) (Bω : Typeω) : Typeω where
  field ⦃ ↜ ⦄ : A; ⦃ ↝ ⦄ : Bω
instance
  mk·⊗ω : ⦃ A ⦄ → ⦃ Bω ⦄ → A ·⊗ω Bω
  mk·⊗ω = record {}
open _·⊗ω_ ⦃...⦄ hiding (↜; ↝)

module _ ⦃ _ : X A ·⊗ω Yω Bω ⦄ where
  _ : A; _ = x
  _ : Bω; _ = yω
module _ ⦃ _ : X A ⦄ ⦃ _ : Yω Aω ⦄ where
  _ : X A ·⊗ω Yω Aω
  _ = itω

infixr -100 _⊗ω·_
record _⊗ω·_ (Aω : Typeω) (B : Type) : Typeω where
  field ⦃ ↜ ⦄ : Aω; ⦃ ↝ ⦄ : B
instance
  mk⊗ω· : ⦃ Aω ⦄ → ⦃ B ⦄ → Aω ⊗ω· B
  mk⊗ω· = record {}
open _⊗ω·_ ⦃...⦄ hiding (↜; ↝)

module _ ⦃ _ : Xω Aω ⊗ω· Y B ⦄ where
  _ : Aω; _ = xω
  _ : B; _ = y
module _ ⦃ _ : Xω Aω ⦄ ⦃ _ : Y A ⦄ where
  _ : Xω Aω ⊗ω· Y A
  _ = itω

infixr -100 _ω⊗ω_
record _ω⊗ω_ (Aω : Typeω) (Bω : Typeω) : Typeω where
  field ⦃ ↜ ⦄ : Aω; ⦃ ↝ ⦄ : Bω
instance
  mkω⊗ω : ⦃ Aω ⦄ → ⦃ Bω ⦄ → Aω ω⊗ω Bω
  mkω⊗ω = record {}
open _ω⊗ω_ ⦃...⦄ hiding (↜; ↝)

-- data OP : Typeω₁ where
--   ·· : (Type ℓ → Type ℓ′ → Type (ℓ ⊔ₗ ℓ′)) → OP
--   ω· : (Typeω → Type ℓ → Typeω) → OP
--   ·ω : (Type ℓ → Typeω → Typeω) → OP
--   ωω : (Typeω → Typeω → Typeω)  → OP

module _ ⦃ _ : Xω Aω ω⊗ω Yω Bω ⦄ where
  _ : Aω; _ = xω
  _ : Bω; _ = yω
module _ ⦃ _ : Xω Aω ⦄ ⦃ _ : Yω Aω ⦄ where
  _ : Xω Aω ω⊗ω Yω Aω
  _ = itω
module _ ⦃ _ : Xω Aω ⦄ ⦃ _ : Yω Aω ⦄ ⦃ _ : Zω Aω ⦄ where
  _ : Xω Aω ω⊗ω Yω Aω ω⊗ω Zω Aω
  _ = itω
module _ ⦃ _ : X A ⦄ ⦃ _ : Yω Aω ⦄ ⦃ _ : Zω Aω ⦄ where
  _ : X A ·⊗ω Yω Aω ω⊗ω Zω Aω
  _ = itω
module _ ⦃ _ : X A ⦄ ⦃ _ : Yω Aω ⦄ ⦃ _ : Z A ⦄ where
  _ : X A ·⊗ω Yω Aω ⊗ω· Z A
  _ = itω
module _ ⦃ _ : X A ⦄ ⦃ _ : Y A ⦄ ⦃ _ : Zω Aω ⦄ where
  _ : X A ·⊗ω Y A ·⊗ω Zω Aω
  _ = itω

-- pattern _⊗_ x y = _·⊗·_ x y
-- pattern _⊗_ x y = x ·⊗ω y
-- pattern _⊗_ x y = x ω⊗· y
-- pattern _⊗_ x y = ωω x y

-- ** dependent version

-- record _⊗_ (A : Typeω) (B : ⦃ A ⦄ → Typeω) : Typeω₁ where
--   constructor _,_
--   field
--     instance ⊗L : A
--   instance _ = ⊗L
--   field
--     instance ⊗R : B
-- open _⊗_ ⦃...⦄

-- -- private variable A : Typeω; B : ⦃ A ⦄ → Typeω
-- -- instance
-- --   mk⊗ : ⦃ _ : A ⦄ → ⦃ _ : B ⦄ → A ⊗ B
-- --   mk⊗ = ? -- itω , itω

-- module _ {A : Type}
--   ⦃ p : DecEq A ⦄
--   ⦃ q : ISetoid A ⊗ Setoid-Laws A ⦄
--   where

--   _ : {x y : A} → auto∶ x ≡ y → {!⊗L ⦃ q ⦄!} -- x ≈ y
--   _ = {!!} -- ≈-reflexive ∘ toWitness
