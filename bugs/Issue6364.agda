open import Agda.Primitive using (Level; _⊔_) renaming (Set to Type)
open import Agda.Builtin.Equality

private variable ℓ ℓ′ : Level

it : ∀ {A : Type ℓ} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

record Semigroup (A : Type ℓ) : Type ℓ where
  field _◇_ : A → A → A
open Semigroup ⦃...⦄

record Semigroup-Laws (A : Type ℓ) ⦃ _ : Semigroup A ⦄ : Type ℓ where
  field ◇-assoc : ∀ {x y z : A} → (x ◇ y) ◇ z ≡ x ◇ (y ◇ z)
open Semigroup-Laws ⦃...⦄

record _⊗_ (A : Type ℓ) (B : ⦃ A ⦄ → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  field ⦃ ↜ ⦄ : A
        ⦃ ↝ ⦄ : B
open _⊗_ ⦃...⦄
instance
  mk⊗ : ∀ {A : Type ℓ} {B : Type ℓ′} → ⦃ A ⦄ → ⦃ B ⦄ → A ⊗ B
  mk⊗ = record {}

Lawful-Semigroup : Type ℓ → Type ℓ
Lawful-Semigroup A = Semigroup A ⊗ Semigroup-Laws A

module _ {A : Type} ⦃ s : Semigroup A ⦄ ⦃ l : Semigroup-Laws A ⦄ where

  -- ** all of these work
  ✓ : Semigroup A ⊗ Semigroup-Laws A
  ✓ = it -- mk⊗ -- mk⊗ ⦃ s ⦄ ⦃ l ⦄

  -- ** the two types involved are definitionally equal :S
  _ : Lawful-Semigroup A ≡ (Semigroup A ⊗ Semigroup-Laws A)
  _ = refl

  -- ** none of these work
  ✖ : Lawful-Semigroup A
  -- ✖ = it
{-
No instance of type Lawful-Semigroup A was found in scope.
when checking that the expression it has type Lawful-Semigroup A
-}
  -- ✖ = mk⊗
{-
Cannot instantiate the metavariable _85 to solution
Semigroup-Laws A since it contains the variable x
which is not in scope of the metavariable
when checking that the expression mk⊗ has type Lawful-Semigroup A
-}
  -- ✖ = mk⊗ ⦃ s ⦄ ⦃ l ⦄
{-
s != x of type Semigroup A
when checking that the expression mk⊗ ⦃ s ⦄ ⦃ l ⦄ has type
Lawful-Semigroup A
-}
  ✖ = {!!}
--- Goal type in the above context context:
-- ∙ [C-,]         Lawful-Semigroup A
-- ∙ [C-u C-u C-,] Semigroup A ⊗ Semigroup-Laws A

  -- ** this suprisingly works!
  ✓✓ : Lawful-Semigroup A
  ✓✓ = record {}
