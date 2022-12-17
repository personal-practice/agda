open import Prelude.Init; open SetAsType

record HasLaws (A : Type) : Type₁ where
  field obeys : A → Type

open HasLaws ⦃...⦄

record Monoid (A : Type) : Type where
  field ε : A

  record Laws : Type where
    field ε≡ : ε ≡ ε
  open Laws public
open Monoid ⦃...⦄ hiding (Laws)

record Semigroup (A : Type) : Type where
  field _◇_ : Op₂ A

  record Laws : Type where
    field ◇-comm : Alg≡.Commutative _◇_
  open Laws public
open Semigroup ⦃...⦄ hiding (Laws)

Laws : ∀ A → ⦃ HasLaws A ⦄ → ⦃ A ⦄ → Type
Laws A = obeys it

private variable A : Type ℓ

instance
  MonoidLaws : HasLaws (Monoid A)
  MonoidLaws .obeys = Monoid.Laws

  Monoid-ℕ = Monoid ℕ ∋ λ where .ε → 0

  MonoidLaws-ℕ : Laws (Monoid ℕ)
  MonoidLaws-ℕ .ε≡ = refl

  SemigroupLaws : HasLaws (Semigroup A)
  SemigroupLaws .obeys = Semigroup.Laws

  Semigroup-ℕ = Semigroup ℕ ∋ λ where ._◇_ → _+_

  SemigroupLaws-ℕ : Laws (Semigroup ℕ)
  SemigroupLaws-ℕ .◇-comm = Nat.+-comm
