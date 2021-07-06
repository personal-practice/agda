module Superclasses where

open import Prelude.Init

-- 1) using `overlap {{super}}`
module 𝟙 where

  record Eq (A : Set) : Set₁ where
    field _≈_ : Rel₀ A
  open Eq ⦃ ... ⦄

  record DecEq (A : Set) : Set₁ where
    field
      overlap ⦃ super ⦄ : Eq A
      _≈?_ : Decidable² _≈_
  open DecEq ⦃ ... ⦄

  instance
    _ : Eq ℕ
    _ = λ where ._≈_ → _≡_

    _ : DecEq ℕ
    _ = λ where .super → it; ._≈?_ → Nat._≟_

  _ : True $ 15 ≈? (6 + 9)
  _ = tt

-- 2) using parametrised records
module 𝟚 where

  record Eq (A : Set) : Set₁ where
    field _≈_ : Rel₀ A
  open Eq ⦃ ... ⦄

  record DecEq (A : Set) ⦃ _ : Eq A ⦄ : Set₁ where
    field _≈?_ : Decidable² _≈_
  open DecEq ⦃ ... ⦄

  instance
    _ : Eq ℕ
    _ = λ where ._≈_ → _≡_

    _ : DecEq ℕ
    _ = λ where ._≈?_ → Nat._≟_

  _ : True $ 15 ≈? (6 + 9)
  _ = tt

-- 3. using a single record (pre-supposes a Decidable class)
module 𝟛 where
  open import Prelude.Decidable

  record Eq (A : Set) : Set₁ where
    field _≈_ : Rel₀ A

    _≈?_ : ⦃ _≈_ ⁇² ⦄ → Decidable² _≈_
    _≈?_ = dec²
  open Eq ⦃ ... ⦄

  instance
    _ : Eq ℕ
    _ = λ where ._≈_ → _≡_

  open import Prelude.DecEq -- includes instance for (_≡_ {A = ℕ} ⁇²)
    -- _ : _≈_ ⁇²
    -- _ =

  _ : True $ 15 ≈? (6 + 9)
  _ = tt

-- 4. using a single record + separate (anonymous) module for decidable fragment
module 𝟜 where
  record Eq (A : Set) : Set₁ where
    field _≈_ : Rel₀ A
  open Eq ⦃ ... ⦄

  open import Prelude.Decidable
  module _ {A} ⦃ _ : Eq A ⦄ ⦃ _ : _≈_ ⁇² ⦄ where
    _≉_ : Rel₀ A
    x ≉ y = ¬ x ≈ y

    _≈?_ : Decidable² _≈_
    _≈?_ = dec²

    _≉?_ : Decidable² _≉_
    _≉?_ = dec²

  instance
    _ : Eq ℕ
    _ = λ where ._≈_ → _≡_

  open import Prelude.DecEq -- includes instance for (_≡_ {A = ℕ} ⁇²)
    -- _ : _≈_ ⁇²
    -- _ =

  _ : True $ 15 ≈? (6 + 9)
  _ = tt

-- 5. using a single record with inner (anonymous) module for decidable fragment
module 𝟝 where
  open import Prelude.Decidable

  record Eq (A : Set) : Set₁ where
    field _≈_ : Rel₀ A

    module _ ⦃ _ : _≈_ ⁇² ⦄ where
      _≉_ : Rel₀ A
      x ≉ y = ¬ x ≈ y

      _≈?_ : Decidable² _≈_
      _≈?_ = dec²

      _≉?_ : Decidable² _≉_
      _≉?_ = dec²
  open Eq ⦃ ... ⦄

  instance
    _ : Eq ℕ
    _ = λ where ._≈_ → _≡_

  open import Prelude.DecEq -- includes instance for (_≡_ {A = ℕ} ⁇²)
    -- _ : _≈_ ⁇²
    -- _ =

  _ : True $ 15 ≈? (6 + 9)
  _ = tt
