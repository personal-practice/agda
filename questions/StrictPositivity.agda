module StrictPositivity where

open import Prelude.Init

private
  variable
    x y n m : ℕ

{-
Consider the case, where you have a 'fallback' constructor that assumes no other constructor applies.
Then, the resulting datatype will become non-strictly-positive
(due to the negative occurence under the negation binder).
-}

module Simple where

  {-# NO_POSITIVITY_CHECK #-}
  data _~_ : Rel ℕ 0ℓ where

    [refl] :
      n ~ n

    [fallback] :
        (∀ n′ m′ → n′ ≢ n → m′ ≢ m → ¬ (n′ ~ m′))
      → n ~ m

  -- ** SOLUTION: stratify datatype in two layers to separate [fallback] from other cases
  data _~₁_ : Rel ℕ 0ℓ where
    [refl] :
      n ~₁ n

  data _~₂_ : Rel ℕ 0ℓ where
    [fallback] :
        (∀ n′ m′ → n′ ≢ n → m′ ≢ m → ¬ (n′ ~₁ m′))
      → n ~₂ m

  data _~′_ : Rel ℕ 0ℓ where
    [1] : n ~₁ m → n ~′ m

    [2] : n ~₂ m → n ~′ m

module Complicated where

  data _~_ : Rel ℕ 0ℓ
  data _~₂_ : Rel ℕ 0ℓ
  data _~₁_ : Rel ℕ 0ℓ
  data _~₁₁_ : Rel ℕ 0ℓ
  data _~₁₂_ : Rel ℕ 0ℓ

  -- ** Definitions.
  data _~₁_ where
    [L] : x ~₁₁ y
        → x ~₁ y

    [R] : x ~₁₂ y
        → x ~₁ y

  data _~₁₁_ where

    [18] : x ~₁₁ y

  data _~₁₂_ where

    [16] :
        (∀ y′ → y′ ≢ y → ¬ (x ~₁₁ y′))
        ----------------------------------------------------------------------------------
      → x ~₁₂ y

  data _~₂_ where

    [1] :
      x ~₂ y

    [3] :
        (∀ y → ¬ (x ~₁ y))
        ---------------
      → x ~₂ y

  data _~_ where

    base : x ~ y

    step₁ : x ~ y
          → x ~₁ y
            -------------
          → suc x ~ suc y

    step₂ : x ~ y
          → x ~₂ y
            -------------
          → suc x ~ suc y
