module Laws where

open import Prelude.Init; open SetAsType
open Alg≡

module 𝟙 where
  record Semigroup (A : Type) : Type where
    infixr 5 _◇_
    field _◇_ : A → A → A
  open Semigroup ⦃...⦄ public

  record SemigroupLaws (A : Type) ⦃ _ : Semigroup A ⦄ : Type where
    field ◇-comm   : Commutative _◇_
          ◇-assocʳ : Associative _◇_
  open SemigroupLaws ⦃...⦄ public

  instance
    _ : Semigroup ℕ
    _ = λ where ._◇_ → _+_

    _ : SemigroupLaws ℕ
    _ = λ where
      .◇-comm   → Nat.+-comm
      .◇-assocʳ → Nat.+-assoc

module 𝟚 where
  record Semigroup (A : Type) : Type where
    infixr 5 _◇_
    field _◇_ : A → A → A
  open Semigroup ⦃...⦄ public

  record SemigroupLaws (A : Type) : Type where
    field
      overlap ⦃ super ⦄ : Semigroup A
      ◇-comm   : Commutative _◇_
      ◇-assocʳ : Associative _◇_
  open SemigroupLaws ⦃...⦄ public

  instance
    _ : Semigroup ℕ
    _ = λ where ._◇_ → _+_

    _ : SemigroupLaws ℕ
    _ = λ where
      .super    → it
      .◇-comm   → Nat.+-comm
      .◇-assocʳ → Nat.+-assoc

module 𝟛 where
  record Semigroup (A : Type) : Type where
    infixr 5 _◇_
    field _◇_ : A → A → A

    record Laws : Type where
      field ◇-comm   : Commutative _◇_
            ◇-assocʳ : Associative _◇_
    open Laws ⦃...⦄ public
    syntax Laws {A = A} = Semigroup-Laws A
  open Semigroup ⦃...⦄ public

  instance
    _ : Semigroup ℕ
    _ = λ where ._◇_ → _+_

    _ : Semigroup-Laws ℕ
    _ = λ where
      .◇-comm   → Nat.+-comm
      .◇-assocʳ → Nat.+-assoc
