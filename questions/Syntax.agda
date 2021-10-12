module Syntax where

open import Prelude.Init


infixr -1 f-syntax
f-syntax = id
syntax f-syntax (λ x → e) = ƛ x ∶ e

_ : ℕ → ℕ
_ = ƛ n ∶ n + 5

_ : ℕ → ℕ → ℕ
_ = ƛ n ∶ ƛ m ∶ n + 5 + m

infixr -1 f²-syntax
f²-syntax = id

-- syntax f²-syntax (λ x → λ y → e) = ƛ² x ∣ y ∶ e

_ : ℕ → ℕ → ℕ
_ = ƛ n ∣ m ∶ n + 5 + m

-- see https://github.com/agda/agda/issues/394
