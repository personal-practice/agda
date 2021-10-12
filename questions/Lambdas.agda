{-# OPTIONS -v tc.pos:95 #-}
-- {-# OPTIONS -v profile:2 #-}
module Lambdas where

open import Prelude.Init

_ : ℕ → ℕ
_ = λ y → y

r : ℕ → ℕ
r = λ y → y

module Y (n : ℕ) where

  _ : ℕ → ℕ
  _ = λ y → y + n

  m : ℕ → ℕ
  m = λ y → y + n


-- _ : ∀ {y : ℕ} → ℕ
-- _ = λ{ {y} → y }

-- _ : ∀ {{y : ℕ}} → ℕ
-- _ = λ {{y}} → y
