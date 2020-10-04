-- temporary file to interactively try out Agda stuff
module Scratch where

open import Prelude.Init

-- data X (x : ℕ) : ℕ → Set where
--   mkF : ∀ {y} → y ≤ x → X x y

data X (x : ℕ) : ℕ → Set
data X x where
  mkF : ∀ {y} → y ≤ x → X x y
