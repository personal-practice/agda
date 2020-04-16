module ListsViewTermination where

open import Data.Product using (_,_; ∃-syntax)
open import Data.Nat using (ℕ; _+_)
open import Data.List using (List; _++_)
-- open import Data.Vec using (Vec; _++_)

open import Agda.Builtin.Equality

variable
  A : Set

view : ∀ (xs : List A) → ∃[ l ] ∃[ r ] (xs ≡ l ++ r)
view = {!!}

rec : List A → ℕ
rec xs with view xs
... | l , r , refl
    = rec l -- + rec r
