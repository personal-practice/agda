module TerminationLast where

open import Data.Empty
open import Data.List
open import Data.List.NonEmpty hiding (last)

last⁺ : ∀ {A : Set} → List⁺ A → A
-- last⁺ (x ∷ [])       = x
-- last⁺ (_ ∷ (x ∷ xs)) = last⁺ (x ∷ xs)
last⁺ (x ∷ xs)
  with xs
... | []       = x
... | x′ ∷ xs′
  with xs′
... | [] = x′
... | x″ ∷ xs″ = last⁺ (x″ ∷ xs″)
