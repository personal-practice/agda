module NatViewTermination where

open import Function using (_$_)

open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.List using (List; []; _∷_; map; sum)

open import Agda.Builtin.Equality

-- *** Termination checking failed...
-- rec : ℕ → ℕ
-- rec 0       = 0
-- rec (suc n) = sum $ map rec (n ∷ n ∷ [])

-- *** Termination checking failed...
-- rec′ : ∀ {y : ℕ} → ∃[ x ] (x ≡ y) → ℕ
-- rec′ (0     , _) = 0
-- rec′ (suc n , _) = sum $ map (rec′ {y = n}) ((n , refl) ∷ (n , refl) ∷ [])

-- PASSES!
rec″ : ∀ {y : ℕ} → ∃[ x ] (x ≡ y) → ℕ
rec″ {y = .0}     (0     , refl) = 0
rec″ {y = .suc n} (suc n , refl) = sum $ map (rec″ {y = n}) ((n , refl) ∷ (n , refl) ∷ [])
