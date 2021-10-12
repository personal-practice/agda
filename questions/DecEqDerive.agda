module DecEqDerive where

open import Prelude.Init
open import Prelude.DecEq.Core


record R⁰ : Set where

-- unquoteDecl r⁰ = DERIVE DecEq [ quote R⁰ , r⁰ ]
dec-eq-R⁰ : Decidable² {_}{R⁰} _≡_

instance
  deq-R⁰ : DecEq R⁰
  deq-R⁰ = λ where ._≟_ → dec-eq-R⁰

dec-eq-R⁰ = λ r r′ → yes refl

data Fin′ : ℕ → Set where
  mk : ∀ {n} → Fin′ n → Fin′ (suc n)
-- unquoteDecl DecEq-Fin′ = DERIVE DecEq [ quote Fin′ , DecEq-Fin′ ]

dec-eq-Fin′ : ∀ {n : ℕ} → Decidable² {_}{Fin′ n} _≡_

instance
  deq-Fin′ : ∀ {n : ℕ} → DecEq (Fin′ n)
  deq-Fin′ {n} = λ where ._≟_ → dec-eq-Fin′

dec-eq-Fin′ {n} = λ where
  (mk fn) (mk fm) → case fn ≟ fm of λ where
    (no ¬p) → no λ{ refl → ¬p refl }
    (yes refl) → yes refl

data FN (n : ℕ) : Set where
  mk : Fin n → FN n
-- unquoteDecl DecEq-FN = DERIVE DecEq [ quote FN , DecEq-FN ]

dec-eq-FN : ∀ {n : ℕ} → Decidable² {_}{FN n} _≡_

instance
  deq-FN : ∀ {n : ℕ} → DecEq (FN n)
  deq-FN {n} = λ where ._≟_ → dec-eq-FN

dec-eq-FN {n} = λ where
  (mk fn) (mk fm) → case fn ≟ fm of λ where
    (no ¬p) → no λ{ refl → ¬p refl }
    (yes refl) → yes refl
