module ModuleMixfixIdentifiers where

open import Prelude.Init
open import Prelude.Ord

module M[_] (A : Set) where
  A×A = A × A

-- open M[ ℕ ]
open M[_] ℕ

_ : A×A
_ = 6 , 66

{- ** opening records (not really needed)
record _↔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
ℕ↔ℤ : ℕ ↔ ℤ
ℕ↔ℤ = let open _↔_ in λ where
  .to   → Integer.+_
  .from → Integer.∣_∣

module _ where

  open _↔_ ℕ↔ℤ

  _ : 5 ≡ from (Integer.+ 5)
  _ = refl
-}


module _⋯_ (low high : ℕ) where
  len   = high ∸ low
  start = low
  end   = high

open _⋯_ 5 10
-- open 5 ⋯ 10

_ : (len ≡ 5) × (start ≡ 5) × (end ≡ 10)
_ = refl , refl , refl
