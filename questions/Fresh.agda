open import Prelude.Init
open import Prelude.Membership
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Nary

record FreshIn (As A : Set) : Set₁ where
  field _∌_ : As → A → Set
open FreshIn ⦃...⦄ public

private variable
  A As Bs : Set
  n : ℕ

instance
  FI-same : FreshIn A A
  FI-same ._∌_ y x = x ≢ y

  -- FI-List : FreshIn (List A) A
  -- FI-List ._∌_ xs x = x ∉ xs

  FI-List : ⦃ FreshIn As A ⦄ → FreshIn (List As) A
  FI-List ._∌_ xs x = All (_∌ x) xs

  -- FI-Vec : FreshIn (Vec A n) A
  -- FI-Vec ._∌_ xs x = x ∉ xs

  FI-Vec : ⦃ FreshIn As A ⦄ → FreshIn (Vec As n) A
  FI-Vec ._∌_ xs x = V.All.All (_∌ x) xs

  FI-× : ⦃ FreshIn As A ⦄ → ⦃ FreshIn Bs A ⦄ → FreshIn (As × Bs) A
  FI-× ._∌_ (xs , ys) x = (xs ∌ x) × (ys ∌ x)

private
  _ : (1 , 2 , 3 , [ 4 ] , [ [ 10 ] ] , (List ℕ ∋ ⟦ 1 , 1 , 2 , 2 , 3 , 3 , 4 , 4 ⟧)) ∌ 5
  _ = auto

  -- _ : [ [ 1 ] ] ∌ [ 2 ]
  -- _ = auto
