module ModuleFunctorsI where

open import Prelude.Init

-- signature
record SetInterface (A : Set) (σ : Level) : Set (lsuc σ) where
  infixr 4 _∪_
  field
    S : Set σ
    ∅ : S
    singleton : A → S
    _∪_ : Op₂ S
    -- _≈_ : Rel S σ

    ∅-identity : Identity ∅ _∪_
    ∪-comm : Commutative _∪_

open SetInterface ⦃ ... ⦄ public
