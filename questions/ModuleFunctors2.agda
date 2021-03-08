module ModuleFunctors2 where

open import Prelude.Init

-- signature
record SetInterface (A : Set) (σ : Level) : Set (lsuc σ) where
  field
    S : Set σ
    ∅ : S
    _∪_ : Op₂ S
    -- _≈_ : Rel S σ

    ∅-identity : Identity ∅ _∪_
    ∪-comm : Commutative _∪_

-- list implementation
module SL (A : Set) where
  abstract
    S : Set
    S = List A

    ∅ : S
    ∅ = []

    _∪_ : Op₂ S
    s ∪ s′ = s ++ s′

    ∅-identity : Identity ∅ _∪_
    ∅-identity = L.++-identityˡ , L.++-identityʳ

    ∪-comm : Commutative _∪_
    ∪-comm = {!!}

-- function-predicate implementation
module SF (A : Set) where
  abstract
    S : Set₁
    S = A → Set

    ∅ : S
    ∅ = const ⊥

    _∪_ : Op₂ S
    (s ∪ s′) x = s x ⊎ s′ x

    ∅-identity : Identity ∅ _∪_
    ∅-identity = {!!}

    ∪-comm : Commutative _∪_
    ∪-comm = {!!}

private variable A : Set

SetsAsLists : SetInterface A 0ℓ
SetsAsLists {A = A} = record {SL A}

SetsAsFunctions : SetInterface A (lsuc 0ℓ)
SetsAsFunctions {A = A} = record {SF A}

module SL-Example where
  -- open SL ℕ
  open SetInterface (SetsAsLists {A = ℕ})

  ex : S
  ex = ∅ ∪ ∅

  ∅-identityˡ : LeftIdentity ∅ _∪_
  ∅-identityˡ = {!L.++-identityˡ!}
  -- ** this should not typecheck if we have properly abstracted away the implemention details

module SF-Example where
  -- open SF ℕ
  open SetInterface (SetsAsFunctions {A = ℕ})

  ex : S
  ex = ∅ ∪ ∅
