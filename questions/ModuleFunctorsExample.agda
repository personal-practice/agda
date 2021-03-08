module ModuleFunctorsExample where

open import Prelude.Init
open import ModuleFunctorsI
import ModuleFunctorsL as SL

private variable A : Set

instance
  SetsAsLists : SetInterface A 0ℓ
  SetsAsLists {A = A} = record {SL A}

-- SetsAsFunctions : SetInterface A (lsuc 0ℓ)
-- SetsAsFunctions {A = A} = record {SF A}

-- syntax SL A = SetInterface {A = A} (record {ModuleFunctorsL A})

-- open SetInterface {A = ℕ} (record {SL ℕ})

-- open Sets (SetsAsLists

module Example-ℕ where
  ex : S
  ex = singleton 5 ∪ ∅ ∪ singleton 10

  ∅-identityˡ : (∅ ∪ singleton 10) ≡ singleton 10
  ∅-identityˡ = {!L.++-identityˡ!}
  -- ** this should not typecheck if we have properly abstracted away the implemention details

module Example-String where
  ex : S
  ex = singleton "one" ∪ ∅ ∪ singleton "two"

  ∅-identityˡ : (∅ ∪ singleton "sth") ≡ singleton "sth"
  ∅-identityˡ = {!L.++-identityˡ!}
  -- ** this should not typecheck if we have properly abstracted away the implemention details
