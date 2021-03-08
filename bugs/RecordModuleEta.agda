module RecordModuleEta where

open import Prelude.Init

record X : Set₁ where
  field
    Set' : Set
    _♯_ : Rel₀ Set'
    ♯-sym : ∀ {x} y → x ♯ y → y ♯ x

module Y where
  record Set' : Set where
    field
      x : ℕ
      .pr : x > 0
  open Set'

  _♯_ : Rel₀ Set'
  _♯_ = _≡_ on x
  -- _♯_ = _≡_

  postulate
    ♯-sym : ∀ {x} y → x ♯ y → y ♯ x

test : X
test = record {Y}
