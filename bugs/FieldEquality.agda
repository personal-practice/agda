open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

record X : Set where
  field nm : ℕ × ℕ
open X public

variable x : X

_ : x .nm .proj₂ ≡ proj₂ (nm x)
_ = refl
