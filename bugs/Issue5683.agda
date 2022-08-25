open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

postulate X : Set
variable x : X

data C : Σ X (λ x → x ≡ x) → Set where
  _ :
    let
      eq : x ≡ x
      eq = refl {x = x}
    in
    C (x , eq)

-- nested generalization example
{-
postulate
  X : Set
  ∀≡ : ∀ {x y : X} → x ≡ y

variable x y : X

data C⁻ : (∀ {x : X} → x ≡ x) → Set where
  _ :
    let
      eq : y ≡ y
      eq = ∀≡
    in
    C⁻ eq

data C⁺ : X → (∀ {x : X} → x ≡ x) → Set where
  _ :
    let
      eq : y ≡ y
      eq = ∀≡
    in
    C⁺ x eq
-}
