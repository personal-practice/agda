open import Agda.Builtin.Bool     using (Bool; true)
open import Agda.Builtin.Sigma    using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)

Bool² : Set
Bool² = Σ Bool (λ _ → Bool)

data F : Bool² → Set where
  mk : ∀ {a b} → F (a , b)

variable
  x : Bool²
  X : F x

postulate
  f : ∀ {A B : Set} → (A → B) → Bool

fail : let _ = f (λ { _ → _ , _ }) in X ≡ mk
fail = {!!}
