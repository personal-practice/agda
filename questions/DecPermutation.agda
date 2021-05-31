module DecPermutation where

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Decidable

private
  variable
    A : Set
    x y : A
    xs ys : List A


_↭′_ : Rel (List A) ℓ
xs ↭′ ys =


length≡ : xs ↭ ys → length xs ≡ length ys
length≡ ↭-refl         = refl
length≡ (↭-prep x p)   = cong suc (length≡ p)
length≡ (↭-swap x y p) = cong (suc ∘ suc) (length≡ p)
length≡ (↭-trans p p′) = trans (length≡ p) (length≡ p′)

single≡ : [ x ] ↭ xs → xs ≡ [ x ]
single≡ ↭-refl = refl
single≡ {xs = _ ∷ xs} (↭-prep _ p) with xs | length≡ p
... | [] | _ = refl
... | _ ∷ _ | ()
single≡ (↭-trans p p′) rewrite single≡ p | single≡ p′ = refl

_↭?_ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ (xs ys : List A) → Dec (xs ↭ ys)
xs ↭? ys
  with xs ≟ ys
... | yes refl = yes ↭-refl
... | no xs≢ys
  with xs | ys
... | [] | [] = contradict xs≢ys
... | [] | y ∷ ys′ = no $ contradict ∘ length≡
... | x ∷ xs′ | [] = no $ contradict ∘ length≡
... | x ∷ xs′ | y ∷ ys′
  with x ≟ y
... | yes refl = case xs′ ↭? ys′ of λ where
  (yes xs↭ys) → yes $ ↭-prep x xs↭ys
  (no ¬xs↭ys) → {!!}
... | no  x≢y

  with xs′ | ys′
... | [] | [] = no ((λ{ refl → xs≢ys refl }) ∘ single≡)
... | [] | y′ ∷ ys″ = no $ contradict ∘ length≡
... | x′ ∷ xs″ | [] = no $ contradict ∘ length≡
... | x′ ∷ xs″ | y′ ∷ ys″
  with (x ≟ y′) ×-dec (x′ ≟ y)
... | yes (refl , refl) = case xs″ ↭? ys″ of λ where
  (yes xs↭ys) → yes $ ↭-swap x x′ xs↭ys
  (no ¬xs↭ys) → no  $ {!!}
... | no ¬p = {!!}
