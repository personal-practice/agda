module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)
open import plfa.Relations using (_<_; z<s; s<s)

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

¬-intro : ∀ {A : Set}
  → A
    -------
  → ¬ ¬ A
¬-intro x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A 
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 2 ≢ 4
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

-- 0 ^ n ≡ 1, if n ≡ 0
--       ≡ 0, if n ≢ 0
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation {A} ¬x _ = extensionality (λ x → ⊥-elim (¬x x))

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s n<n) = <-irreflexive n<n

data Tri (A B C : Set) : Set where
  tri< : A     → (¬ B) → (¬ C) → Tri A B C
  tri≡ : (¬ A) → B     → (¬ C) → Tri A B C
  tri> : (¬ A) → (¬ B) → C     → Tri A B C

trichotomy : ∀ (m n : ℕ) → Tri (m < n) (m ≡ n) (n < m)
trichotomy zero zero = tri≡ (λ ()) refl (λ ())
trichotomy zero (suc n) = tri< z<s (λ ()) (λ ())
trichotomy (suc m) zero = tri> (λ ()) (λ ()) z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | tri< a  ¬b ¬c = tri< (s<s a) (λ{ refl → ¬b refl }) λ{ (s<s x) → ¬c x }
... | tri≡ ¬a b  ¬c = tri≡ (λ{ (s<s x) → ¬a x }) (cong suc b) λ{ (s<s x) → ¬c x }
... | tri> ¬a ¬b c  = tri> (λ{ (s<s x) → ¬a x }) (λ{ refl → ¬b refl }) (s<s c)

⊎-dual-× : ∀ {A B : Set} → (¬ (A ⊎ B)) ≃ (¬ A) × (¬ B)
⊎-dual-× {A} {B} = →-distrib-⊎ {A} {B} {⊥}
  where
    -- imported from plfa.Connectives
    →-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
    →-distrib-⊎ =
      record
        { to   = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩
        ; from = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y }}
        ; from∘to = λ f → extensionality (λ{ (inj₁ x) → refl ; (inj₂ y) → refl })
        ; to∘from = λ{ ⟨ g , h ⟩ → refl }
        }

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable ¬P = ¬P (inj₂ λ z → ¬P (inj₁ z))

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set}
    ------------
  → Stable (¬ A)
¬-stable = λ ¬¬¬x x → ¬¬¬x (¬-intro x)

×-stable : ∀ {A B : Set}
  → Stable A
  → Stable B
    --------------
  → Stable (A × B)
×-stable sa sb = λ ¬¬x → ⟨ sa (λ ¬x → ¬x (sa (λ z → ¬¬x (λ z₁ → z (proj₁ z₁)))))
                         , sb (λ ¬y → ¬y (sb (λ z → ¬¬x (λ z₂ → z (proj₂ z₂)))))
                         ⟩

{- stdlib

import Relation.Nullary using (¬_)
import Relation.Nullary.Negation using (contraposition)

-}
