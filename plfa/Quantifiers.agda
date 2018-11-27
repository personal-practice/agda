module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    ---------------------
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to      = λ P → ⟨ (λ x → proj₁ (P x)) , (λ x → proj₂ (P x)) ⟩
    ; from    = λ Q x → ⟨ (proj₁ Q x) , (proj₂ Q x) ⟩
    ; from∘to = λ P → refl
    ; to∘from = λ Q → refl
    }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj1′ : A
    proj2′ : B proj1′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , Bx ⟩ = f x Bx

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      = λ{ f ⟨ x , Bx ⟩ → f x Bx }
    ; from    = λ g x Bx → g ⟨ x , Bx ⟩
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality (λ{ ⟨ x , Bx ⟩ → refl }) 
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to      = λ{ ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩
                 ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩
                 }
    ; from    = λ{ (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩
                 ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩
                 }
    ; from∘to = λ{ ⟨ x , inj₁ Bx ⟩ → refl
                 ; ⟨ x , inj₂ Cx ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , Bx ⟩) → refl
                 ; (inj₂ ⟨ x , Cx ⟩) → refl
                 }
    }

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- forwards
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                      = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

-- backwards
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero  , refl ⟩ = even-zero
∃-even ⟨ suc x , refl ⟩ = even-suc (∃-odd ⟨ x , refl ⟩)

∃-odd  ⟨ m     , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ (∀ x → ¬ B x)
¬∃≃∀¬ =
  record
    { to      = λ f x Bx → f ⟨ x , Bx ⟩
    ; from    = λ{ g ⟨ x , Bx ⟩ → g x Bx }
    ; from∘to = λ f → extensionality (λ{ ⟨ x , Bx ⟩ → refl })
    ; to∘from = λ g → refl
    }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x) 
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ f = ¬Bx (f x)

{- stdlib

import Data.Product using (Σ, _,_; ∃; Σ-syntax; ∃-syntax)

-}
