module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-suc)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)

open plfa.Isomorphism.≃-Reasoning

infixr 2 _×_
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
      -----
  → A
proj₁ ⟨ x , _ ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ _ , y ⟩ = y

record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to   = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from = λ{ ⟨ x , y ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to   = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

open import plfa.Isomorphism using (_⇔_)
open _⇔_
⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) × (B → A))
⇔≃× =
  record
    { to   = λ A⇔B → ⟨ to A⇔B , from A⇔B ⟩
    ; from = λ{⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A } }
    ; from∘to = λ A⇔B → refl
    ; to∘from = λ{⟨ A→B , B→A ⟩ → refl }
    }

data ⊤ : Set where
  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identity¹ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identity¹ =
  record
    { to   = λ{ ⟨ tt , x ⟩ → x }
    ; from = λ x → ⟨ tt , x ⟩
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ x → refl
    }

⊤-identity² : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identity² =
  record
    { to   = λ{ ⟨ x , tt ⟩ → x }
    ; from = λ x → ⟨ x , tt ⟩ 
    ; from∘to = λ{ ⟨ x , tt ⟩ → refl }
    ; to∘from = λ x → refl
    }

infix 1 _⊎_
data _⊎_ : Set → Set → Set where

  inj₁ : ∀ {A B : Set}
    → A
      -----
    → A ⊎ B

  inj₂ : ∀ {A B : Set}
    → B
      -----
    → A ⊎ B

open _⊎_

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B)
  → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ x) = refl

⊎-comm : ∀ {A B : Set}
  → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to   = λ{ (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
    ; from = λ{ (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
    ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ x) → refl }
    ; to∘from = λ{ (inj₁ x) → refl ; (inj₂ x) → refl}
    }

data ⊥ : Set where

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h () 

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to   = λ{ (inj₁ ()) ; (inj₂ x) → x}
    ; from = inj₂
    ; from∘to = λ{ (inj₁ ()) ; (inj₂ x) → refl}
    ; to∘from = λ y → refl
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
    { to   = λ{ (inj₁ x) → x ; (inj₂ ())}
    ; from = inj₁
    ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ ())}
    ; to∘from = λ y → refl
    }

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -----
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          | aa     | aa      = 1
...          | aa     | bb      = 2
...          | aa     | cc      = 3
...          | bb     | aa      = 4
...          | bb     | bb      = 5
...          | bb     | cc      = 6
...          | cc     | aa      = 7
...          | cc     | bb      = 8
...          | cc     | cc      = 9

-- (p ^ n) ^ m ≡ p ^ (n * m)
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to   = λ{ f ⟨ x₁ , x₂ ⟩ → f x₁ x₂ }
    ; from = λ g x₁ x₂ → g ⟨ x₁ , x₂ ⟩
    ; from∘to = λ{f → refl}
    ; to∘from = λ{g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- p ^ (n + m) ≡ (p ^ n) * (p ^ m)
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to   = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩
    ; from = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y }}
    ; from∘to = λ f → extensionality (λ{ (inj₁ x) → refl ; (inj₂ y) → refl })
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

-- (p * n) ^ m ≡ (p ^ m) * (n ^ m)
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ ((A → B) × (A → C))
→-distrib-× =
  record
    { to   = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from = λ{ ⟨ g , h ⟩ → λ{ x → ⟨ g x , h x ⟩ } }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
                 ; ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z
                 ; ⟨ inj₂ z , _ ⟩      → inj₂ z
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → (A × C) ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩ = inj₁ ⟨ x , z ⟩
⊎-weak-× ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩

{- stdlib

import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)

-}
