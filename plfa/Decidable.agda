module plfa.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contraposition)
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; foldr; map)
open import Data.Bool using (Bool; true; false)
open import Function using (_∘_)
open import plfa.Relations using (_<_; z<s; s<s; _≤_; z≤n; s≤s)
open import plfa.Isomorphism using (_⇔_)

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))


infix 4 _≤ᵇ_
_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ n     = true
suc m ≤ᵇ zero  = false
suc m ≤ᵇ suc n = m ≤ᵇ n

_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎

T : Bool → Set
T true  = ⊤
T false = ⊥

T→≡ : ∀ {b : Bool} → T b → b ≡ true
T→≡ {false} ()
T→≡ {true}  tt = refl

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero    n       tt = z≤n
≤ᵇ→≤ (suc m) zero    ()
≤ᵇ→≤ (suc m) (suc n) t  = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n       = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                  = yes z≤n
suc m ≤? zero               = no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n = yes (s≤s m≤n)
...               | no ¬m≤n = no (¬s≤s ¬m≤n)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

¬n<z : ∀ {m : ℕ} → ¬ (m < zero)
¬n<z ()

¬s<s : ∀ {m n : ℕ} → ¬ m < n → ¬ suc m < suc n
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n 

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero  <? zero               = no ¬n<z
zero  <? suc n              = yes z<s
suc m <? zero               = no ¬n<z
suc m <? suc n with m <? n
...               | yes m<n = yes (s<s m<n)
...               | no ¬m<n = no (¬s<s ¬m<n)

_ : 2 <? 1 ≡ no (¬s<s ¬n<z)
_ = refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no (λ ())
suc m ≡ℕ? zero = no (λ ())
suc m ≡ℕ? suc n with m ≡ℕ? n
...                | yes m≡n = yes (cong suc m≡n)
...                | no  m≢n = no (λ sm≡sn → m≢n (suc-injective sm≡sn))

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p

⌞_⌟ : ∀ {A : Set} → Dec A → Bool
⌞ yes _ ⌟ = true
⌞ no  _ ⌟ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n = ⌞ m ≤? n ⌟

toWitness : ∀ {A : Set} {D : Dec A} → T ⌞ D ⌟ → A
toWitness {_} {yes x} tt = x
toWitness {_} {no _}  ()  

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌞ D ⌟
fromWitness {_} {yes x} _ = tt
fromWitness {_} {no ¬x} x = ¬x x

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤ = toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′ = fromWitness

infixr 6 _∧_
_∧_ : Bool → Bool → Bool
false ∧ _     = false
true  ∧ false = false
true  ∧ true  = true

infixr 6 _×-dec_
_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , _ ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ _ , y ⟩ → ¬y y }

infixr 5 _∨_
_∨_ : Bool → Bool → Bool
true  ∨ _     = true
_     ∨ true  = true
false ∨ false = false

infixr 5 _⊎-dec_
_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x

_⊃_ : Bool → Bool → Bool
_     ⊃ true  = true
false ⊃ _     = true
true  ⊃ false = false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y = yes (λ _ → y)
no ¬x →-dec _     = yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y = no (λ f → ¬y (f x))

_iff_ : Bool → Bool → Bool
false iff false = true
false iff true  = false
true  iff false = false
true  iff true  = true

open _⇔_
_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes x ⇔-dec yes y = yes (record { to = λ _ → y ; from = λ _ → x })
yes x ⇔-dec no ¬y = no (λ z → ¬y (to z x))
no ¬x ⇔-dec yes y = no (λ z → ¬x (from z y))
no ¬x ⇔-dec no ¬y = yes (record { to = λ x → ⊥-elim (¬x x) ; from = λ y → ⊥-elim (¬y y) })

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B)
      → ⌞ x ⌟ iff ⌞ y ⌟ ≡ ⌞ x ⇔-dec y ⌟ 
iff-⇔ (yes x) (yes y) = refl
iff-⇔ (yes x) (no ¬y) = refl
iff-⇔ (no ¬x) (yes y) = refl
iff-⇔ (no ¬x) (no ¬y) = refl

{- stdlib

import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
import Data.Nat.Base using (_≤?_)
import Data.List.All using (All; []; _∷_) renaming (all to All?)
import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)

-}
