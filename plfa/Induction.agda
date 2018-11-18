module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_;_∸_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5 
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p    = sym refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p                           = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero    = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-identityʳ' : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ' zero                           = refl
+-identityʳ' (suc m) rewrite +-identityʳ' m = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n    = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ∎

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero    rewrite +-identityʳ m          = refl
+-comm' m (suc n) rewrite +-suc m n | +-comm m n = refl

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite cong (m +_) (+-comm n p)
                   | sym (+-assoc m p n)
                   | +-comm n (m + p)
                   = refl

*-identityʳ : ∀ (m : ℕ) → m * 0 ≡ 0
*-identityʳ zero    = refl
*-identityʳ (suc m) = *-identityʳ m

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m * n + m
*-suc zero n = refl
*-suc (suc m) n
  rewrite *-suc m n
        | +-suc (n + m * n) m
        | +-assoc n (m * n) m
        = refl 

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-identityʳ n = refl
*-comm (suc m) n 
  rewrite *-comm m n
        | *-suc n m
        | +-comm n (n * m)
        = refl

+-distrib-* : ∀ (m n p : ℕ) → (m + n) * p ≡ (m * p) + (n * p)
+-distrib-* m n zero
  rewrite *-identityʳ (m + n)
        | *-identityʳ m
        | *-identityʳ n
        = refl
+-distrib-* m n (suc p)
  rewrite *-suc (m + n) p
        | +-distrib-* m n p
        | *-suc m p
        | *-suc n p
        | +-assoc (m * p) (n * p) (m + n)
        | sym (+-assoc (n * p) m n)
        | +-comm (n * p) m
        | +-assoc m (n * p) n
        | sym (+-assoc (m * p) m (n * p + n))
        = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p
  rewrite +-distrib-* n (m * n) p
        | *-assoc m n p
        = refl

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
