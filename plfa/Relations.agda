module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_;_∸_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Data.List using (List; []; _∷_) 
open import Function using (id; _∘_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}

        --------
      → zero ≤ n

  s≤s : ∀ {m n : ℕ}

      → m ≤ n
        -------------
      → suc m ≤ suc n
  
infix 4 _≤_

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)


≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl


≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)


≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  backward :
      n ≤ m
      ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n       = forward z≤n
≤-total (suc m) zero    = backward z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward  m≤n = forward  (s≤s m≤n)
...                        | backward n≤m = backward (s≤s n≤m)

+-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
    -------------
  → m + p ≤ m + q
+-monoʳ-≤ zero    p q p≤q = p≤q
+-monoʳ-≤ (suc m) p q p≤q = s≤s (+-monoʳ-≤ m p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n
  rewrite +-comm m p
        | +-comm n p
        = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → p ≤ q
  → m ≤ n
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q p≤q m≤n = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s       (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data _>_ (n m : ℕ) : Set where
  from< :
      m < n
      -----
    → n > m

data Trichotomy (m n : ℕ) : Set where

  le :
      m < n
      ----------------
    → Trichotomy m n

  eq :
      m ≡ n
      ----------------
    → Trichotomy m n

  gr :
      m > n
      ----------------
    → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = eq refl
<-trichotomy zero (suc n) = le z<s
<-trichotomy (suc m) zero = gr (from< z<s)
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                             | le m<n         = le (s<s m<n)
...                             | eq m≡n         = eq (cong suc m≡n)
...                             | gr (from< n<m) = gr (from< (s<s n<m))

≤-iff-<ˡ : ∀ (m n : ℕ)
  → suc m ≤ n
    ---------
  → m < n
≤-iff-<ˡ zero    .(suc _) (s≤s m≤n) = z<s
≤-iff-<ˡ (suc m) .(suc _) (s≤s m≤n) = s<s (≤-iff-<ˡ m _ m≤n)

≤-iff-<ʳ : ∀ (m n : ℕ)
  → m < n
    ---------
  → suc m ≤ n
≤-iff-<ʳ m zero ()
≤-iff-<ʳ .0       (suc n) z<s       = s≤s z≤n
≤-iff-<ʳ .(suc _) (suc n) (s<s m<n) = s≤s (≤-iff-<ʳ _ n m<n)


data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero :
    ---------
    even zero

  suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
  
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    ------------
  → odd (m + n)

e+e≡e zero     en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

{- stdlib

import Data.Nat using (_≤_; z≤n; s≤s)
import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                  +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)

-}
