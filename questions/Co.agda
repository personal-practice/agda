module Co where

open import Prelude.Init

record Stream (A : Set) : Set where
  coinductive
  constructor _∷∞_
  field
    hd : A
    tl : Stream A

open Stream public

variable
  A : Set
  α : A
  σ : Stream A

P∞ : Set → Set₁
P∞ A = Pred (Stream A) 0ℓ

record _≈_ (xs ys : Stream A) : Set where
  coinductive
  field
    hd≡ : hd xs ≡ hd ys
    tl≈ : tl xs ≈ tl ys

data ◇ (X : P∞ A) : Stream A → Set where
  base : X σ → ◇ X σ
  step : ◇ X σ → ◇ X (α ∷∞ σ)

data □ (X : P∞ A) : Stream A → Set where
  mk□ : X (α ∷∞ σ) → □ X σ → □ X (α ∷∞ σ)


from : ℕ → Stream ℕ
hd (from n) = n
tl (from n) = from (suc n)

nats = from 0

□≥0 : □ ((_≥ 0) ∘ hd) nats
□≥0 = {!!}

◇≡1 : ◇ ((_≡ 1) ∘ hd) nats
◇≡1 = {!!}

-- record Tree (A : Set) : Set where
--   coinductive
--   field
