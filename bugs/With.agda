module With where

data Nat : Set where
  z : Nat
  s : Nat → Nat

data NonZero : Nat → Set where
  nz : ∀ {x} → NonZero (s x)

bug : NonZero (s z) → Nat
bug x@(y) with z
... | _ = z
