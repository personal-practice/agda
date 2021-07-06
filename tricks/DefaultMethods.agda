-- {-# OPTIONS --rewriting #-}
{-# OPTIONS --no-auto-inline #-}
module DefaultMethods where

-- open import Prelude.Init
--   hiding (_<_; _>_)
-- open Meta
open import Agda.Builtin.Bool
open import Data.Bool using (T; not)
open import Agda.Builtin.Equality
open import Data.Maybe.Base
open import Data.Nat using (ℕ)
open import Function

open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

{-
is-default : {A : Set} {x : A} → Maybe (x ≡ x)
is-default = just refl

try-default : Term → TC ⊤
try-default hole =
  catchTC (unify hole (def (quote is-default) []))
          (unify hole (con (quote nothing) []))

record Ord (A : Set) : Set where
  field
    _<_ : A → A → Bool
    _>_ : A → A → Bool

record OrdDefaults (A : Set) : Set where
  field
    overlap ⦃ super ⦄ : Ord A
  open Ord super

  default_<_ : A → A → Bool
  default x < y = y > x

  default_>_ : A → A → Bool
  default x > y = y < x

  field
    @(tactic try-default) isDefault< : Maybe (_<_ ≡ default_<_)
    @(tactic try-default) isDefault> : Maybe (_>_ ≡ default_>_)

  {-# INLINE default_<_ #-}
  {-# INLINE default_>_ #-}


open Ord ⦃ ... ⦄ public
open OrdDefaults ⦃ ... ⦄ public

private variable A : Set

instance
  Ord→ : ⦃ _ : Ord A ⦄ → OrdDefaults A
  Ord→ = record {}

  OrdBool : Ord Bool
  OrdBool .Ord._<_ false false = false
  OrdBool .Ord._<_ false true  = true
  OrdBool .Ord._<_ true  false = false
  OrdBool .Ord._<_ true  true  = false
  OrdBool .Ord._>_ = default_>_
-}

{-
-- * 2. using postulate DEFAULT + rewrite rules (Jesper?)

private
  variable
    A : Set ℓ
    x y : A

postulate DEFAULT : String → A

record Ord (A : Set) : Set where
  field
    _<_ : A → A → Bool
    _>_ : A → A → Bool

  DEFAULT_<_ = flip _>_
  DEFAULT_>_ = flip _<_
  {-# INLINE .... #-}

  -- DEF_<_ : ⦃ _ : Ord A ⦄ → DEFAULT {A = A → A → Bool} "_<_" ≡ DEFAULT_<_
  postulate
    DEF_>_ : DEFAULT {A = A → A → Bool} "_>_" x y ≡ DEFAULT_>_ x y
open Ord ⦃ ... ⦄ public
{-# REWRITE DEF_>_ #-}


instance
  OrdBool : Ord Bool
  OrdBool ._<_ = λ where
    false false → false
    false true → true
    true false → false
    true true → false
  OrdBool .Ord._>_ = DEFAULT "_>_"

-}

-- {-
-- * 1. using minimal records
record Ord (A : Set) : Set where
  field
    _<_ : A → A → Bool
    _>_ : A → A → Bool

    showList : ....

record OrdMinimal₁ (A : Set) : Set where
  field
    _<_ : A → A → Bool

  _>_ : A → A → Bool
  _>_ = flip _<_

record OrdMinimal₂ (A : Set) : Set where
  field
    _>_ : A → A → Bool

  _<_ : A → A → Bool
  _<_ = flip _>_

private variable A : Set

open Ord ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Ord class OrdMinimal₁ OrdMinimal₂ #-}
-- CHECKS
--   1. in case of overlapping, make sure they are syntactically equal
       --> covers check for distinct minimal schemes, e.g. cannot have the exact same derivation
       --> easier to check after compiling to Haskell
--   2. [OPTIONAL] check all record signatures match (or simply leave to GHC)

--   3. Never inline inside minimal records

{-
-- instance (need overlapping instances)
ord₁ : ⦃ _ : OrdMinimal₁ A ⦄ → Ord A
ord₁ ⦃ r ⦄ = record {OrdMinimal₁ r}

ord₂ : ⦃ _ : OrdMinimal₂ A ⦄ → Ord A
ord₂ ⦃ r ⦄ = record {OrdMinimal₂ r}

OrdBool₁ : OrdMinimal₁ Bool
OrdBool₁ = λ where
  .OrdMinimal₁._<_ false false → false
  .OrdMinimal₁._<_ false true  → true
  .OrdMinimal₁._<_ true  false → false
  .OrdMinimal₁._<_ true  true  → false
-}

ord₁ : OrdMinimal₁ A → Ord A
ord₁ r = record {OrdMinimal₁ r}

ord₂ : OrdMinimal₂ A → Ord A
ord₂ r = record {OrdMinimal₂ r}

instance
  OrdBool₁ : Ord Bool
  OrdBool₁ = ord₁ λ where
    .OrdMinimal₁._<_ false false → false
    .OrdMinimal₁._<_ false true  → true
    .OrdMinimal₁._<_ true  false → false
    .OrdMinimal₁._<_ true  true  → false

  -- OrdBool₂ : Ord Bool
  -- OrdBool₂ = ord₂ λ where
  --   .OrdMinimal₂._>_ false false → false
  --   .OrdMinimal₂._>_ false true  → false
  --   .OrdMinimal₂._>_ true  false → true
  --   .OrdMinimal₂._>_ true  true  → false

  Ordℕ′ : Ord ℕ
  Ordℕ′ ._<_ = {!!}
  Ordℕ′ ._>_ = {!!}

  Ordℕ : Ord ℕ
  Ordℕ = record {OrdMinimal₁ Ordℕ₁}
  --   ~ record {_<_ = Ordℕ₁._<_; _>_ = Ordℕ₁._>_}
  --   ~ OrdN ._<_ = OrdN1._<_       ~> compile N1._<_ (primitive)
  --     OrdN ._>_ = OrdN1._>_       ~> drop N1._>_ (derived)
  --   ~ record {_<_ = Ordℕ₁._<_; _>_ = λ ....}
  --   ~ OrdN ._<_ = OrdN1._<_       ~> compile N1._<_ (primitive)
  --     OrdN ._>_ = λ ....          ~> compile λ .... (not even related to N1)
    where
      Ordℕ₁ : OrdMinimal₁ ℕ
      Ordℕ₁ .OrdMinimal₁._<_ = Data.Nat._<ᵇ_
{-# COMPILE AGDA2HS Ordℕ #-}
-- -}

private
  _ : T (false < true)
  _ = tt

  _ : T (true > false)
  _ = tt
