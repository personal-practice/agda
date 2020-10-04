module Recursors where

-- open import Induction
open import Prelude.Init

variable
  A : Set

-- A RecStruct describes the allowed structure of recursion.

RecStruct : Set → Set₁
RecStruct A = (A → Set) → (A → Set)

-- A recursor builder constructs an instance of a recursion structure
-- for a given input.

RecursorBuilder : RecStruct A → Set₁
RecursorBuilder Rec = ∀ P → (∀ x → Rec P x → P x) → (∀ x → Rec P x)

-- A recursor can be used to actually compute/prove something useful.

Recursor : RecStruct A → Set₁
Recursor Rec = ∀ P → (∀ x → Rec P x → P x) → (∀ x → P x)

-- And recursors can be constructed from recursor builders.

build : ∀ {Rec : RecStruct A} → RecursorBuilder Rec → Recursor Rec
build builder P f x = f x (builder P f x)

module SimpleRecursion-ℕ where

  Rec : RecStruct ℕ
   -- ≈ (ℕ → Set) → (ℕ → Set)
  Rec P zero    = ⊤
  Rec P (suc n) = P n

  recBuilder : RecursorBuilder Rec
          -- ≈ ∀ P → (∀ x → Rec P x → P x) → (∀ x → Rec P x)
  recBuilder P f zero    = tt
  recBuilder P f (suc n) = f n (recBuilder P f n)

  rec : Recursor Rec
   -- ≈ ∀ P → (∀ x → Rec P x → P x) → (∀ x → P x)
  rec = build recBuilder

  twice : ℕ → ℕ
  twice = rec (const ℕ) λ
    { zero    _   → zero
    ; (suc n) n*2 → suc $ suc n*2 }

-- We can repeat the exercise above for subsets of the type we are
-- recursing over.

SubsetRecursorBuilder : (A → Set) → RecStruct A → Set₁
SubsetRecursorBuilder Q Rec = ∀ P → (∀ x → Rec P x → P x) → (∀ x → Q x → Rec P x)

SubsetRecursor : (A → Set) → RecStruct A → Set₁
SubsetRecursor Q Rec = ∀ P → (∀ x → Rec P x → P x) → (∀ x → Q x → P x)

subsetBuild : ∀ {Q : A → Set} {Rec : RecStruct A}
  → SubsetRecursorBuilder Q Rec
  → SubsetRecursor Q Rec
subsetBuild builder P f x q = f x (builder P f x q)

-- Well-founded recursion
module SOME {_<_ : A → A → Set} where

  WfRec : RecStruct A
     -- ≈ (A → Set) → (A → Set)
  WfRec P x = ∀ y → y < x → P y

  wfRecBuilder : SubsetRecursorBuilder (Acc _<_) WfRec
  wfRecBuilder P f x (acc rs) = λ y y<x →
    f y (wfRecBuilder P f y (rs y y<x))

  wfRec : SubsetRecursor (Acc _<_) WfRec
  wfRec = subsetBuild wfRecBuilder

  module ALL (wf : WellFounded _<_) where

    wfRecBuilder' : RecursorBuilder WfRec
              -- ≈ ∀ P → (∀ x → WfRec P x → P x) → (∀ x → WfRec P x)
    wfRecBuilder' P f x = wfRecBuilder P f x (wf x)

    wfRec' : Recursor WfRec
    wfRec' = build wfRecBuilder'


module WellFoundedRelation-ℕ where

  open import Data.Nat.Induction using (<-wellFounded)
  open SOME {_<_ = _<_}
  open ALL <-wellFounded

  twice : ℕ → ℕ
  twice = wfRec' (const ℕ) λ
    { zero    f → zero
    ; (suc n) f → suc $ suc $ f n (Nat.n<1+n _) }

  State  = ℕ

  st₀ : State
  st₀ = 0

  ↑ : State → State
  ↑ = suc

  ret : State → ℕ
  ret x = x

  count-suc : ℕ → ℕ
  count-suc e = (wfRec' (λ _ → State → ℕ) λ
    { zero    f st → st
    ; (suc n) f st → f n (Nat.n<1+n _) (↑ st)
    }) e st₀

  -- statefully st₀ ret rec = rec (State → R) λ
  --   {
    -- rec st₀ ↑
  --   = rec (
  --   where
  --     run :

  -- count' : ℕ → ℕ
  -- count' = (statefully 0 (λ x → x) wfRec') (const ℕ) λ
  --   { zero    f st → st
  --   ; (suc n) f st → f n (Nat.n<1+n _) (↑ st) }
