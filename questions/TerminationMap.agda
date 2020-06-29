------------------------------------------------------------------------
-- Limitations of termination checking.
------------------------------------------------------------------------
module TerminationMap where

open import Level
open import Function
open import Data.Empty
open import Data.Nat using (ℕ; _+_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Unary.Any
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  hiding ([_])
open import Induction
open import Induction.WellFounded

data Expr : Set where
  k : ℕ → Expr
  ∑ : List Expr → Expr

{- The following definition does not pass the termination checker, because of the use of concatMap.
nums : Expr → List ℕ
nums (k n)    = [ n ]
nums (∑ es) = concatMap nums es
-}

-- Solution I: Mutually define a function on singlular elements and one acting on lists of those elements.
module Sol₁ where
  nums  : Expr → List ℕ
  numsˡ : List Expr → List ℕ

  nums (k n)    = [ n ]
  nums (∑ es) = numsˡ es

  -- numsˡ = concatMap nums {- this again does not work, we need to manually expand the recursion of concatMap -}
  numsˡ [] = []
  numsˡ (e ∷ es) = nums e ++ numsˡ es


-- ** Solution II
module Sol₂ where
  data _≺_ : Rel Expr 0ℓ where
    L : ∀ {e es} → e ≺ ∑ (e ∷ es)
    R : ∀ {e es} → ∑ es ≺ ∑ (e ∷ es)
  postulate ≺-wf : WellFounded _≺_

  nums : Expr → List ℕ
  nums e = go _ (≺-wf e)
    where
      go : (e : Expr) → Acc _≺_ e → List ℕ
      go (k n)        _       = [ n ]
      go (∑ [])       _       = []
      go (∑ (e ∷ es)) (acc a) = go e (a _ L) ++ go (∑ es) (a _ R)

-- ** Solution III
module Sol₃ where
  _≺_ : Rel Expr 0ℓ
  e ≺ ∑ es = e ∈ es
  e ≺ k _  = ⊥

  ≺-wf : WellFounded _≺_
  ≺-wf e = acc $ go e
    where
      go : ∀ e e′ → e′ ≺ e → Acc _≺_ e′
      go (∑ .(e′ ∷ _)) e′ (here refl) = acc (go e′)
      go (∑ (_  ∷ es)) e′ (there e′≺) = go (∑ es) e′ e′≺

  nums : Expr → List ℕ
  nums e = go _ (≺-wf e)
    where
      go : (e : Expr) → Acc _≺_ e → List ℕ
      go (k n)  _       = [ n ]
      go (∑ es) (acc a) = concat $ mapWith∈ es λ {e} e∈ → go e (a _ e∈)

  {-# TERMINATING #-}
  nums+₁ : Expr → ℕ → List ℕ
  nums+₁ e m = go (e , m + 10 , ≺-wf e)
    where
      go : Σ[ e ∈ Expr ] ℕ × Acc _≺_ e → List ℕ
      go (k n  , m , _    ) = [ m + n ]
      go (∑ es , m , acc a) = concat $ mapWith∈ es λ {e} e∈ → go (e , 126 + m , a _ e∈)

  {-# TERMINATING #-}
  nums+₂ : Expr → ℕ → List ℕ
  nums+₂ e m = go e (m + 10 , ≺-wf e)
    where
      go : (e : Expr) → ℕ × Acc _≺_ e → List ℕ
      go (k n ) (m , _    ) = [ m + n ]
      go (∑ es) (m , acc a) = concat $ mapWith∈ es λ {e} e∈ → go e (126 + m , a _ e∈)

  nums+₃ : Expr → ℕ → List ℕ
  nums+₃ e m = go e (m + 10) (≺-wf e)
    where
      go : (e : Expr) → ℕ → Acc _≺_ e → List ℕ
      go (k n ) m _       = [ m + n ]
      go (∑ es) m (acc a) = concat $ mapWith∈ es λ {e} e∈ → go e (126 + m) (a _ e∈)
