------------------------------------------------------------------------
-- Limitations of termination checking.
------------------------------------------------------------------------
module TerminationMap where

open import Data.Nat  using (ℕ)
open import Data.List using (List; []; [_]; _∷_; map; concatMap; _++_)

data Expr : Set where
  k   : ℕ → Expr
  sum : List Expr → Expr

{- The following definition does not pass the termination checker, because of the use of concatMap.
nums : Expr → List ℕ
nums (k n)    = [ n ]
nums (sum es) = concatMap nums es
-}

-- Solution: Mutually define a function on singlular elements and one acting on lists of those elements.
nums  : Expr → List ℕ
numsˡ : List Expr → List ℕ

nums (k n)    = [ n ]
nums (sum es) = numsˡ es

-- numsˡ = concatMap nums {- this again does not work, we need to manually expand the recursion of concatMap -}
numsˡ [] = []
numsˡ (e ∷ es) = nums e ++ numsˡ es
