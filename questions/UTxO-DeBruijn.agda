module UTxO-DeBruijn where

open import Data.Product using (proj₂; ∃-syntax)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; #_)
open import Data.List using (List; []; _∷_; [_]; map)

open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

open import Prelude.Lists

record Node (n : ℕ) : Set where
  constructor _∶-_
  field
    refs  : List (Fin n)
    .uniq : Unique refs
open Node public

data DAG : ℕ → Set where
  ∙ :
    ------
    DAG 0

  _⊕_ : ∀ {n : ℕ}
    → DAG n
    → Node n
      -----------
    → DAG (suc n)


infix 6 _∶-_
infixl 5 _⊕_

_ : DAG 2
_ = ∙
  ⊕ [] ∶- []
  ⊕ [ # 0 ] ∶- ([] ∷ []) -- ([ # 0 ] ∶- ?)
