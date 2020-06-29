module NaryListNotation where

open import Level renaming (suc to lsuc)
open import Function
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.Vec
open import Data.Nat using (ℕ; suc)

private
  variable
    n : ℕ
    A : Set
    F : Set → ℕ → Set

_^_ : Set → ℕ → Set
A ^ 0     = A
A ^ suc n = A × (A ^ n)

{-
record ListLike (F : Set → Set) : Set₁ where
  field
    nil  : F A
    cons : A → F A → F A
open ListLike {{...}} public

instance
  LL-List : ListLike List
  LL-List = record {nil = []; cons = _∷_}


⟦_⟧ : ∀ {n} {{_ : ListLike F}} → A ^ n → F A
⟦_⟧ {n = 0}     x        = cons x nil
⟦_⟧ {n = suc n} (x , xs) = cons x ⟦ xs ⟧

_ : List ⊤
_ = ⟦ tt , tt , tt , tt , tt , tt ⟧

_ : ∃ (Vec ⊤)
_ = ⟦ tt , tt , tt , tt , tt , tt ⟧

_ : Vec ⊤ 6
_ = proj₂ ⟦ tt , tt , tt , tt , tt , tt ⟧

-}

record ListLike (F : Set → ℕ → Set) : Set₁ where
  constructor mkLL
  field
    `[]  : F A 0
    _`∷_ : ∀ {n} → A → F A n → F A (suc n)

  ⟦_⟧ : A ^ n → F A (suc n)
  ⟦_⟧ {n = 0}     x        = x `∷ `[]
  ⟦_⟧ {n = suc n} (x , xs) = x `∷ ⟦ xs ⟧
open ListLike {{...}} public

instance
  LL-List : ListLike (const ∘ List)
  LL-List = mkLL [] _∷_

  LL-Vec : ListLike Vec
  LL-Vec = mkLL [] _∷_

  LL-Vec∃ : ListLike (const ∘ ∃ ∘ Vec)
  LL-Vec∃ = mkLL (0 , []) λ{ x (_ , xs) → _ , x ∷ xs }


_ : List ⊤
_ = ⟦ tt , tt , tt , tt , tt , tt ⟧

_ : Vec ⊤ 6
_ = ⟦ tt , tt , tt , tt , tt , tt ⟧

_ : ∃ (Vec ⊤)
_ = ⟦ tt , tt , tt , tt , tt , tt ⟧
