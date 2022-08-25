-- temporary file to interactively try out Agda stuff
module REPL where

open import Prelude.Init
-- open import Prelude.Lists
-- open import Prelude.DecLists
-- open import Prelude.DecEq
-- open import Prelude.Decidable

{-
open import IO

main : Main
main = run (putStrLn "hello")
-}

{-
data _⊆_ : Rel List where
  [] :
    ───────
    [] ⊆ []

  keep :
    xs ⊆ ys
    ────────────────
    x ∷ xs ⊆ x ∷ ys

  drop :
    xs ⊆ ys
    ────────────────
    xs ⊆ x ∷ ys


  OPE: [x,y,z,k,l]
        0 1 0 0 1 : Vec Bool

A:  [ x  ,  y    ,  z ]
      qr            k

B:       [q   ,r,   k   ,l]
B:       [q   ,r,   k   ∅]
          x    x    z    -
        x ∈ A  0    2    ∅
          0

ys ⊆ xs = y ∈ ys → x ∈ xs

y ∈ ys → Maybe (x ∈ xs)

attackes <?> blockers

  Σ λ bs → bs ⊑ blockers
         × bs ⊆ attackers

  Σ (_⊑ blockers /\ _⊆ attackers)
-}

-- data X : Set where
--   ◇ ◆ : X

-- data IsBlack : X → Set where
--   instance mk : IsBlack ◆

-- data IsWhite : X → Set where
--   instance mk : IsWhite ◇

-- -- it : ∀ {A : Set} → {{ _ : A }} → A
-- -- it ⦃ x ⦄ = x

-- -- _ : IsBlack ◆
-- -- _ = it

-- -- ** pattern abstraction!!
-- -- data R : Set where

-- --   RULE :
-- --     ∀ (x@(k , v) : ℕ × ℕ)
-- --     → k ≡ 0
-- --     → v ≡ 0
-- --     → R
