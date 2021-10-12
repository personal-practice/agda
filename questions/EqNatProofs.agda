{-# OPTIONS -v Generics:100 #-}
module EqNatProofs where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Nary
open import Prelude.Ord
-- open import Prelude.Membership
open L.Mem
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Show

variable xs : List ℕ

open import Prelude.Generics hiding (unifyStrict)
open Meta
open Debug ("Generics" , 100)

import Level as Lvl

pattern `0ℓ = quote Lvl.zero ∙
pattern `ℕ = quote ℕ ∙
pattern `auto = quote auto ∙
pattern `refl = quote refl ◆
pattern `it   = quote it ∙

pattern _`++_ xs ys = quote _++_ ∙⟦ xs ∣ ys ⟧
pattern `Any P xs = quote Any ∙⟦ P ∣ xs ⟧

data ViewEqℕ : Set where
  _`≡_ : Term → Term → ViewEqℕ
  ∅ : ViewEqℕ

viewEqℕ : Term → ViewEqℕ
viewEqℕ = λ where
  (def (quote _≡_) (hArg `0ℓ ∷ hArg `ℕ ∷ vArg x ∷ vArg y ∷ [])) →
    x `≡ y
  _ → ∅

unifyStrict : (Hole × Type) → Term → TC ⊤
unifyStrict (hole , ty) x = do
  m ← newMeta ty
  noConstraints $ unify m x
  unify hole m

unifyStricts : (Hole × Type) → List Term → TC ⊤
unifyStricts ht = L.NE.foldr₁ _<|>_ ∘ (L.NE._∷ʳ error "∅") ∘ fmap (unifyStrict ht)

decideEqℕ : Hole → Term × Term → TC ⊤
decideEqℕ hole (x , y) = do
  let x≡y = quote _≡_ ∙⟦ x ∣ y ⟧
  let x≟y = quote _≟_ ∙⟦ x ∣ y ⟧
  unifyStrict (hole , x≡y) $ def (quote toWitness) (hArg? ∷ hArg x≡y ∷ hArg x≟y ∷ vArg (quote tt ◆) ∷ [])
  print $ "Decided: " ◇ show x ◇ " ≡ " ◇ show y

tryEqℕ : Hole → Term × Term → TC ⊤
tryEqℕ hole (x , y) =
  if x == y then (do
    print "tryEqℕ: terms are exactly equal, applying reflexivity..."
    unifyStrict (hole , quote _≡_ ∙⟦ x ∣ y ⟧) `refl
    )
  -- else if == swap
  --   print "tryEqℕ: terms are swapped, applying commutativity..."
  --   ...
  else error "tryEqℕ: terms are not exactly equal, cannot apply reflexivity"

recEqℕ : Hole → Term × Term → TC ⊤
solveEqℕ′ : Hole → TC ⊤

errorP : String → TC ⊤
errorP s = print s >> error s

recEqℕ hole = λ where
  (con c as , con c′ as′) →
    case map₁₂ vArgs (as , as′) of λ where
      ((x ∷ []) , (y ∷ [])) →
        if c == c′ then (do
          print "recEqℕ: same constructors"
          m ← newMeta $ quote _≡_ ∙⟦ x ∣ y ⟧
          solveEqℕ′ m
          -- m′ ← instantiate m -- leads to unsolved metas
          unify hole $ quote cong ∙⟦ c ◆ ∣ m ⟧)
        else
          errorP "recEqℕ: different head constructors"
      _ → errorP "recEqℕ: cannot deal with multiple constructor arguments yet"
  (def f as , def f′ as′) →
    case map₁₂ vArgs (as , as′) of λ where
      ((x ∷ []) , (y ∷ [])) →
        if f == f′ then (do
          print "recEqℕ: same heads"
          m ← newMeta $ quote _≡_ ∙⟦ x ∣ y ⟧
          solveEqℕ′ m
          unify hole $ quote cong ∙⟦ f ∙ ∣ m ⟧)
        else
          errorP "recEqℕ: different heads"
      _ → errorP "recEqℕ: cannot deal with multiple head arguments yet"
  _ → errorP "recEqℕ: cannot peel head"

solveEqℕ′ hole = do
  ty ← normalise =<< inferType hole
  (x `≡ y) ← return (viewEqℕ ty)
    where ∅ → error "solveEqℕ: can only solve holes of type (m : ℕ) ≡ (n : ℕ)"
  print $ show x ◇ " =? " ◇ show y
  printLn " ** decideEqℕ" >> decideEqℕ hole (x , y)
    <|> printLn " ** recEqℕ" >> recEqℕ hole (x , y)
    <|> printLn " ** tryEqℕ" >> tryEqℕ hole (x , y)

macro
  solveEqℕ : Hole → TC ⊤
  solveEqℕ = solveEqℕ′

private
  variable x y : ℕ

  _ : 0 ≡ 0
  -- _ = here refl -- GREEN
  -- _ = here auto -- GREEN
  -- _ = here it -- GREEN
  -- _ = auto -- GREEN
  -- _ = there auto -- YELLOW
  -- _ = here it -- RED
  _ = solveEqℕ

  _ : x ≡ x
  _ = solveEqℕ

  _ : suc x ≡ suc x
  _ = solveEqℕ

  postulate f : ℕ → ℕ

  _ : f x ≡ f x
  _ = solveEqℕ

  _ : x + 1 ≡ x + 1
  _ = solveEqℕ

  -- _ : x + y ≡ y + x
  -- _ = solveEqℕ
