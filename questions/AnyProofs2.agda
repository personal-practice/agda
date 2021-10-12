{-# OPTIONS -v Generics:100 #-}
module AnyProofs2 where

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

open import Prelude.Generics hiding (viewTy)
open Meta
open Debug ("Generics" , 100)

private variable A B : Set ℓ

record Solver : Set₁ where
  field
    View : Set
    view : Term → Maybe View
    solve : THole → View → TC ⊤

  solveM : Hole → TC ⊤
  solveM hole = do
    ty ← normalise =<< inferType hole
    case view ty of λ where
      (just v) → solve (hole , ty) v
      nothing  → error $ "Can only solve holes of view: " ◇ show (quoteTerm View)

open Solver public

Solver-Eq Solver-Any : Solver

solveAll′ : Hole → TC ⊤
solveAll′ hole = do
  print $ "***************\nHole: " ◇ show hole ◇ "\n***************\n"
  ⋃⁺ fmap (flip solveM hole)
    ⟦ Solver-Eq
    , Solver-Any
    ⟧

macro
  solveAll : Hole → TC ⊤
  solveAll = solveAll′

-- ** _≡_ solver
data ViewEq : Set where
  _`≡_ : Term → Term → ViewEq

viewEq : Term → Maybe ViewEq
viewEq = λ where
  (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg x ∷ vArg y ∷ [])) → just (x `≡ y)
  _ → nothing

solveEq : THole → ViewEq → TC ⊤
solveEq (hole , _) (x `≡ y) = do
  print $ show x ◇ " =? " ◇ show y
  x ← normalise x
  y ← normalise y
  print $ show x ◇ " =? " ◇ show y
  decideEq hole (x , y) <|> tryEq hole (x , y)
  where
    decideEq : Hole → Term × Term → TC ⊤
    decideEq hole (x , y) = do
      let x≡y = quote _≡_ ∙⟦ x ∣ y ⟧
      let x≟y = quote _≟_ ∙⟦ x ∣ y ⟧
      unifyStrict (hole , x≡y) $ def (quote toWitness) (hArg? ∷ hArg x≡y ∷ hArg x≟y ∷ vArg (quote tt ◆) ∷ [])
      print $ "Decided: " ◇ show x ◇ " ≡ " ◇ show y

    tryEq : Hole → Term × Term → TC ⊤
    tryEq hole (x , y) =
      if x == y then (do
        print "tryEq: terms are exactly equal, applying reflexivity..."
        unifyStrict (hole , quote _≡_ ∙⟦ x ∣ y ⟧) (quote refl ◆)
        )
      -- else if == swap
      --   print "tryEq: terms are swapped, applying commutativity..."
      --   ...
      else error "tryEq: terms are not exactly equal, cannot apply reflexivity"

Solver-Eq = λ where
  .View → ViewEq
  .view → viewEq
  .solve → solveEq

private
  _ : 5 ≡ 5
  _ = solveAll -- solveM Solver-Eq

  _ : 5 ≡ 1 + 1 + 0 + 2 + 0 + 1
  _ = solveAll -- solveM Solver-Eq

  _ : ∀ {x : ℕ} → x ≡ x
  _ = solveAll

  _ : ∀ {x} → suc x ≡ suc x
  _ = solveAll

-- ** Any solver
data ViewAny : Set where
  Any⦅_⦆ : Term × Term → ViewAny

viewAny : Term → Maybe ViewAny
viewAny = λ where
  (def (quote Any) as) → case vArgs as of λ where
    (P ∷ xs ∷ []) → just Any⦅ P , xs ⦆
    _ → nothing
  _ → nothing

data ViewList : Set where
  ∷⦅_,_⦆ : Term → Term → ViewList
  ++⦅_,_⦆ : Term → Term → ViewList

viewList : Term → Maybe ViewList
viewList = λ where
  (con (quote L._∷_) args) →
    case vArgs args of λ where
      (x ∷ xs ∷ []) → just ∷⦅ x , xs ⦆
      _ → nothing
  (def (quote _++_) args) →
    case vArgs args of λ where
      (xs ∷ ys ∷ []) → just ++⦅ xs , ys ⦆
      _ → nothing
  _ → nothing

solveAs : Type → TC Hole
solveAs ty = do
  hole′ ← newMeta ty
  solveAll′ hole′
  return hole′

{-# TERMINATING #-}
solveAny : THole → ViewAny → TC ⊤
solveAny thole@(hole , ty) Any⦅ P , xs ⦆ = do
  printLn ">ANY"
  xs ← normalise xs
  case viewList xs of λ where
    nothing → error $ "Not recognized: " ◇ show xs
    (just c) → case c of λ where
      ∷⦅ y , ys ⦆ → do
        printLn $ "Recognized: Any " ◇ show P ◇ " " ◇ show y ◇ " ∷ " ◇ show ys
        (do
          hole′ ← solveAs =<< P -∙- y
          unifyStrict thole $ quote Any.here ◆⟦ hole′ ⟧
          ) <|> (do
          hole′ ← solveAs $ quote Any ∙⟦ P ∣ ys ⟧
          unifyStrict thole $ quote Any.there ◆⟦ hole′ ⟧
          )
      ++⦅ ys , zs ⦆ → do
        printLn $ "Recognized: Any " ◇ show P ◇ " " ◇ show ys ◇ " ++ " ◇ show zs
        (do
          hole′ ← solveAs $ quote Any ∙⟦ P ∣ ys ⟧
          unifyStrict thole $ quote L.Any.++⁺ˡ ∙⟦ hole′ ⟧
          ) <|> (do
          hole′ ← solveAs $ quote Any ∙⟦ P ∣ zs ⟧
          unifyStrict thole $ quote L.Any.++⁺ʳ ∙⟦ ys ∣ hole′ ⟧
          )

Solver-Any = λ where
  .View → ViewAny
  .view → viewAny
  .solve → solveAny

private
  variable xs ys : List ℕ

  _ : Any (_≡ 0) (0 ∷ [])
  _ = solveAll

  _ : Any (_≡ 0) [ 0 ]
  _ = solveAll

  _ : Any (_≡ 0) ⟦ 0 ⟧
  _ = solveAll

  _ : Any (_≡ 0) (1 ∷ 0 ∷ [])
  _ = solveAll

  _ : Any (_≡ 0) (2 ∷ 1 ∷ 0 ∷ [])
  _ = solveAll

  _ : Any (_≡ 0) (0 ∷ xs)
  _ = solveAll

  _ : Any (_≡ 0) ((0 ∷ []) ++ xs)
  _ = solveAll

  _ : Any (_≡ 0) (xs ++ (0 ∷ []))
  _ = solveAll

  _ : Any (_≡ 0) (xs ++ ys ++ (0 ∷ []))
  _ = solveAll

  _ : Any (_≡ 0) (xs ++ ys ++ (1 ∷ 125 ∷ 0 ∷ []))
  _ = solveAll

  _ : 0 ∈ (0 ∷ 1 ∷ xs)
  _ = solveAll

  _ : 0 ∈ xs ++ (0 ∷ 1 ∷ xs)
  _ = solveAll

  open import Prelude.Membership using () renaming (_∈_ to _∈′_)

  _ : 0 ∈′ xs ++ (0 ∷ 1 ∷ xs)
  _ = solveAll

{- ** DOESNT WORK
-}
record Solvable (A : Set ℓ) : Set₁ where
  field solver : Solver
  -- private open Solver solver

  macro
    SolveM : Hole → TC ⊤
    SolveM hole = do
      ty ← normalise =<< inferType hole
      case solver .view ty of λ where
        (just v) → solver .solve (hole , ty) v
        nothing  → error $ "Can only solve holes of view: " ◇ show (quoteTerm (solver .View))
open Solvable ⦃...⦄ public

instance
  Solvable-Any : ∀ {a}{A : Set a} {xs : List A} {p}{P : A → Set p} → Solvable (Any P xs)
  Solvable-Any .solver = Solver-Any

macro
  goal : Hole → TC ⊤
  goal hole = do
    ctx ← getContext
    printS ctx
    ty ← inferType hole
    unify hole ty
    -- >>= unify hole

  -- explicate : (Hole → TC ⊤) → Hole → TC ⊤
  -- explicate macro hole = do

  --   ty ← inferType hole
  --   a ← fresh-level
  --   A ← unquoteTC {A = Set a} ty
  --   SolveM {A = A} hole
    -- ← SolveM hole
    -- unify hole $ def (quote SolveM) (hArg? ∷ hArg ty ∷ vArg hole ∷ [])

_ : Any (_≡ 0) (0 ∷ [])
_ = SolveM {A = Any (_≡ 0) (0 ∷ [])}

_ : Any (_≡ 0) (0 ∷ [])
_ = {!!} goal
  where
    TY = Any (_≡ 0) (0 ∷ [])
