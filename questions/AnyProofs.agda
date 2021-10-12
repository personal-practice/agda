{-# OPTIONS -v Generics:100 #-}
module AnyProofs where

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

TTerm = Term × Type
THole = Hole × Type

record Solver (A : Set ℓ) : Set₁ where
  field
    View : Set
    view : Term → Maybe View
    solve : THole → View → TC ⊤

  syntax view {A = A} = view⟨ A ⟩
-- syntax solve {A = A} = solve⟨ A ⟩

  macro
    solveM : Hole → TC ⊤
    solveM hole = do
      ty ← inferType hole
      case view ty of λ where
        (just v) → solve (hole , ty) v
        nothing  → error $ "Can only solve holes of type: " ◇ show (quoteTerm A)
open Solver ⦃...⦄ public

mkSolveTerm : Type → Term
mkSolveTerm ty = def (quote solveM) ⟦ hArg? , hArg ty ⟧

solveAs : THole → TC ⊤
solveAs (hole , ty) = do
  print ("Solving " ◇ show hole ◇ " as " ◇ show ty)
  noConstraints $ unify hole (mkSolveTerm ty)

pattern _`,_ x y = quote _,_ ◆⟦ x ∣ y ⟧

-- data 𝕌 : Set where

macro
  solveAll : Hole → TC ⊤
  solveAll hole = do
    print $ "***************\nHole: " ◇ show hole ◇ "\n***************\n"
    ty ← inferType hole
    printS ty
    ty ← normalise ty
    print " ↝ " >> printS ty
    unify hole $ case view ty of λ where
      (ANY v) → solveM {A =


    -- A ← unquoteTC {A = Set} ty
    -- unify hole $ quoteTerm (solveM {A = A})
    -- A ← unquoteTC ty
    -- case view {A = A} ty of λ where
    --   (just v) → solve (hole , ty) v
    --   nothing  → error $ "Can only solve holes of type: " ◇ show (quoteTerm A)
    -- unify hole $ quote solve ∙⟦ hole `, ty ⟧
    -- unify hole $ def (quote solveM) ⟦ hArg? , hArg ty ⟧
      -- unifyStrict (hole , ty) $ def (quote solveM) ⟦ hArg? , hArg ty ⟧
      -- solveAs =<< (hole ,_) <$> inferType hole

-- ** EQ solver

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

instance
  Solver-Eq : ∀ {x y : A} → Solver (x ≡ y)
  Solver-Eq = λ where
    .View → ViewEq
    .view → viewEq
    .solve → solveEq

private
  -- _ : 5 ≡ 5
  -- _ = solveM {A = 5 ≡ 5}

  _ : 5 ≡ 5
  _ = solveAll

  _ : 5 ≡ 1 + 1 + 0 + 2 + 0 + 1
  _ = solveAll

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
          printS P
          printS y
          ty′ ← P -∙- y
          printS ty′
          -- unifyStrict thole $ quote Any.here ◆⟦ mkSolveTerm ty′ ⟧
          hole′ ← newMeta ty′
          solveAs (hole′ , ty′)
          unifyStrict thole $ quote Any.here ◆⟦ hole′ ⟧
          ) <|> (do
          let ty′ = quote Any ∙⟦ P ∣ ys ⟧
          -- unifyStrict thole $ quote Any.there ◆⟦ mkSolveTerm ty′ ⟧
          hole′ ← newMeta ty′
          solveAny (hole′ , ty′) Any⦅ P , ys ⦆
          unifyStrict thole $ quote Any.there ◆⟦ hole′ ⟧
          )
      ++⦅ ys , zs ⦆ → do
        printLn $ "Recognized: Any " ◇ show P ◇ " " ◇ show ys ◇ " ++ " ◇ show zs
        (do
          let ty′ = quote Any ∙⟦ P ∣ ys ⟧
          unifyStrict thole $ quote L.Any.++⁺ˡ ∙⟦ mkSolveTerm ty′ ⟧
          ) <|> (do
          let ty′ = quote Any ∙⟦ P ∣ zs ⟧
          -- hole′ ← newMeta ty′
          -- solveAny hole′ Any⦅ P , zs ⦆
          unifyStrict thole $ quote L.Any.++⁺ʳ ∙⟦ ys ∣ mkSolveTerm ty′ ⟧
          )

instance
  Solver-Any : ∀ {A : Set ℓ} {xs : List A} {P : Pred A ℓ′} → Solver (Any P xs)
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


{-
-- ** General solver (dispatches to sub-solvers)

data ViewTy : Set where
  ANY EQ LIST ∅ : ViewTy

viewTy : Type → ViewTy
viewTy ty =
  case viewAny ty of λ where
    ∅ → case viewEq ty of λ where
          ∅ → case viewList ty of λ where
                ∅ → ∅
                _ → LIST
          _ → EQ
    _ → ANY

macro
  solve : Hole → TC ⊤
  solve hole@(meta holeM _) = do
    print $ "***************\nHole: " ◇ show hole ◇ "\n***************\n"
    ty ← normalise hole >>= (inferType >=> normalise)
    solve′ (hole , ty)
    {-
    printTerm "hole" hole
    hole′ ← instantiate hole
    printTerm "hole′" hole′
    solve′ (hole , ty) <|> solve′ (hole′ , ty)
    -}
  solve _ = error "hole is not a meta"

solve′ : Hole × Type → TC ⊤
solve′ ht@(hole , ty) = case viewTy ty of λ where
  ANY → solveAny′ ht
  EQ  → solveEq′ hole
  _   → error "can only solve ANY or EQ propositions"

-}
