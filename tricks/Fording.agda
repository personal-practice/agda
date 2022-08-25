{-# OPTIONS -v ford:100 #-}
open import Prelude.Init
open Meta
open import Prelude.Generics
open Debug ("ford" , 100)

{- ** automatically ford a given type signature

    e.g. ∀ {xs ys P} → xs ↦ P → ys ↦ P → xs ++ ys ↦ P
       ↝ ∀ {xs ys P} {zs} {zs≡ : zs ≡ xs ++ ys} → xs ↦ P → ys ↦ P → zs ↦ P

    + also derive the corresponding term from the original

    t : Ford (∀ {xs ys P} → xs ↦ P → ys ↦ P → xs ++ ys ↦ P)
    t {zs≡ = refl} = t₀
-}

fordify : Type → Type
fordify ty
  with argTys , retTy ← viewTy ty
  = tyView (concatMap goArg argTys ++ goRet retTy, retTy)
  where
    goArg : Abs (Arg Type) → List (Abs $ Arg Type)
    goArg = ?

    go : Type → List (Abs $ Arg Type)
    go = ?

 -- λ where
 --  (con c as) → {!!}
 --  (def s as) → {!!}
 --  (lam v (abs s a)) → {!!}
 --  (pat-lam cs as) → {!!}
 --  (pi (arg i a) (abs s P)) → {!!}
 --  _ → {!!}
 --  where
 --    trivial

 --    goArgs : Args Term →


macro
  Ford : Term → Hole → TC ⊤
  Ford t hole = unify hole (fordify t)

  -- FordOnlySlime : Term → Hole → TC ⊤
  -- FordOnlySlime t hole = unify hole (fordifyOnlySlime t)


private
  _ = Ford (ℕ → ℕ × Bool)
    ≡ (ℕ → ℕ × Bool)
    ∋ refl

  _ = Ford ((x : ℕ) → (y : ℕ) → x ≡ y)
    ≡ ((x : ℕ) → (y : ℕ) → x ≡ y)
    ∋ refl

  _ = Ford ((x y : ℕ) → x ≡ x + y)
    ≡ (∀ (x y : ℕ) {z} {z≡ : z ≡ x + y} → x ≡ z)
    ∋ refl
