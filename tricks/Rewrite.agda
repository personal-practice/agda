{-# OPTIONS -v rewrite:100 #-}

open import Prelude.Init
open Meta
open import Prelude.Generics
open Debug ("rewrite" , 100)

open import Prelude.DecEq

open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Monad
open import Prelude.Semigroup
open import Prelude.Show

-- {-# TERMINATING #-}
getFocus : (ℕ → Bool) → Term → Term → Term
getFocus apply⁇ x = proj₂ ∘ go 0 0
  where
    go : ℕ → ℕ → Term → Bool × Term
    go k n t =
      if (x == t) then
        true , (if apply⁇ k then (var n []) else x)
      else case t of λ where
        (con c as) → map₂ (con c) (goArgs k as)
        (def s as) → let b , as′ = goArgs k as
                     in b , def s as′
        (lam v (abs s a)) →
          let b , a′ = go k (suc n) a
          in b , lam v (abs s a′)
        -- (pat-lam cs as) → pat-lam (map goCl cs) (map goArg as)
        (pi (arg i a) (abs s P)) →
          let b , a′  = go k n a
              k′      = if b then suc k else k
              b′ , P′ = go k′ (suc n) P
          in (b ∨ b′) , pi (arg i a′) (abs s P′)
        _ → false , t
      where
        goArgs : ℕ → Args Term → Bool × Args Term
        goArgs _ []       = false , []
        goArgs k (arg i a ∷ as) =
          let b , a′   = go k n a
              k′       = if b then suc k else k
              b′ , as′ = goArgs k′ as
          in b ∨ b′ , arg i a′ ∷ as′

          -- goPat  = λ where
          --   (con c ps) → con c (map (fmap goPat) ps)
          --   (dot t) → dot (go n t)
          --   (var x) → var x
          --   var    : (x : Nat)     → Pattern
          --   lit    : (l : Literal) → Pattern
          --   proj   : (f : Name)    → Pattern
          --   absurd : (x : Nat)     → Pattern
          --   p → p

          -- goClause = λ where
          --   (clause tel ps t) → clause (map (map₂ goArg) tel) (map goPat ps) (go (n + length tel) t)
          --   (absurd-clause tel ps) → absurd-clause (map (map₂ goArg) tel) (map goPat ps)


viewEq : Term → TC (Term × Term)
viewEq eq = do
  (def (quote _≡_) (_ ∷ _ ∷ vArg x ∷ vArg y ∷ [])) ← inferType eq
    where _ → error "Can only write with equalities `x ≡ y`."
  return (x , y)

∗ : ℕ → Bool
∗ = const true

macro
  by_rw_⟪_⟫ : Term → Term → (ℕ → Bool) → Hole → TC ⊤
  (by t rw eq ⟪ apply⁇ ⟫) hole = do
    ty ← inferType hole
    x , y ← viewEq eq
    unify hole $ quote subst ∙⟦ (`λ "◆" ⇒ getFocus apply⁇ x ty) ∣ quote sym ∙⟦ eq ⟧ ∣ t ⟧

  rw_at_⟪_⟫ : Term → Term → (ℕ → Bool) → Hole → TC ⊤
  (rw eq at t ⟪ apply⁇ ⟫) hole = do
    ty ← inferType t
    x , y ← viewEq eq
    unify hole $ quote subst ∙⟦ (`λ "◆" ⇒ getFocus apply⁇ x ty) ∣ eq ∣ t ⟧

private
  postulate
    X : Set
    a b : X
    eq : a ≡ b

    P : Pred₀ X
    Pa : P a

    P² : Rel₀ X
    P²a : P² a a

  Pb : P b
  -- Pb = subst (λ x → P x) eq Pa
  Pb = rw eq at Pa ⟪ ∗ ⟫

  P²b : P² b b
  -- P²b = subst (λ x → P² x x) eq P²a
  P²b = rw eq at P²a ⟪ ∗ ⟫

  private
    postulate f : P a ≡ P b → X → X

    go : a ≡ b → X → X
    -- go a≡b = f $ subst (λ x → P x ≡ P b) (sym a≡b) refl
    -- go a≡b = f $ by (P b ≡ P b) ∋ refl rw a≡b ⟪ ∗ ⟫
    go a≡b = f $ rw a≡b at ((P a ≡ P a) ∋ refl) ⟪ _== 1 ⟫
    -- go a≡b = f Pa≡Pb
    --   where
    --   Pa≡Pb : P a ≡ P b
    --   Pa≡Pb rewrite a≡b = refl
