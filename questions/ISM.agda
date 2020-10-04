module ISM where

open import Prelude.Init hiding (suc; _≤_; _≥_; _>_; _<_; _+_)
open Integer using
  ( _+_; -_; -[1+_]; suc; -1ℤ; 1ℤ; pred; ∣_∣
  ; _≤_; _≥_; _>_; _<_; +0; +≤+; ≤-refl; ≤-trans; n≤1+n; ≤-step; ≤-step-neg
  )

open import Prelude.DecEq

record StateMachine (S I : Set) : Set where
  constructor SM[_,_,_]
  field
    q₀ : S
    δ : S → I → Maybe S
open StateMachine public

module SM {S I} (sm : StateMachine S I) where

  variable
    s s′ s″ : S
    i i′ i″ : I

  Predˢ = Pred S 0ℓ
  Predⁱ = Pred I 0ℓ

--

  _—→[_]_ : S → I → S → Set
  s —→[ i ] s′ = sm .δ s i ≡ just s′

  _—→_ : S → S → Set
  s —→ s′ = ∃ λ i → s —→[ i ] s′

  data _—→⋆_ : S → S → Set where
    base : s —→⋆ s
    step : s —→⋆ s′ → s′ —→ s″ → s  —→⋆ s″

  Reachable : S → Set
  Reachable = sm .q₀ —→⋆_

  -- safety (always)
  □_ : (S → Set) → Set
  □ P = ∀ {s} → Reachable s → P s

  -- liveness (eventually)
  ◇_ : (S → Set) → Set
  ◇ P = ∃ λ s → Reachable s × P s
  -- ◇ P = ¬ □ (¬_ ∘ P)

  -- lift : ∀ {S⁺} {sm⁺ : StateMachine S⁺ I}
  --   → (↓ : S⁺ → S)
  --   → (init sm⁺ ⇒ init sm)
  --   → (s⁺ —→ s⁺′ ⇒ (↓ s⁺) —→ (↓ s⁺′)
  --     -----------------------------
  --   → □ (↓ s⁺) ⇒ □⁺ s⁺
  --   → ... □/◇ are preserved ...

--

  data _⁇_—→⋆_ (Pⁱ : Predⁱ) : S → S → Set where
    base : Pⁱ ⁇ s —→⋆ s
    step : Pⁱ ⁇ s —→⋆ s′
         → s′ —→[ i ] s″
         → Pⁱ i
         → Pⁱ ⁇ s  —→⋆ s″

  sinceAsLong : Predˢ → Predˢ → Predⁱ → Set
  sinceAsLong P Q Pⁱ = ∀ s → P s → (∀ s′ → Pⁱ ⁇ s —→⋆ s′ → Q s′)

  -- s  —→⋆[ i ] s′
  -- Pˢ —→⋆[ Pⁱ ] Pˢ′
  _—→⋆⟨_⟩_ : Predˢ → Predⁱ → Predˢ → Set
  P —→⋆⟨ Pⁱ ⟩ Q = sinceAsLong P Q Pⁱ

{-

  data Formula : Set₁ where
    ∃○_ : Predˢ → Formula
    ∃□_ : Predˢ → Formula
    ∃[_u_] : Predˢ → Predˢ → Formula

  -- infix 3 ∃□_

  _⊢_ : S → Formula → Set
  s ⊢ (∃○ P)     = ∃ λ s′ → (s —→ s′) × P s′
  s ⊢ (∃□ P)     = {!!}
    -- P s × ∃ λ s′ → (s —→ s′) × (s′ ⊢ (∃□ P))
    -- ∀ s′ → s —→⋆ s′ → P s′
  s ⊢ ∃[ P u Q ] = {!!}

  ⊢_ : Formula → Set
  ⊢ φ = sm .q₀ ⊢ φ
-}

{-
  ∀○_ ∀◇_ ∀□_ ∃◇_ : Predˢ → Formula
  ∀[_u_] : Predˢ → Predˢ → Formula

  ∀○_ = ¬_ ∘ ∃○_ ∘ ¬_
  ∀◇_ = ¬_ ∘ ∃□_ ∘ ¬_
  ∀□_ = ¬_ ∘ ∃◇_ ∘ ¬_
  ∃◇ φ = ∃[ (const ⊤) u φ ]
  ∀[ φ u ψ ] = (¬ ∃□ ¬ ψ) × (¬ ∃[ ¬ ψ u (¬ φ × ¬ ψ) ])
-}

module Counter where

  counter : StateMachine ℤ ⊤
  counter .q₀ = +0
  counter .δ n tt = just (suc n)

  open SM counter

  safety : □ (_≥ +0)
  safety base                 = +≤+ z≤n
  safety (step p (tt , refl)) = ≤-trans (safety p) (n≤1+n _)

  liveness : ◇ (_≥ + 1)
  liveness = -, r₁ , ≤-refl
    where
      r₁ : Reachable (+ 1)
      r₁ = step base (tt , refl)

  -- liveness′ : □q₀ (λ s → ◇ₛ (_≥ + 1)) -- ◇ (_≥ + 1))
  -- liveness′ = ?

  -- NEXT
  -- _ : ○ (_≡ + 1)
  -- _ = ?
  -- _ : ○ ○ (_≡ + 2)
  -- _ = ?

module Counter₂ where

  counter : StateMachine ℤ Bool
  counter .q₀ = +0

  counter .δ +0 true  = just 1ℤ
  counter .δ +0 false = just -1ℤ

  counter .δ z@(+_ (Nat.suc _)) _ = just (suc z)
  counter .δ z@(-[1+ _ ])       _ = just (pred z)

  open SM counter

  -- safety⁻ : ⊢ ∃□ (_≤ +0)
  -- safety⁻ = {!!}

  -- ∙ ∃□ (_≤ 0)
  -- ∙ ∃□ (_≥ 0)
  -- ∙ ∀○ ((_≡ 1) ∘ ∣_∣)

{-
  P⁺ P⁻ : ℤ → Set
  P⁺ = _> 0
  P⁻ = _< 0

  -- since P⁺ P⁺
  safety : ∀ {s} → P⁺ s → □ P⁺
  safety = ?
  -- since P⁻ P⁻

  -- safety base                 = +≤+ z≤n
  -- safety (step p (tt , refl)) = ≤-trans (safety p) (n≤1+n _)
-}


module Counter₃ where
  counter : StateMachine ℤ Bool
  counter .q₀ = +0

  counter .δ z true  = just (suc z)
  counter .δ z false = just (pred z)

  open SM counter

  sal⁺ : (_≡ +0) —→⋆⟨ T ⟩ (_≥ +0) -- ≈ sinceAsLong (_≡ +0) (_≥ +0) T
  sal⁺ .+0 refl .+0         SM.base                                   = +≤+ z≤n
  sal⁺ .+0 refl .(+ 1 + s′) (SM.step {s′ = s′} {i = true} st refl tt) = ≤-step (sal⁺ +0 refl s′ st)

  sal⁻ : (_≡ +0) —→⋆⟨ ¬_ ∘ T ⟩ (_≤ +0) -- ≈ sinceAsLong (_≡ +0) (_≤ +0) (¬_ ∘ T)
  sal⁻ .+0 refl .+0           SM.base                                   = +≤+ z≤n
  sal⁻ .+0 refl _             (SM.step {s′ = s′} {i = true}  st refl p) = ⊥-elim (p tt)
  sal⁻ .+0 refl .(- + 1 + s′) (SM.step {s′ = s′} {i = false} st refl p) = ≤-step-neg (sal⁻ +0 refl s′ st)
