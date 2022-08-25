open import Prelude.Init
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.General

private variable A : Set ℓ; B : Set ℓ′; C : Set ℓ″; M : Set↑

record Monad (M : Set↑) : Setω where
  infixl 1 _>>=_
  field
    overlap ⦃ super ⦄ : Applicative M
    return : A → M A
    _>>=_  : M A → (A → M B) → M B
open Monad ⦃...⦄ public

record Monad-Laws (M : Set↑) ⦃ _ : Monad M ⦄ : Setω where
  field
    >>=-identityˡ : ∀ {A : Set ℓ} {B : Set ℓ′} {a : A} {h : A → M B} →
      (return a >>= h) ≡ h a
    >>=-identityʳ : ∀ {A : Set} (m : M A) →
      (m >>= return) ≡ m
    >>=-assoc : ∀ {A B C : Set} (m : M A) {g : A → M B} {h : B → M C} →
      ((m >>= g) >>= h) ≡ (m >>= (λ x → g x >>= h))
open Monad-Laws ⦃...⦄ public

record Lawful-Monad (M : Set↑) : Setω where
  field
    ⦃ isMonad ⦄ : Monad M
    ⦃ hasMonadLaws ⦄ : Monad-Laws M

  instance
    mkLawful-Monad : ⦃ _ : Monad M ⦄ → ⦃ Monad-Laws M ⦄ → Lawful-Monad M
    mkLawful-Monad = record {}
open Lawful-Monad ⦃...⦄ using (mkLawful-Monad) public

instance
  Monad-Maybe : Monad Maybe
  Monad-Maybe = λ where
    .return → pure
    ._>>=_ m f → maybe f nothing m

  MonadLaws-Maybe : Monad-Laws Maybe
  MonadLaws-Maybe = λ where
    .>>=-identityˡ → refl
    .>>=-identityʳ → λ where
      (just _) → refl
      nothing  → refl
    .>>=-assoc → λ where
      (just _) → refl
      nothing  → refl

-- instance
--   LawfulMonad-Maybe : Lawful-Monad Maybe
--   LawfulMonad-Maybe = record
--     { isMonad = it
--     -- { isMonad = λ where
--     --     .return → pure
--     --     ._>>=_ m f → maybe f nothing m
--     ; hasMonadLaws = it
--     -- ; hasMonadLaws = λ where
--     --     .>>=-identityˡ → refl
--     --     .>>=-identityʳ → λ where
--     --       (just _) → refl
--     --       nothing  → refl
--     --     .>>=-assoc → λ where
--     --       (just _) → refl
--     --       nothing  → refl
--     }

private
  _ : (return 5 >>= just) ≡ just 5
  _ = refl
  _ : (return 5 >>= just) ≡ just 5
  _ = >>=-identityʳ _

  _ : ⦃ _ : Lawful-Monad M ⦄ → (ℕ → M ℕ)
  _ = return

  _ : Lawful-Monad Maybe
  _ = itω
