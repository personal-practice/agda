-- posed by Jacques Carette in [Agda-info] on 1/3/2021
module SubstPuzzle where

open import Prelude.Init

subst≢ : ∀ {k y} (i : Fin k) (p : suc k ≡ suc y) → subst Fin p (fsuc i) ≢ 0F
subst≢ 0F refl ()
subst≢ (fsuc p) refl ()

subst-suc : ∀{k k'}(m : Fin k)(p : suc k ≡ suc k')
  → subst Fin p (Fin.suc m) ≡ Fin.suc (subst Fin (Nat.suc-injective p) m)
subst-suc m refl = refl

subst≢′ : ∀ {k} (y : Fin (k + 0)) (p : suc k ≡ suc (k + 0)) → subst Fin p 0F ≢ fsuc y
subst≢′ {k} _ p rewrite Nat.+-identityʳ k | p = λ ()

lemma : (k : ℕ)(m : Fin k)(p : k ≡ k + 0) → F.splitAt k (subst Fin p m) ≡ inj₁ m
lemma (suc k) m p
  with F.splitAt (suc k) (subst Fin p m) | subst Fin p m | inspect (subst Fin p) m
lemma (suc k) m p | inj₁ x | 0F | ≡[ eq ]
  with m | eq
... | 0F     | _   = refl
... | fsuc _ | eq′ = ⊥-elim $ subst≢ _ p eq′
lemma (suc k) m p | inj₁ x | fsuc y | ≡[ eq ]
  with m | eq
... | 0F     | eq′ = ⊥-elim $ subst≢′ _ p eq′
... | fsuc i | eq′
  rewrite sym $ F.suc-injective $ subst (_≡ fsuc y) (subst-suc i p) eq′
        | lemma k i (Nat.suc-injective p)
    = refl

lemma′ : (k : ℕ)(m : Fin k)(p : k ≡ k + 0) → F.splitAt k (subst Fin p m) ≡ inj₁ m
lemma′ (suc k) m p
  with m | subst Fin p m | inspect (subst Fin p) m | Nat.suc-injective p
... | 0F | 0F | _ | _ = refl
... | 0F | fsuc mmm | ≡[ eq ] | x rewrite x = {!!}
... | fsuc mm | 0F | ≡[ eq ] | x = {!!}
... | fsuc mm | fsuc mmm | eq | x = {!!}
