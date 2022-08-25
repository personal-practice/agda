-- {-# OPTIONS --auto-inline #-}
open import Prelude.Init
open ≡-Reasoning

infixr 10 _∣_ ||_
postulate
  TODO : ∀ {A : Set} → A
  A : Set
  Cfg : Set
  _∣_ : Op₂ Cfg
  ||_ : List Cfg → Cfg
  Null : Pred₀ (List String)
  collect : Cfg → List String
  P Q : A → Cfg

private
  f : (xs : List A)
    → collect (|| map (λ x → P x ∣ Q x) xs)
    ≡ collect (|| map P xs)
  f [] = refl
  f (_ ∷ []) = TODO
  f (x ∷ xs@(_ ∷ _)) =
    -- let
    --   rec : collect (|| map (λ x → P x ∣ Q x) xs) ≡ collect (|| map P xs)
    --   rec = f xs
    -- in
    begin
      collect (|| (P x ∣ Q x ∷ map (λ x → P x ∣ Q x) xs))
    ≡⟨ TODO ⟩
      collect (P x) ++ collect (|| map (λ x → P x ∣ Q x) xs)
    ≡⟨ cong (collect (P x) ++_) rec ⟩
      collect (P x) ++ collect (|| map P xs)
    ≡⟨ TODO ⟩
      collect (|| (P x ∷ map P xs))
    ∎
    where -- NB: needs --auto-inline to pass the termination checker
      rec : collect (|| map (λ x → P x ∣ Q x) xs) ≡ collect (|| map P xs)
      rec = f xs
