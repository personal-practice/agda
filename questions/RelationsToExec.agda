open import Prelude.Init
open import Prelude.Lists
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.General


X = ℕ

data C : Set where
  ⟦_⟧ : List ℕ × ℕ → C

private variable
  x n : X
  xs : List ℕ
  c c′ : C

data _—[_]→_ : C → X → C → Set where
  [1] :
    let tot = sum xs in
      ¬Null xs
    → x ≥ tot
      --─────────────────────────────────────────────────
    → ⟦ xs , n ⟧
      —[ x ]→
      ⟦ x ∷ xs , n + x ⟧

step : C → X → Maybe C
step ⟦ xs , n ⟧ x =
  if ⌊ ¿ (
       let tot = sum xs in
         ¬Null xs
       × x ≥ tot
     ) ¿ ⌋
    then just ⟦ x ∷ xs , n + x ⟧
    else nothing

step-computes-relation : c —[ x ]→ c′ ⇔ step c x ≡ just c′
step-computes-relation {c = c@(⟦ xs , n ⟧)}{x} = from , to
  where
    from : c —[ x ]→ c′ → step c x ≡ just c′
    from ([1] p₁ p₂) rewrite T⇒true $ fromWitness {Q = dec} (p₁ , p₂) = refl

    to : step c x ≡ just c′ → c —[ x ]→ c′
    to eq with ¿ (let tot = sum xs in ¬Null xs × x ≥ tot) ¿ | eq
    ... | yes (p₁ , p₂) | refl = [1] p₁ p₂
