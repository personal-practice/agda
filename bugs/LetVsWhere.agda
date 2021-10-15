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

module ℂ₁ xs x (n : ℕ) where
  private tot = sum xs
  ℍ  = ¬Null xs × x ≥ tot
  ℂ  = ⟦ xs , n ⟧
  α  = x
  ℂ′ = ⟦ x ∷ xs , n + x ⟧

module ℂ₂ (xs : List ℕ) x n where
  ℍ = Null xs × n ≡ 0
  ℂ  = ⟦ xs , n ⟧
  α  = x
  ℂ′ = ⟦ x ∷ xs , n + x ⟧

data _—[_]→_ : C → X → C → Set where
  [1] : let open ℂ₁ xs x n in ℍ → ℂ —[ α ]→ ℂ′
  [2] : let open ℂ₂ xs x n in ℍ → ℂ —[ α ]→ ℂ′

module ℂ xs x n where
  open ℂ₁ xs x n using () renaming (ℍ to ℍ₁; ℂ′ to ℂ₁′) public
  open ℂ₂ xs x n using () renaming (ℍ to ℍ₂; ℂ′ to ℂ₂′) public

step : C → X → Maybe C
step ⟦ xs , n ⟧ x =
  let open ℂ xs x n in
       if ⌊ ¿ ℍ₁ ¿ ⌋ then just ℂ₁′
  else if ⌊ ¿ ℍ₂ ¿ ⌋ then just ℂ₂′
  else nothing
  -- where open ℂ xs x n

step-computes-relation : c —[ x ]→ c′ ⇔ step c x ≡ just c′
step-computes-relation {c = c@(⟦ xs , n ⟧)}{x} = from , to
  where
    open ℂ xs x n

    ℂ₂⇒¬ℂ₁ : ℍ₂ → ¬ ℍ₁
    ℂ₂⇒¬ℂ₁ (xs≡[] , _) (xs≢[] , _) = xs≢[] xs≡[]

    from : c —[ x ]→ c′ → step c x ≡ just c′
    from ([1] p) rewrite T⇒true $ fromWitness {Q = dec} p
                       = refl
    from ([2] p) rewrite T∘not⇒false $ fromWitnessFalse {Q = dec} (ℂ₂⇒¬ℂ₁ p)
                       | T⇒true $ fromWitness {Q = dec} p
                       = refl

    to : step c x ≡ just c′ → c —[ x ]→ c′
    to eq with ¿ ℍ₁ ¿ | eq
    ... | yes p | refl = [1] p
    ... | no  _ | eq′ with ¿ ℍ₂ ¿ | eq′
    ... | yes p | refl = [2] p
