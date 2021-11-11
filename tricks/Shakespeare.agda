-- temporary file to interactively try out Agda stuff
module REPL where

-- open import IO

-- main : Main
-- main = run (putStrLn "hello")

-- open import Prelude.Init

-- f : {impossible : ⊥} → String → ℕ
-- f {impossible = ()}

open import Prelude.Init

Type = Set

-- ∣ ⊥ ∣ = 0 elements
-- ∣ ⊤ ∣ = 1 elements
-- ∣ Bool ∣ = 2 elements
-- ...
-- ...
-- ∣ ℕ ∣ = +∞ elements (i.e. n → n' > n)

-- ∣ A ∣ = n, | B | = m
-- | A × B | = n * m
-- | A ⊎ B | = n + m
-- | A → B | = m^n

-- T : Bool → Type
-- T false = ⊥
-- T true  = ⊤

_ : T true
_ = tt

_ : T false
_ = impossible
  where postulate impossible : ⊥

f : ∀ (b : Bool) → (T b) ⊎ (¬ T b)
f b = case b of λ where
  false → {!!} -- inj₂ (λ x → x)
  true  → {!!} -- inj₁ tt
f b = case b of λ where
  false → {!!} -- inj₂ (λ x → x)
  true  → {!!} -- inj₁ tt
