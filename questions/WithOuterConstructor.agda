open import Prelude.Init; open SetAsType

-- ** Case 0) Naive, full (total) pattern match
data X : Type where
  𝟘 : X
  𝟙 : ℕ → X
  𝟚 : ℕ → X

f : X → X
f = λ where
  𝟘 → 𝟙 0
  x → x

f≢𝟘 : ∀ x → f x ≢ 𝟘
f≢𝟘 = λ where
  𝟘     → λ ()
  (𝟙 _) → λ ()
  (𝟚 _) → λ ()

P : X → Type
P x
  with f𝟘≢𝟘 ← f≢𝟘 x
  with f x
... | 𝟘   = ⊥-elim $ f𝟘≢𝟘 refl
... | 𝟙 n = Vec X n
... | 𝟚 n = Vec X n

variable x : X

testP : ∃ λ n → P x ≡ Vec X n
testP {x}
  with f𝟘≢𝟘 ← f≢𝟘 x
  with f x
... | 𝟘   = ⊥-elim $ f𝟘≢𝟘 refl
... | 𝟙 n = n , refl
... | 𝟚 n = n , refl

-- ** Case 1) Datatype relation, partial (total) pattern match, inner constructors
variable n : ℕ

data NonZero : Pred₀ X where
  𝟙 : NonZero (𝟙 n)
  𝟚 : NonZero (𝟚 n)

f≢𝟘′ : ∀ x → NonZero (f x)
f≢𝟘′ = λ where
  𝟘     → 𝟙
  (𝟙 _) → 𝟙
  (𝟚 _) → 𝟚

P′ : X → Type
P′ x
  with _ ← f≢𝟘′ x
  with f x
... | 𝟙 n = Vec X n
... | 𝟚 n = Vec X n

testP′ : ∃ λ n → P′ x ≡ Vec X n
testP′ {x}
  with _ ← f≢𝟘′ x
  with f x
... | 𝟙 n = n , refl
... | 𝟚 n = n , refl

-- ** Case 2) Datatype relation, partial (total) pattern match, outer constructor
P″ : X → Type
P″ x = Vec X (go x)
  where
    go : X → ℕ
    go x
      with _ ← f≢𝟘′ x
      with f x
    ... | 𝟙 n = n
    ... | 𝟚 n = n

testP″ : ∃ λ n → P″ x ≡ Vec X n
testP″ = -, refl
