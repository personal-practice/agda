module SmallStepLifetime2 where

open import Prelude.Init hiding (⊥)
open import Data.Empty.Polymorphic
open import Prelude.Membership
open import Prelude.Lists
open import Prelude.Nary
open import Prelude.Nary
open import Prelude.Decidable
open import Prelude.General

Hypothesis = Set
Proof = Set
Hypotheses = List Hypothesis

P₁ P₂ P₃ : Hypothesis
P₁ = ∀ (n : ℕ) → n ≥ 0
P₂ = ∀ (xs : List⁺ ℕ) → L.NE.head xs + ∑ℕ (L.NE.tail xs) ≡ ∑ℕ (L.NE.toList xs)
P₃ = ∀ (b : Bool) → not b ≡ b ∧ b

p₁ : P₁
p₁ = λ _ → z≤n

p₂ : P₂
p₂ = λ _ → refl

¬p₃ : ¬ P₃
¬p₃ p₃ = case p₃ true of λ ()

data Response (A : Set ℓ) : Set ℓ where
  Y N : A → Response A
Responses = List (Response Hypothesis)

data ℂ : Set₁ where
  ∅ : ℂ
  _∣_ : Op₂ ℂ
  ⁇_ : Hypotheses → ℂ
  Y : Proof → ℂ
  N : Proof → ℂ
  _∎ : Responses → ℂ

infix 0 _—→_
infixr 4 _∣_
infix 5 _∎
infix 5 ⁇_

variable
  A : Set ℓ
  c c′ c″ Γ Γ′ Γ″ Δ Δ′ Δ″ :  ℂ
  h h′ : Hypothesis
  hs hs′ : Hypotheses

_-answers-_ : ℂ → Hypotheses → Set₁
Δ -answers- hs with Δ
... | ∅     = hs ≡ []
... | Y h   = hs ≡ [ h ]
... | N h   = hs ≡ [ h ]
... | l ∣ r = ∃[ hsˡ ] ∃[ hsʳ ]
  ( (l -answers- hsˡ)
  × (r -answers- hsʳ)
  × (hs ↭ hsˡ ++ hsʳ)
  )
... | ⁇ _ = ⊥
... | _ ∎ = ⊥

answer : (Δ -answers- hs) → Responses
answer {Δ}{hs} p with Δ | p
... | ∅     | _ = []
... | Y h   | _ = [ Y h ]
... | N h   | _ = [ N h ]
... | l ∣ r | _ , _ , (pˡ , pʳ , _) = answer pˡ ++ answer pʳ
... | ⁇ _   | ()
... | _ ∎   | ()

toList : ℂ → List ℂ
toList = λ where
  ∅ → []
  (l ∣ r) → toList l ++ toList r
  c → [ c ]

fromList : List ℂ → ℂ
fromList [] = ∅
fromList (c ∷ []) = c
fromList (c ∷ cs) = c ∣ fromList cs

remove∅ : ℂ → ℂ
remove∅ = fromList ∘ toList

data _—→_ : ℂ → ℂ → Set₁ where

  [Remove∅] :
    Γ —→ remove∅ Γ

  [Query] :
    Γ —→ ⁇ hs ∣ Γ

  [Prove] : ∀ H {_ : H ∈ hs}
    → (h : H)
      --————————
    → ⁇ hs ∣ Γ
      —→
      ⁇ hs ∣ Γ ∣ Y H

  [Refute] : ∀ H {_ : H ∈ hs}
    → (¬h : ¬ H)
      --————————
    → ⁇ hs ∣ Γ
      —→
      ⁇ hs ∣ Γ ∣ N H

  [QED] :
      (p : Δ -answers- hs)
      --—————————————————
    → ⁇ hs ∣ Δ
      —→
      answer p ∎

data _—↠_ : ℂ → ℂ → Set₁ where
  _∎∎ : ∀ Γ → Γ —↠ Γ

  _—→⟨_⟩_ : ∀ (Γ : ℂ)
    → Γ —→ Γ′
    → Γ′ —↠ Γ″
      --————————————————————————
    → Γ —↠ Γ″

infix -1 _—↠_
infixr -1 _—→⟨_⟩_
infix 0 _∎∎

fin : Responses
fin = Y P₁ ∷ Y P₂ ∷ N P₃ ∷ []

_ : ∅ —↠ fin ∎
_ = (∅
  —→⟨ [Query] ⟩
    ⁇ ⟦ P₁ , P₂ , P₃ ⟧ ∣ ∅
  —→⟨ [Prove] P₂ {𝟚} p₂ ⟩
    ⁇ ⟦ P₁ , P₂ , P₃ ⟧ ∣ ∅ ∣ Y P₂
  —→⟨ [Refute] P₃ {𝟛} ¬p₃ ⟩
    ⁇ ⟦ P₁ , P₂ , P₃ ⟧ ∣ (∅ ∣ Y P₂) ∣ N P₃
  —→⟨ [Prove] P₁ {𝟙} p₁ ⟩
    ⁇ ⟦ P₁ , P₂ , P₃ ⟧ ∣ ((∅ ∣ Y P₂) ∣ N P₃) ∣ Y P₁
  —→⟨ [QED] p ⟩
    answer {Δ_}{hs_} p ∎
  ∎∎) :~ ans≡ ⟪ (λ ◆ → ∅ —↠ ◆ ∎) ⟫
  where
    pattern 𝟙 = here refl
    pattern 𝟚 = there 𝟙
    pattern 𝟛 = there 𝟚

    Δ_  = ((∅ ∣ Y P₂) ∣ N P₃) ∣ Y P₁
    hs_ = ⟦ P₁ , P₂ , P₃ ⟧

    p : Δ_ -answers- hs_
    p = ⟦ P₂ , P₃ ⟧ , ⟦ P₁ ⟧
          , (⟦ P₂ ⟧ , ⟦ P₃ ⟧ , ([] , [ P₂ ] , refl , (refl , ↭-refl)) , refl , ↭-refl  )
          , refl
          , (↭-trans (↭-swap P₁ P₂ ↭-refl) (↭-prep P₂ (↭-swap P₁ P₃ ↭-refl)))


    ans≡ : answer {Δ_}{hs_} p ≡ fin
    ans≡ =
      begin
        answer {Δ_}{hs_} p
      ≡⟨⟩
        answer {hs = ⟦ P₂ , P₃ ⟧} {!!} ++ answer {hs = ⟦ P₁ ⟧} {!!}
      ≡⟨⟩
        (answer {hs = ⟦ P₂ ⟧} {!!} ++ answer {hs = ⟦ P₃ ⟧} {!!}) ++ answer {hs = ⟦ P₁ ⟧} {!!}
      ≡⟨ {!!} ⟩
        answer {hs = ⟦ P₁ ⟧} (Y p₁) ++ ⟦ Y P₂ ⟧ ++ ⟦ N P₃ ⟧
      ≡⟨⟩
        ⟦ Y P₁ ⟧ ++ ⟦ Y P₂ ⟧ ++ ⟦ N P₃ ⟧
      ≡⟨⟩
        Y P₁ ∷ Y P₂ ∷ N P₃ ∷ []
      ≡⟨⟩
        fin
      QED
      where open ≡-Reasoning renaming (_∎ to _QED)
