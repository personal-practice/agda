open import Prelude.Init

postulate
  A X : Set
  xs ys : List A
  _∈_ : A → List A → Set
  ↑ : X → A

lem′ : xs ≡ ys → ∃ λ x → ↑ x ∈ ys
lem′ xs≡ys = qed
  where
    postulate
      lem : ∃ λ x → ↑ x ∈ xs

    qed : ∃ λ x → ↑ x ∈ ys
    qed rewrite sym xs≡ys = lem

-- Works here, but triggers in a more complicated settings, c.f. formal-bitml/Semantics/Properties/TraceInit.agda
