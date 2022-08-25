open import Agda.Builtin.Sigma

postulate X : Set
variable x : X
postulate
  _≺_ : X → X → Set
  H : ∀ x → Σ _ (_≺ x)

module M (x : X) where
  postulate z : X

mutual
  data C : Set where
    _ :
      let
        -- y = fst (H x) -- works!
        y , _ = H x  -- raises internal error :S
        open M y
      in
      C
