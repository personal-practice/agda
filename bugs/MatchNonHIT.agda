open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; [])
open import Data.List.Membership.Propositional using (mapWith∈)

postulate X : Set

f : List X → List (List X)
f xs = mapWith∈ xs λ _ → xs

notImplemented : ∀ {ns} → f ns ≡ f ns
notImplemented = {!!} -- ←—— press C-c C-a here
