module Dollar where

open import Function using (_$_; _$′_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix; here; there)

_ : Any (_≡ 2) (1 ∷ 2 ∷ 3 ∷ [])
-- _ = there $′ here refl
_ = there $ here refl
