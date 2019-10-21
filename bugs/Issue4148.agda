{-# OPTIONS -v impossible:100 #-}
module Issue4148 where

postulate
  A : Set

module M (I : Set) where

  postulate
    P : I → Set

  record R (i : I) : Set where
    constructor mk
    field
      f : P i

open module N = M A

data D : ∀ {i} → R i → Set where
  c : ∀ {i} {t : P i} → D (mk t)

test-bug : ∀ {i} {t : R i} → D t → Set₁
test-bug c = Set
