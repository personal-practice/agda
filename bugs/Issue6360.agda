module _ (A : Set) where

record R : Set where
  field .a : A

.FAIL : R → A → A
FAIL r _ = a
  where open R r
