{-# OPTIONS --safe #-}
open import Agda.Builtin.Bool

record Box (A : Set) : Set where
  constructor box
  field .unbox : A

-- .FAIL : {A : Set} → .A → A
-- FAIL = box true .Box.unbox

.SUCCESS : {A : Set} → .A → A
SUCCESS x = unbox
  where open Box (box x)
