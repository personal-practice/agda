module LetRewrite where

open import Prelude.Init

f : ∀ {x y z} → x ≡ y → x ≤ z → y ≤ z
f {x}{y}{z} x≡y x≤z =
  let
    res : y ≤ z
    res = subst (_≤ z) x≡y x≤z
    -- res rewrite x≡y = x≤z
    -- ^ **ERROR** Not a valid let-declaration
  in  res
