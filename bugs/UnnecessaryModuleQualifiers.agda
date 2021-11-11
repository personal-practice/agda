module UnnecessaryModuleQualifiers (A : Set) where

data X : Set where
  [1] : A → X

-- module M₁ (B : Set) where
--   data Y : Set where
--     [1] : B → Y

-- module M₂ (B : Set) where
--   open M₁ B

--   f : Y → B
--   -- f x = {! C-c C-c x !}
--   f (M₁.[1] x) = ?
