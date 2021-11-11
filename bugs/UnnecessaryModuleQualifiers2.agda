module UnnecessaryModuleQualifiers2 (A : Set) where
open import UnnecessaryModuleQualifiers A

f : X → A
f (UnnecessaryModuleQualifiers.X.[1] x) = ?
