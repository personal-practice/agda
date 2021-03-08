-- temporary file to interactively try out Agda stuff
module REPL where

open import Prelude.Init
open import Prelude.DecEq

testUnnamedImplicit : {True (1 ≟ 1 + 0)} → 1 ≡ 1 + 0
testUnnamedImplicit {p} = toWitness {Q = 1 ≟ 1 + 0} p
