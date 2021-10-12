-- temporary file to interactively try out Agda stuff
module REPL where

-- open import IO

-- main : Main
-- main = run (putStrLn "hello")

open import Prelude.Init

f : {impossible : ⊥} → String → ℕ
f {impossible = ()}
