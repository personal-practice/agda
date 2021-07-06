-- temporary file to interactively try out Agda stuff
module REPL where

open import IO

main : Main
main = run (putStrLn "hello")
