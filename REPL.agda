-- temporary file to interactively try out Agda stuff
module REPL where

-- open import IO

-- main : Main
-- main = run (putStrLn "hello")

-- open import Prelude.Init

-- f : {impossible : ⊥} → String → ℕ
-- f {impossible = ()}

open import Prelude.Init

variable A : Set

module Simple where

  data _∈_ (x : A) : List A → Set where
    here  : ∀ {xs} → x ∈ (x ∷ xs)
    there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

  data Term (s : List String) : Set where
    var : (x : String) → x ∈ s → Term s
    lam : (x : String) → ¬ x ∈ s → Term (x ∷ s) → Term s
    app : Term s → Term s → Term s

  ex∙ : Term []
  ex∙ = lam "f" (λ ()) (
          lam "x" (λ where (there ())) (
            app (var "f" (there here))
                (var "x" here)
          )
        )

  ex∘ : ∀ (f x : String) → f ≢ x → Term []
  ex∘ f x f≢x =
    lam f (λ ()) (
      lam x (λ where here → ⊥-elim (f≢x refl); (there ())) (
        app (var f (there here))
            (var x here)
      )
    )

module WellScopedFresh where

  data FreshList (A : Set) : Set
  _#_ : {A : Set} → A → FreshList A → Set

  data FreshList A where
    []    : FreshList A
    _∷_<_> : (x : A) (xs : FreshList A) → x # xs → FreshList A

  x # [] = ⊤
  x # (y ∷ xs < _ >) = x ≢ y × (x # xs)

  data _∈_ {A : Set} (x : A) : FreshList A → Set where
    here  : ∀ {xs p} → x ∈ (x ∷ xs < p >)
    there : ∀ {y xs p} → x ∈ xs → x ∈ (y ∷ xs < p >)

  Scope = FreshList String

  data Term (s : Scope) : Set where
    var : (x : String) → x ∈ s → Term s
    lam : (x : String) (p : x # s)
        → Term (x ∷ s < p >) → Term s
    app : Term s → Term s → Term s

  ex∙ : Term []
  ex∙ = lam "f" f# (
         lam "x" x#f (
           app (var "f" (there here))
               (var "x" here)
         )
       )
    where
      f# : "f" # []
      f# = tt

      x#f : "x" # ("f" ∷ [] < f# >)
      x#f = (λ ()) , tt

  ex∘ : ∀ (f x : String) → x ≢ f → Term []
  ex∘ f x x≢f =
    lam f tt (
      lam x (x≢f , tt) (
        app (var f (there here))
            (var x here)
      )
    )
