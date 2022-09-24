-- reported issue as #6130
open import Agda.Builtin.List
open import Agda.Builtin.Equality

private variable
  A : Set; P : A → Set
  x : A; xs : List A

data Any (P : A → Set) : List A → Set where
  here : P x → Any P (x ∷ xs)
  there : Any P xs → Any P (x ∷ xs)

LastAny : Any P xs → Set
LastAny = λ where
  (here {xs = xs} _) → xs ≡ []
  (there p) → LastAny p

test : (p : Any P xs) → LastAny p → LastAny p
-- ↓ works
-- test _ = λ p → p

-- ↓ works
-- test = λ where
--   (here _)  → λ p → p
--   (there _) → λ p → p

-- ↓ works
-- test = λ where
--   (here _)  → λ p → p
--   (there p) → test p

-- ↓ produces two huge goals:
test = λ where
  (here _)  → λ p → p
  (there _) → test {!!} {!!}
{-
?0
  : Any P
    (_x_39 ∷
     _x_49 ∷
     _x_59 ∷
     _x_69 ∷
     _x_79 ∷
     _x_89 ∷
     _x_99 ∷
     _x_109 ∷
     _x_119 ∷
     _x_129 ∷
     _x_139 ∷
     _x_149 ∷
     _x_159 ∷
     _x_169 ∷
     _x_179 ∷
     _x_189 ∷
     _x_199 ∷
     _x_209 ∷
     _x_219 ∷
     _x_229 ∷
     _x_239 ∷
     _x_249 ∷
     _x_259 ∷
     _x_269 ∷
     _x_279 ∷
     _x_289 ∷
     _x_299 ∷
     _x_309 ∷
     _x_319 ∷
     _x_329 ∷
     _x_339 ∷
     _x_349 ∷
     _x_359 ∷
     _x_369 ∷
     _x_379 ∷
     _x_389 ∷
     _x_399 ∷
     _x_409 ∷
     _x_419 ∷
     _x_429 ∷
     _x_439 ∷
     _x_449 ∷
     _x_459 ∷
     _x_469 ∷
     _x_479 ∷ _x_489 ∷ _x_499 ∷ _x_509 ∷ _x_519 ∷ _x_529 ∷ _xs_530)
?1
  : LastAny
    (there
     (there
      (there
       (there
        (there
         (there
          (there
           (there
            (there
             (there
              (there
               (there
                (there
                 (there
                  (there
                   (there
                    (there
                     (there
                      (there
                       (there
                        (there
                         (there
                          (there
                           (there
                            (there
                             (there
                              (there
                               (there
                                (there
                                 (there
                                  (there
                                   (there
                                    (there
                                     (there
                                      (there
                                       (there
                                        (there
                                         (there
                                          (there
                                           (there
                                            (there
                                             (there
                                              (there
                                               (there
                                                (there
                                                 (there
                                                  (there
                                                   (there
                                                    (there
                                                     (there
                                                      _p_531))))))))))))))))))))))))))))))))))))))))))))))))))
-}

-- LastAny-map⁺ :
--   ∀ {A B : Set} {xs : List A} (f : A → B) {P : B → Set}
--     (x∈ : Any (P ∘ f) xs)
--     → LastAny x∈
--     → LastAny (L.Any.map⁺ {f = f} {P = P} x∈)
-- LastAny-map⁺ = LastAny-map⁺ {!!} {!!}
-- LastAny-map⁺ f {P} (there x∈) p = LastAny-map⁺ f {P} x∈ p
-- LastAny-map⁺ {!!} {!!}
-- LastAny-map⁺ {!cong f!} {!!}

-- Last∈ : Pred₀ (x ∈ xs)
-- Last∈ = LastAny

-- Last∈-map⁺ : ∀ (f : A → B) (x∈ : x ∈ xs) →
--   Last∈ x∈
--   → Last∈ (L.Mem.∈-map⁺ f x∈)
-- Last∈-map⁺ = LastAny-map⁺ {!cong f!} {!!}
