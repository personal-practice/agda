module Exam where


----------------------------- DEFINITIONS ------------------------------
data Bool : Set where
  True : Bool
  False : Bool

data _≡_ {a : Set} (x : a) : a → Set where
  Refl : x ≡ x

data Empty : Set where

data Nat : Set where
  Zero : Nat
  Succ : Nat → Nat

_+_ : Nat → Nat → Nat
Zero   + m = m
Succ n + m = Succ (n + m)

{-# BUILTIN NATURAL Nat #-}

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

data Fin : Nat → Set where
  FZero : ∀ {n} → Fin (Succ n)
  FSucc : ∀ {n} → Fin n → Fin (Succ n)

data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b

data _≤_ : Nat → Nat → Set where
  Base : ∀ {n} → Zero ≤ n
  Step : ∀ {n m} →  n  ≤ m → Succ n ≤ Succ m

------------------------------- HELPERS --------------------------------

-- Equational reasoning
cong : ∀ {a b} {x y : a}
    → (f : a → b) → x ≡ y → f x ≡ f y
cong f Refl = Refl

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ Refl ⟩ Refl = Refl
infixr 1 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = Refl
infix  2 _∎

pairEq : ∀ {A B : Set} {x x' : A} {y y' : B}
       → x ≡ x' → y ≡ y' → (x , y) ≡ (x' , y')
pairEq Refl Refl = Refl

sym : {a : Set} {x y : a} → x ≡ y → y ≡ x
sym Refl = Refl

trans : {a : Set} {x y z : a} → x ≡ y → y ≡ z → x ≡ z
trans Refl Refl = Refl

magic : ∀ {a : Set} →  Empty → a
magic ()

-- Arithmetic
succEq : ∀ {x y : Nat} → (Succ x ≡ Succ y) → (x ≡ y)
succEq Refl = Refl

plusSucc : {n m : Nat} → Succ (n + m) ≡ (n + Succ m)
plusSucc {Zero}   {m} = Refl
plusSucc {Succ n} {m} = cong Succ (plusSucc {n} {m})

plusZero : (n : Nat) → (n + 0) ≡ n
plusZero Zero     = Refl
plusZero (Succ n) = cong Succ (plusZero n)

succHelp : ∀ {n m c}
         → c ≡ (n + Succ (m + Succ c))
         → c ≡ (n + Succ ((Succ m) + c))
succHelp {n} {m} {c} h =
   c
  ≡⟨ h ⟩
   n + Succ (m + Succ c)
  ≡⟨ cong (λ i → n + Succ i) (sym (plusSucc {m} {c})) ⟩
   n + Succ (Succ (m + c))
  ∎

contrarith : ∀ {n c m : Nat} → c ≡ (n + Succ (m + c)) → Empty
contrarith {Zero}   {Zero}   {m} ()
contrarith {Succ n} {Zero}   {m} ()
contrarith {Zero}   {Succ c} {m} r =
  contrarith {m} {c} {0} (succEq r)
contrarith {Succ n} {Succ c} {m} r =
  contrarith {n} {c} {Succ m} (succHelp {n} {m} {c} (succEq r))

contraLt : ∀ {i x n : Nat} → (i ≡ (x + (Succ n))) → (i ≤ n) → Empty
contraLt {.0}     {x} {n}      eq Base      =
  contrarith {x} {0} {n} (trans eq (cong (λ k → x + Succ k) (sym (plusZero n))))
contraLt {Succ n} {x} {Succ m} eq (Step lt) =
  contraLt {n} {x} {m} (succEq (trans eq (sym (plusSucc {x} {Succ m})))) lt

plusL : ∀ {n n' m m' : Nat}
       → n ≡ n' → m ≡ m' → (n + m) ≡ (n' + m')
plusL Refl Refl = Refl

plusR : ∀ {n n' c : Nat} → (n + c) ≡ (n' + c) → n ≡ n'
plusR {Zero}   {Zero}    {Zero}   r = Refl
plusR {Zero}   {Zero}    {Succ c} r = Refl
plusR {Zero}   {Succ n'} {Zero}   ()
plusR {Zero}   {Succ n'} {Succ c} r = magic (contrarith {n'} {c} {0} (succEq r))
plusR {Succ n} {Zero}    {Zero}   ()
plusR {Succ n} {Zero}    {Succ c} r = magic (contrarith {n} {c} {0} (sym (succEq r)))
plusR {Succ n} {Succ n'} {c}      r = cong Succ (plusR {n} {n'} {c} (succEq r))

-- Finite numbers
forget : {n : Nat} → Fin n → Nat
forget FZero     = Zero
forget (FSucc i) = Succ (forget i)

forgetLt : ∀ {n : Nat} {i : Fin (Succ n)} → forget i ≤ n
forgetLt {n}      {FZero}   = Base
forgetLt {Zero}   {FSucc ()}
forgetLt {Succ n} {FSucc i} = Step forgetLt

finEq : ∀ {a : Nat} {fx : Fin a} {fy : Fin a}
     → (forget fx ≡ forget fy) → (fx ≡ fy)
finEq {.(Succ _)} {FZero}    {FZero}    r = Refl
finEq {.(Succ _)} {FZero}    {FSucc fy} ()
finEq {.(Succ _)} {FSucc fx} {FZero}    ()
finEq {.(Succ _)} {FSucc fx} {FSucc fy} r = cong FSucc (finEq (succEq r))

maxFin : {n : Nat} → Fin (Succ n)
maxFin {Zero}   = FZero
maxFin {Succ n} = FSucc maxFin

embed : {n : Nat} → Fin n → Fin (Succ n)
embed FZero     = FZero
embed (FSucc i) = FSucc (embed i)

embedL : ∀ {n m : Nat} → Fin n → Fin (n + m)
embedL FZero     = FZero
embedL (FSucc i) = FSucc (embedL i)

embedR : ∀ {n m : Nat} → Fin m → Fin (n + m)
embedR {Zero}   {m} fm = fm
embedR {Succ n} {m} fm = FSucc (embedR {n} {m} fm)

correctEmbedL : {n m : Nat} → (i : Fin n) → forget (embedL {n} {m} i) ≡ forget i
correctEmbedL FZero     = Refl
correctEmbedL (FSucc i) = cong Succ (correctEmbedL i)

correctEmbedR : ∀ {n m x} → forget (embedR {n} {m} x) ≡ (forget x + n)
correctEmbedR {Zero}   {m} {x} = sym (plusZero (forget x))
correctEmbedR {Succ n} {m} {x} =
    Succ (forget (embedR {n} {m} x))
  ≡⟨ cong Succ (correctEmbedR {n} {m} {x}) ⟩
    Succ (forget x + n)
  ≡⟨ plusSucc {forget x} {n} ⟩
    forget x + Succ n
  ∎

------------------------------ SOLUTIONS -------------------------------

-- Question (a)
data W (S : Set) (P : S → Nat) : Set where
  Node : (s : S) → (Fin (P s) → W S P) → W S P

data ListS : Set where
  Nil  : ListS
  Cons : Nat → ListS

ListP : ListS → Nat
ListP Nil      = 0
ListP (Cons _) = 1

ListW : Set
ListW = W ListS ListP

none : ∀ {a : Set} → Fin 0 → a
none = λ ()

nil : ListW
nil = Node Nil none

cons : Nat → ListW → ListW
cons n w = Node (Cons n) (λ _ → w)

-- Question (b)
data TreeS : Set where
  Bin : TreeS
  Leaf : Nat → TreeS

TreeP : TreeS → Nat
TreeP Bin      = 2
TreeP (Leaf _) = 0

TreeW : Set
TreeW = W TreeS TreeP

-- Question (c)
Monoid : (r : Set) → Set
Monoid r = Pair r (r → r → r)

foldFin : ∀ {r : Set} {n : Nat} → Monoid r → (Fin n → r) → r
foldFin {r} {Zero}   (ε , <>) f = ε
foldFin {r} {Succ n} (ε , <>) f =
  <> (f maxFin) (foldFin (ε , <>) (λ i → f (embed i)))

sumFin : {n : Nat} → (Fin n → Nat) → Nat
sumFin = foldFin (0 , _+_)

gsize : ∀ {S : Set} {P : S → Nat} → W S P → Nat
gsize {S} {P} (Node s f) = 1 + sumFin (λ i → gsize (f i))

-- Question (d)
foldW : ∀ {r S P} → Monoid r → (S → r) → W S P → r
foldW {r} {S} {P} (ε , <>) alg (Node s f) =
  <> (alg s) (foldFin (ε , <>) (λ fn → foldW (ε , <>) alg (f fn)))

gsize' : ∀ {S P} → W S P → Nat
gsize' w = foldW (0 , _+_) (λ _ → 1) w

postulate
  funext : ∀ {n : Nat} {b : Set} → {f g : Fin n → b} → ((x : Fin n) → f x ≡ g x) → f ≡ g

gsizeEquiv : ∀ {S P} → (w : W S P) → gsize w ≡ gsize' w
gsizeEquiv {S} {P} (Node s f) with (P s)
... | Zero    = Refl
... | Succ ps =
  cong Succ (
    plusL
      (gsizeEquiv (f maxFin))
      (cong (foldFin {Nat} {ps} (0 , _+_))
        (funext (λ i → gsizeEquiv (f (embed i))))))

-- Question (e)
_⊕ₛ_ : Set → Set → Set
s ⊕ₛ s' = Either s s'

_⊕ₚ_ : ∀ {S S' : Set} → (P : S → Nat) → (P' : S' → Nat) → ((S ⊕ₛ S') → Nat)
(p ⊕ₚ p') (Left s)   = p s
(p ⊕ₚ p') (Right s') = p' s'

inl : ∀ {S S' P P'} → W S P → W (S ⊕ₛ S') (P ⊕ₚ P')
inl (Node s f) = Node (Left s) (λ fn → inl (f fn))

inr : ∀ {S S' P P'} → W S' P' → W (S ⊕ₛ S') (P ⊕ₚ P')
inr (Node s f) = Node (Right s) (λ fn → inr (f fn))

-- Question (f)
_⊗ₛ_ : Set → Set → Set
s ⊗ₛ s' = Pair s s'

_⊗ₚ_ : ∀ {S S' : Set} → (P : S → Nat) → (P' : S' → Nat) → ((S ⊗ₛ S') → Nat)
(p ⊗ₚ p') (a , b) = p a + p' b

fst : ∀ {S S' P P'} → W (S ⊗ₛ S') (P ⊗ₚ P') → W S P
fst (Node (s , _) f) = Node s (λ fn → fst (f (embedL fn)))

snd : ∀ {S S' P P'} → W (S ⊗ₛ S') (P ⊗ₚ P') → W S' P'
snd {S} {S'} {P} {P'} (Node (s , s') f) =
  Node s' (λ fn → snd {S} {S'} {P} {P'} (f (embedR {P s} {P' s'} fn)))

-- Question (g)
data Sigma (S : Set) (B : S → Set) : Set where
  ∃_∷_ : (s : S) → B s → Sigma S B

toPF : (S : Set) → (P : S → Nat) → Set → Set
toPF S P a = Sigma S λ s → Fin (P s) → a

-- (g): Sums
from⊕ : ∀ {S S' P P' X} → toPF (S ⊕ₛ S') (P ⊕ₚ P') X → Either (toPF S P X) (toPF S' P' X)
from⊕ (∃ Left s ∷ f)  = Left  (∃ s ∷ f)
from⊕ (∃ Right s ∷ f) = Right (∃ s ∷ f)

to⊕ : ∀ {S S' P P' X} → Either (toPF S P X) (toPF S' P' X) → toPF (S ⊕ₛ S') (P ⊕ₚ P') X
to⊕ (Left  (∃ s ∷ f)) = ∃ Left  s ∷ f
to⊕ (Right (∃ s ∷ f)) = ∃ Right s ∷ f

→⊕ : ∀ {S S' P P' X} {x : Either (toPF S P X) (toPF S' P' X)}
   → from⊕ {S} {S'} {P} {P'} {X} (to⊕ {S} {S'} {P} {P'} {X} x) ≡ x
→⊕ {S} {S'} {P} {P'} {X} {Left (∃ s ∷ x)}  = Refl
→⊕ {S} {S'} {P} {P'} {X} {Right (∃ s ∷ x)} = Refl

←⊕ : ∀ {S S' P P' X} {x : toPF (S ⊕ₛ S') (P ⊕ₚ P') X}
  → to⊕ {S} {S'} {P} {P'} {X} (from⊕ {S} {S'} {P} {P'} {X} x) ≡ x
←⊕ {S} {S'} {P} {P'} {X} {∃ Left x ∷ f}  = Refl
←⊕ {S} {S'} {P} {P'} {X} {∃ Right x ∷ f} = Refl

-- (g): Products
from⊗ : ∀ {S S' P P' X} → toPF (S ⊗ₛ S') (P ⊗ₚ P') X → Pair (toPF S P X) (toPF S' P' X)
from⊗ {S} {S'} {P} {P'} (∃ s , s' ∷ f) =
  (∃ s ∷ λ i → f (embedL i)) , (∃ s' ∷ λ i → f (embedR {P s} {P' s'} i))

compare : ∀ {x y : Nat} → (fn : Fin (x + y))
       → Either (Sigma (Fin x) (λ fx → forget fx       ≡ forget fn))
                (Sigma (Fin y) (λ fy → (forget fy + x) ≡ forget fn))
compare {Zero}   {y} fn    = Right (∃ fn ∷ plusZero (forget fn))
compare {Succ x} {y} FZero = Left  (∃ FZero ∷ Refl)
compare {Succ x} {y} (FSucc fn) with (compare {x} {y} fn)
... | Left  (∃ fx ∷ h) = Left  (∃ FSucc fx ∷ cong Succ h)
... | Right (∃ fy ∷ h) = Right (∃ fy ∷ trans (sym (plusSucc {forget fy} {x})) (cong Succ h))

⟨to⊗⟩ : ∀ {x y : Nat} {X : Set} → (Fin x → X) → (Fin y → X) → Fin (x + y) → X
⟨to⊗⟩ {x} {y} f f' fn with (compare {x} {y} fn)
... | Left  (∃ l ∷ _) = f l
... | Right (∃ r ∷ _) = f' r

to⊗ : ∀ {S S' P P' X} → Pair (toPF S P X) (toPF S' P' X) → toPF (S ⊗ₛ S') (P ⊗ₚ P') X
to⊗ {S} {S'} {P} {P'} ((∃ s  ∷ f) , (∃ s' ∷ f')) =
  ∃ s , s' ∷ λ p → ⟨to⊗⟩ f f' p

⟨→⊗⟩₁ : ∀ {X : Set} {n m : Nat} {f : Fin n → X} {f' : Fin m → X} {x : Fin n}
      → (⟨to⊗⟩ f f' (embedL x) ≡ f x)
⟨→⊗⟩₁ {X} {n} {m} {f} {f'} {x} with (compare {n} {m} (embedL {n} {m} x))
⟨→⊗⟩₁ {X} {n}      {m} {f} {f'} {x}  | Left  (∃ i ∷ r) =
  cong f (finEq (trans r (correctEmbedL x)))
⟨→⊗⟩₁ {X} {Zero}   {m} {f} {f'} {()} | Right (∃ i ∷ r)
⟨→⊗⟩₁ {X} {Succ n} {m} {f} {f'} {x}  | Right (∃ i ∷ r) =
  magic ( contraLt {forget x} {forget i} {n}
    (sym (trans r (correctEmbedL x)))
    forgetLt )

⟨→⊗⟩₂ : ∀ {X : Set} {n m : Nat} {f : Fin n → X} {f' : Fin m → X} {x : Fin m}
      → (⟨to⊗⟩ f f' (embedR {n} {m} x) ≡ f' x)
⟨→⊗⟩₂ {X} {n}      {m} {f} {f'} {x} with (compare {n} {m} (embedR {n} {m} x))
⟨→⊗⟩₂ {X} {Zero}   {m} {f} {f'} {x} | Left (∃ () ∷ r)
⟨→⊗⟩₂ {X} {Succ n} {m} {f} {f'} {x} | Left (∃ i ∷ r) =
  magic ( contraLt {forget i} {forget x} {n}
    ( forget i
    ≡⟨ r ⟩
      Succ (forget (embedR {n} {m} x))
    ≡⟨ cong Succ (correctEmbedR {n} {m} {x}) ⟩
      Succ (forget x + n)
    ≡⟨ plusSucc {forget x} {n} ⟩
      forget x + Succ n
    ∎ )
    forgetLt
  )
⟨→⊗⟩₂ {X} {n} {m} {f} {f'} {x} | Right (∃ i ∷ r) =
  cong f' (
    finEq
      (plusR {forget i} {forget x} {n}
        ( forget i + n
        ≡⟨ r ⟩
          forget (embedR {n} {m} x)
        ≡⟨ correctEmbedR {n} {m} {x} ⟩
          forget x + n
        ∎)))

→⊗ : ∀ {S S' P P' X} {x}
   → from⊗ {S} {S'} {P} {P'} {X} (to⊗ {S} {S'} {P} {P'} {X} x) ≡ x
→⊗ {S} {S'} {P} {P'} {X} {(∃ s ∷ f) , (∃ s' ∷ f')} =
  pairEq
    (cong (λ i → ∃ s ∷ i)
      (funext λ x → ⟨→⊗⟩₁ {X} {P s} {P' s'} {f} {f'} {x}))
    (cong (λ i → ∃ s' ∷ i)
      (funext λ x → ⟨→⊗⟩₂ {X} {P s} {P' s'} {f} {f'} {x}))

⟨←⊗⟩ : ∀ {X : Set} {n m : Nat} {f : Fin (n + m) → X} {x : Fin (n + m)}
      → (⟨to⊗⟩ (λ i → f (embedL {n} {m} i)) (λ i → f (embedR {n} {m} i)) x ≡ f x)
⟨←⊗⟩ {X} {n} {m} {f} {x} with compare {n} {m} x
⟨←⊗⟩ {X} {n} {m} {f} {x} | Left (∃ s ∷ fl) =
  cong f (finEq (trans (correctEmbedL s) fl))
⟨←⊗⟩ {X} {n} {m} {f} {x} | Right (∃ s ∷ fr) =
  cong f (finEq (trans (correctEmbedR {n} {m} {s}) fr))

←⊗ : ∀ {S S' P P' X} {x}
  → to⊗ {S} {S'} {P} {P'} {X} (from⊗ {S} {S'} {P} {P'} {X} x) ≡ x
←⊗ {S} {S'} {P} {P'} {X} {∃ s , s' ∷ f} =
  cong (λ i → ∃ s , s' ∷ i)
    (funext λ x  → ⟨←⊗⟩ {X} {P s} {P' s'} {f} {x})
