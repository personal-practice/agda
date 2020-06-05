module Exercise where

{- Instruction: Fill in all the missing definitions. In most cases,
the type signature enforces that there should be a single unique
definition that fits.

If you have any questions, don't hesitate to email me or ask in class.
-}


---------------------
------ Prelude ------
---------------------

data Bool : Set where
  True : Bool
  False : Bool

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
Zero + m = m
Succ k + m = Succ (k + m)

_*_ : Nat → Nat → Nat
Zero * n = Zero
(Succ k) * n = n + (k * n)

data List (a : Set) : Set where
  Nil : List a
  Cons : a → List a → List a

data Vec (a : Set) : Nat → Set where
  Nil : Vec a 0
  Cons : {n : Nat} → (x : a) → (xs : Vec a n) → Vec a (Succ n)

head : {a : Set} {n : Nat}-> Vec a (Succ n) → a
head (Cons x xs) = x

append : {a : Set} {n m : Nat} → Vec a n → Vec a m → Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {a : Set} (x : a) : a → Set where
  Refl : x == x

cong : {a b : Set} {x y : a} → (f : a → b) → x == y → f x == f y
cong f Refl = Refl

data Unit : Set where
  unit : Unit

data Empty : Set where

magic : {a : Set} → Empty → a
magic ()

record Pair (a b : Set) : Set where
  constructor _,_
  field
    ♯₁ : a
    ♯₂ : b
open Pair

data Fin : Nat → Set where
  Fz : forall {n} → Fin (Succ n)
  Fs : forall {n} → Fin n → Fin (Succ n)

data Maybe (a : Set) : Set where
  Just : a → Maybe a
  Nothing : Maybe a

----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : Nat} {a : Set} → a → Vec a n
pure {Zero} {_} x = Nil
pure {Succ n} {a} x = Cons x (pure {n} {a} x)

_<*>_ : {a b : Set} {n : Nat} → Vec (a → b) n → Vec a n → Vec b n
Nil <*> vx = Nil
Cons f vf <*> Cons x vx = Cons (f x) (vf <*> vx)

vmap : {a b : Set} {n : Nat} → (a → b) → Vec a n → Vec b n
vmap f Nil = Nil
vmap f (Cons x v) = Cons (f x) (vmap f v)


-- Add two vectors.
vadd : {n : Nat} → Vec Nat n → Vec Nat n → Vec Nat n
vadd Nil _ = Nil
vadd (Cons x xs) (Cons y ys) = Cons (x + y) (vadd xs ys)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set → Nat → Nat → Set
Matrix a n m = Vec (Vec a n) m

-- Define matrix addition
madd : {n m : Nat} → Matrix Nat m n → Matrix Nat m n → Matrix Nat m n
madd Nil _ = Nil
madd (Cons xs xss) (Cons ys yss) = Cons (vadd xs ys) (madd xss yss)

-- Define the identity matrix
idMatrix : {n : Nat} → Matrix Nat n n
idMatrix {Zero} = Nil
idMatrix {Succ n} = Cons (Cons 1 (pure 0)) (vmap (Cons 0) idMatrix)

-- Define matrix transposition
vhead : {a : Set} {n : Nat} → Vec a (Succ n) → a
vhead (Cons x xs) = x

insert : {n m : Nat} {a : Set } → Vec a m → Matrix a n m → Matrix a (Succ n) m
insert Nil xss = Nil
insert (Cons x ys) (Cons xs yss) = Cons (Cons x xs) (insert ys yss)

transpose : {n m : Nat} {a : Set} → Matrix a m n → Matrix a n m
transpose Nil = pure Nil
transpose (Cons xss yss) = insert xss (transpose yss)

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.

-- data Fin : Nat -> Set where
--  Fz : forall {n} -> Fin (Succ n)
--  Fs : forall {n} -> Fin n -> Fin (Succ n)

plan : {n : Nat} → Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (vmap Fs (plan {n}))

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} → Fin n → Nat
forget Fz = Zero
forget (Fs i) = Succ (forget i)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} → Fin n → Fin (Succ n)
embed Fz = Fz
embed (Fs i) = Fs (embed i)

correct : {n : Nat} → (i : Fin n) → forget i == forget (embed i)
correct Fz = Refl
correct (Fs i) = cong Succ (correct i)

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat → Nat → Set where
  LessThan : ∀ {n} k → Compare n (n + Succ k)
  Equal : ∀ {n} → Compare n n
  GreaterThan : ∀ {n} k → Compare (n + Succ k) n

-- Show that there is a 'covering function'
cmp : (n m : Nat) → Compare n m
cmp Zero Zero = Equal
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) with cmp n m
... | LessThan k = LessThan k
... | Equal = Equal
... | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) → Nat
difference n m with cmp n m
... | LessThan k = k
... | Equal = 0
... | GreaterThan k = k

----------------------
----- Exercise 5 -----
----------------------

-- Notation for equational reasoning.
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x == y → y == z → x == z
x ≡⟨ Refl ⟩ Refl = Refl
infixr 1 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x == x
x ∎ = Refl
infix  2 _∎

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} → x == y → y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} → x == y → y == z → x == z
trans Refl Refl = Refl

plusZero : (n : Nat) → (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) → Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusSucc' : (n m : Nat) → Succ (n + m) == (m + Succ n)
plusSucc' n Zero = cong Succ (plusZero n)
plusSucc' n (Succ m) = cong Succ (trans (sym (plusSucc n m)) (plusSucc' n m))

plusCommutes : (n m : Nat) → (n + m) == (m + n)
plusCommutes Zero m = sym (plusZero m)
plusCommutes (Succ n) m = plusSucc' n m

associativity : (n m k : Nat) → ((n + (m + k)) == ((n + m) + k))
associativity Zero m k = Refl
associativity (Succ n) m k = cong Succ (associativity n m k) 

constAddL : (c x y : Nat) → x == y → (c + x) == (c + y)
constAddL Zero x y eq = eq
constAddL (Succ c) x y eq = cong Succ (constAddL c x y eq)

constAddR : (x y c : Nat) → x == y → (x + c) == (y + c)
constAddR x y c eq =
   x + c
  ≡⟨ plusCommutes x c ⟩
   c + x
  ≡⟨ constAddL c x y eq ⟩ 
   c + y
  ≡⟨ plusCommutes c y ⟩ 
   y + c
  ∎

addLemma : (x y z w : Nat) → ((x + y) + (z + w)) == ((x + z) + (y + w))
addLemma x y z w =
  (x + y) + (z + w)
 ≡⟨ sym (associativity x y (z + w)) ⟩ 
  x + (y + (z + w))
 ≡⟨ constAddL x (y + (z + w)) ((y + z) + w) (associativity y z w) ⟩
  x + ((y + z) + w)
 ≡⟨ constAddL x ((y + z) + w) ((z + y) + w) (constAddR (y + z) (z + y) w (plusCommutes y z)) ⟩
  x + ((z + y) + w)
 ≡⟨  constAddL x ((z + y) + w) (z + (y + w)) (sym (associativity z y w)) ⟩
  x + (z + (y + w))
 ≡⟨ associativity x z (y + w) ⟩
  (x + z) + (y + w)
 ∎

distributivity : (n m k : Nat) → (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k =
  let ih = distributivity n m k
  in  (m + k) + (n * (m + k))
     ≡⟨ constAddL (m + k) (n * (m + k)) ((n * m) + (n * k)) ih ⟩
      (m + k) + ((n * m) + (n * k))
     ≡⟨ addLemma m k (n * m) (n * k) ⟩
      (m + (n * m)) + (k + (n * k))
     ∎

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data _⊆_ {a : Set} : List a → List a → Set where
  Base : Nil ⊆ Nil  
  Keep : ∀ {x xs ys} → xs ⊆ ys → Cons x xs ⊆ Cons x ys
  Drop : ∀ {y zs ys} → zs ⊆ ys → zs ⊆ Cons y ys

SubListRefl : {a : Set} {xs : List a} → xs ⊆ xs
SubListRefl {a} {Nil} = Base
SubListRefl {a} {Cons x xs} = Keep SubListRefl

subListNil : {a : Set} {xs : List a} → Nil ⊆ xs
subListNil {a} {Nil} = Base
subListNil {a} {Cons x xs} = Drop subListNil

SubListTrans : {a : Set} {xs ys zs : List a} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
SubListTrans Base h2 = h2
SubListTrans (Keep h1) (Keep h2) = Keep (SubListTrans h1 h2)
SubListTrans (Keep h1) (Drop h2) = Drop (SubListTrans (Keep h1) h2)
SubListTrans (Drop h1) (Keep h2) = Drop (SubListTrans h1 h2)
SubListTrans (Drop h1) (Drop h2) = Drop (SubListTrans h1 (SubListTrans (Drop SubListRefl) h2))

SubListLem : {a : Set} {xs ys : List a} → (x : a) → Cons x ys ⊆ Cons x xs → ys ⊆ xs
SubListLem x (Keep h) = h
SubListLem x (Drop h) = SubListTrans (Drop SubListRefl) h

SubListLem' : {a : Set} {xs ys : List a} → (x y : a)
           → Cons x (Cons y ys) ⊆ xs → Cons y ys ⊆ xs
SubListLem' x y (Keep h) = Drop h
SubListLem' x y (Drop h) = Drop (SubListLem' x y h)

SubListContra : {a : Set} {xs : List a} → (x : a) → Cons x xs ⊆ xs → Empty
SubListContra x (Keep h) = SubListContra x h
SubListContra {a} {Cons y ys} x (Drop h) = SubListContra y (SubListLem' x y h)

SubListAntiSym : {a : Set} {xs ys : List a} →  xs ⊆ ys → ys ⊆ xs → xs == ys
SubListAntiSym Base h2 = Refl
SubListAntiSym {a} {Cons x xs} {Cons y ys} (Keep h1) h2 =
  cong (Cons x) (SubListAntiSym h1 (SubListLem x h2))
SubListAntiSym {a} {Cons x xs} {Cons y ys} (Drop h1) (Keep h2) =
  cong (Cons x) (SubListAntiSym (SubListTrans (Drop SubListRefl) h1) h2)
SubListAntiSym {a} {Cons x xs} {Cons y ys} (Drop h1) (Drop h2) =
  magic (SubListContra x (SubListTrans h1 (SubListTrans (Drop SubListRefl) h2))) 

----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type
data _≤_ : Nat → Nat → Set  where
   Base : {n : Nat} → 0 ≤ n 
   Step : {n m : Nat} → n ≤ m → Succ n ≤ Succ m
infix 4 _≤_
   
-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) → n ≤ n
leqRefl Zero = Base
leqRefl (Succ n) = Step (leqRefl n)

leqTrans : {n m k : Nat} → n ≤ m → m ≤ k → n ≤ k
leqTrans Base h2 = Base
leqTrans (Step h1) (Step h2) = Step (leqTrans h1 h2)

leqAntiSym : {n m : Nat} → n ≤ m → m ≤ n → n == m
leqAntiSym Base Base = Refl
leqAntiSym (Step h1) (Step h2) = cong Succ (leqAntiSym h1 h2)

-- Given the following function:
_<=_ : Nat → Nat → Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} → n ≤ m → (n <= m) == True
leq<= Base = Refl
leq<= (Step h) = leq<= h

leqContra : (False == True) -> Empty
leqContra ()

<=leq : (n m : Nat) → (n <= m) == True → n ≤ m
<=leq Zero m h = Base
<=leq (Succ n) Zero h = magic (leqContra h)
<=leq (Succ n) (Succ m) h = Step (<=leq n m h)

----------------------
----- Exercise 8 -----
----------------------

-- We can define negation as follows
¬_ : Set -> Set
¬ P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} → P → ¬(¬ P)
notNotP p not = not p

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data _∨_ (a b : Set) : Set where
  Inl : a -> a ∨ b
  Inr : b -> a ∨ b

data _∧_ (a b : Set) : Set where
  And : a -> b -> a ∧ b

orCase : {a b c : Set} → (a → c) → (b → c) → a ∨ b → c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

contra : {P : Set} → ¬ (P ∧ (¬ P))
contra (And p np) = np p

deMorgan : {P : Set} → ¬ (P ∨ (¬ P)) → (¬ P) ∧ (¬ (¬ P))
deMorgan f = And (λ z → f (Inl z)) (λ z → f (Inr z)) 

deMorgan' : {P : Set} → (¬ P) ∧ (¬ (¬ P)) → ¬ (P ∨ (¬ P))
deMorgan' {P} (And np nnp) = magic (contra {¬ P} (And np nnp))
 
notNotExcludedMiddle : {P : Set} → ¬ (¬ (P ∨ (¬ P)))
notNotExcludedMiddle neg =  contra (deMorgan neg)   

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.

doubleNegation = {P : Set} → ¬ (¬ P) → P
excludedMiddle = {P : Set} → P ∨ (¬ P)
impliesToOr = {P Q : Set} → (P → Q) → (¬ P) ∨ Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...

lem : {P Q : Set} → (Q → P) → ¬ P → ¬ Q
lem {P} {Q} imp notP = λ q → notP (imp q)

step1 : {P : Set} → doubleNegation → P ∨ (¬ P)
step1 {P} dn = dn (lem {(¬ P) ∧ (¬ (¬ P))} {¬ (P ∨ (¬ P))} deMorgan contra)

step2 : {P Q : Set} → P ∨ (¬ P) → ((P → Q) → (¬ P) ∨ Q)
step2 (Inl p) imp = Inr (imp p)
step2 (Inr np) imp = Inl np

orLem : {P Q : Set} → P ∨ Q → ¬ P → Q
orLem (Inl x) notP = magic (contra (And x notP))
orLem (Inr x) notP = x

step3 : {P : Set} → impliesToOr → (¬ (¬ P) → P)
step3 {P} ito h = orLem (ito (λ z → z)) h 

-- HARDER: show that these are equivalent to Peirces law:
peircesLaw = {P Q : Set} → ((P → Q) → P) → P

-- NOTE: I prove equivalence with only 'excluded middle', but this is enough since the others
-- (i.e. Double Negation and ImpliesToOr) are also equivalent by transitivity of equivalence.

-- Peirce's Law --> Excluded Middle
peirce : {P : Set} → peircesLaw → P ∨ (¬ P)
peirce {P} law = law {P ∨ (¬ P)} {Empty} λ exM → Inr (λ p → exM (Inl p))

-- Excluded Middle --> Peirce's Law
peirce' : {P Q : Set} → (P ∨ (¬ P)) → (((P → Q) → P) → P)
peirce' {P} {Q} (Inl p) h = p
peirce' {P} {Q} (Inr np) h = magic (contra (And (h λ p → magic (contra (And p np))) np))

----------------------
----- Exercise 9 -----
----------------------

-- Given the following data type for expressions

data Expr : Set where
  Add : Expr -> Expr -> Expr
  Val : Nat -> Expr

-- We can write a simple evaluator as follows
eval : Expr → Nat
eval (Add l r) = eval l + eval r
eval (Val x) = x

-- We can also compile such expressions to stack machine code
data Cmd : Nat → Nat → Set where
  -- stop execution and return the current stack
  HALT : {n : Nat} → Cmd n n
  -- push a new number on the stack
  PUSH : {n m : Nat} → Nat → Cmd n m → Cmd n (Succ m)
  -- replace the top two elements of the stack with their sum
  ADD : {n m : Nat} → Cmd n (Succ (Succ m)) → Cmd n (Succ m)

Stack : Nat → Set
Stack n = Vec Nat n

-- Complete the following definition, executing a list of instructions
-- Note: the 'obvious' definition is not total.  There are several
-- ways to fix this. One is to use vectors rather than lists to
-- represent stacks. To do so, however, you may also need to update
-- the Cmd datatype...

pop : {n : Nat} → Stack (Succ n) → Pair (Stack n) Nat
pop (Cons x st) = st , x

stackAdd : {n : Nat} → Stack (Succ (Succ n)) → Stack (Succ n)
stackAdd (Cons y (Cons x st)) = Cons (x + y) st

exec : {n m : Nat} → Cmd n m → Stack n → Stack m
exec HALT st = st
exec (PUSH x c) st = Cons x (exec c st)
exec (ADD c) st = stackAdd (exec c st)

-- Define a compiler from expressions to instructions
_>>_ : {x y z : Nat} → Cmd x y → Cmd y z → Cmd x z
HALT >> c' = c'
c >> HALT = c
c >> PUSH x c' = PUSH x (c >> c')
c >> ADD c' = ADD (c >> c')

compile : {n : Nat} → Expr → Cmd n (Succ n)
compile {n} (Add e e') = ADD (compile e >> compile e')
compile (Val x) = PUSH x HALT

Cons' : {a : Set} {n : Nat} (xs : Vec a n) (x : a) → Vec a (Succ n)
Cons' xs x = Cons x xs 

seqHalt : {n m : Nat} → (c : Cmd n m) → (c >> HALT) == c
seqHalt HALT = Refl
seqHalt (PUSH x c) = Refl
seqHalt (ADD c) = Refl

compileLem : {x y z : Nat} {st : Stack x} (c : Cmd x y) (c' : Cmd y z)
          → exec (c >> c') st == exec c' (exec c st)
compileLem HALT c' = Refl
compileLem {x} {y} {z} {st} c HALT = cong (λ cc → exec cc st) (seqHalt c)
compileLem {x} {y} {z} {st} (PUSH i c) (PUSH i' c') = cong (Cons i') (compileLem (PUSH i c) c')
compileLem (PUSH x c) (ADD c') = cong stackAdd (compileLem (PUSH x c) c')
compileLem (ADD c) (PUSH x c') = cong (Cons x) (compileLem (ADD c) c')
compileLem {x} {y} {z} {st} (ADD c) (ADD c') = cong stackAdd (compileLem (ADD c) c')

-- And prove your compiler correct
correctness : {n : Nat} {s : Stack n} → (e : Expr) ->
   Cons (eval e) s == exec (compile e) s
correctness (Val x) = Refl
correctness {n} {st} (Add e e') =
  sym (
    stackAdd (exec (compile e >> compile e') st)
   ≡⟨ cong stackAdd (compileLem (compile e) (compile e')) ⟩
    stackAdd (exec (compile e') (exec (compile e) st))
   ≡⟨ cong stackAdd (cong (exec (compile e')) (sym (correctness e))) ⟩
    stackAdd (exec (compile e') (Cons (eval e) st))
   ≡⟨ cong stackAdd (sym (correctness e')) ⟩
    stackAdd (Cons (eval e') (Cons (eval e) st))
   ∎)

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
