module Demo2 where

data Bool : Set where
  True : Bool
  False : Bool

not : Bool -> Bool
not True = False
not False = True

if_then_else_ : {a : Set} -> Bool -> a -> a -> a
if True then b1 else b2 = b1
if False then b1 else b2 = b2

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ n + m = Succ (n + m)

id : {a : Set} -> a -> a
id {a} x = x

example : Bool
example = id {Bool} True

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

xs : List Bool
xs = Cons True (Cons False (Cons True Nil))

_++_ : forall {a : Set} -> List a -> List a -> List a
Nil ++ ys = ys
Cons x xs ++ ys = Cons x (xs ++ ys)

length : ∀ {a} → List a → Nat
length Nil = Zero
length (Cons x xs) = Succ (length xs)

{-# BUILTIN NATURAL Nat #-}

x : Nat
x = 3 -- Succ (Succ (Succ Zero))

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

-- List lookup must return a 'Maybe a'
_!!_ : {a : Set} -> List a -> Nat -> Maybe a
Nil !! n = Nothing
Cons x xs !! Zero = Just x
Cons x xs !! Succ n = xs !!  n

--- How to define head?

head : {a : Set} -> List a -> a
head Nil = {! !}
head (Cons x xs) = x

data Vec (a : Set) : Nat -> Set where
  Nil : Vec a 0
  Cons : ∀ {n} -> (y : a) -> (ys : Vec a n) -> Vec a (Succ n)

vhead : ∀ {a n} -> Vec a (Succ n) -> a
vhead (Cons x xs) = x

data Fin : Nat -> Set where
  FZero : ∀ {n} -> Fin (Succ n)
  FSucc : ∀ {n} -> Fin n -> Fin (Succ n)

vlookup : forall {a n} -> Fin n -> Vec a n -> a
vlookup FZero (Cons x xs) = x
vlookup (FSucc i) (Cons y ys) = vlookup i ys

vlookup' : forall {a n} -> Fin n -> Vec a n -> a
vlookup' () Nil
vlookup' FZero (Cons y xs) = y
vlookup' (FSucc i) (Cons y xs) = vlookup' i xs

vlookup'' : {a : Set} -> (n : Nat) -> Fin n -> Vec a n -> a
vlookup'' .(Succ _) FZero xs = {!!}
vlookup'' .(Succ _) (FSucc i) xs = {!!}

lessThan : Nat -> Nat -> Bool
lessThan Zero Zero = False
lessThan Zero (Succ m) = True
lessThan (Succ n) Zero = False
lessThan (Succ n) (Succ m) = lessThan n m

data _<_ : Nat -> Nat -> Set where
  Base : forall {n} -> Zero < Succ n
  Step : forall {n m} ->  n < m -> Succ n < Succ m

proveSomething : Succ (Zero) < Succ (Succ (Succ (Zero)))
proveSomething = Step Base

listLookup' : {a : Set} -> (n : Nat) -> (xs : List a) -> n < length xs -> a
listLookup' n Nil ()
listLookup' .0 (Cons x₁ xs₁) Base = x₁
listLookup' .(Succ _) (Cons x₁ xs₁) (Step p) = listLookup' _ xs₁ p

listLookup'' : {a : Set} {n : Nat} -> (xs : List a) -> n < length xs -> a
listLookup'' Nil ()
listLookup'' (Cons x₁ xs₁) Base = x₁
listLookup'' (Cons x₁ xs₁) (Step p) = listLookup'' xs₁ p

foo : {n : Nat} -> Bool -> Bool
foo {n} b = if lessThan n 43 then True else False


listLookup : {a : Set} -> (n : Nat) -> (xs : List a) -> n < length xs -> a
listLookup Zero Nil ()
listLookup Zero (Cons x₁ xs₁) p = x₁
listLookup (Succ n) Nil ()
listLookup (Succ n) (Cons x₁ xs₁) (Step p) = listLookup n xs₁ p


vappend : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
vappend Nil ys = ys
vappend (Cons z zs) ys = Cons z (vappend zs ys)

vec1 : Vec Bool 4
vec1 = Cons True (Cons False (Cons True (Cons False Nil)))

vec2 : Vec Bool 2
vec2 = Cons True (Cons False Nil)

vecs : Vec Bool 6
vecs = vappend vec1 vec2

listLookup1 : {a : Set} -> (n : Nat) -> (xs : List a) -> n < length xs -> a
listLookup1 = {! .. length xs ..!}

filter : {a : Set} -> (a -> Bool) -> List a -> List a
filter p Nil = Nil
filter p (Cons x xs) with p x
... | True = Cons x (filter p xs)
... | False = filter p xs

data _==_ : Nat -> Nat -> Set where
  Refl : {n : Nat} -> n == n

cong : ∀ {n m} -> (f : Nat -> Nat) -> n == m -> f n == f m
cong {n} {.n} f Refl = Refl

sym : (x : Nat) -> (y : Nat) -> x == y -> y == x
sym x .x Refl = Refl
--sym x y p = {!!}

trans : ∀ {x y z} -> x == y -> y == z -> x == z
trans Refl q = q

exP : 3 == 3
exP = Refl

exampleProof : (2 + 3) == 5
exampleProof = Refl

lemma1 : (n : Nat) -> (0 + n) == n
lemma1 n = Refl

lemma2 : (n : Nat) -> (n + 0) == n
lemma2 Zero = Refl
lemma2 (Succ n) = let ih = lemma2 n in cong Succ ih
