module Demo3 where

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
head Nil = {!!}
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

example< : 2 < 12
example< = {!!}

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

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x

cong : ∀ {n m} -> (f : Nat -> Nat) -> n == m -> f n == f m
cong {n} {.n} f Refl = Refl

sym :  {x y : Nat} -> x == y -> y == x
sym Refl = Refl

trans : ∀ {a : Set} {x y z : a} -> x == y -> y == z -> x == z
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

lemma3 : (n m : Nat) -> (m + Succ n) == Succ (m + n)
lemma3 n Zero = Refl
lemma3 n (Succ m) = cong Succ (lemma3 n m)

infixr 2 _⟨_⟩_
_⟨_⟩_ : (x : Nat) -> {y z : Nat} -> (x == y) -> (y == z) -> x == z
x ⟨ p ⟩ q = trans p q

_■ : forall {a : Set} (x : a) -> x == x
_■ x = Refl


plus-comm : (n m : Nat) -> (n + m) == (m + n)
plus-comm Zero m = {!!}
plus-comm (Succ n) m =
  (Succ n) + m
    ⟨ Refl ⟩
  Succ (n + m)
    ⟨ cong Succ (plus-comm n m) ⟩
  Succ (m + n)
    ⟨ sym (lemma3 n m) ⟩
  (m + Succ n)
    ⟨ Refl ⟩
  (m + (Succ n))
  ■

--  trans (cong Succ (plus-comm n m)) (sym (lemma3 n m))

data IsEven : Nat -> Set where
  Base : IsEven 0
  Step : forall {n} -> IsEven n -> IsEven (Succ (Succ n))

proof : IsEven 4
proof = Step (Step Base)


even? : Nat -> Bool
even? Zero = True
even? (Succ Zero) = False
even? (Succ (Succ n)) = even? n

test : even? 1024 == True
test = Refl

data Unit : Set where
  tt : Unit

data Empty : Set where

So : Bool -> Set
So True = Unit
So False = Empty

buildEven : (n : Nat) -> So (even? n) -> IsEven n
buildEven Zero h = Base
buildEven (Succ Zero) ()
buildEven (Succ (Succ n)) h = let recurse = buildEven n h in Step recurse

proof1 : IsEven 1024
proof1 = buildEven 1024 tt


B : Set
B = {!!}

elB : B -> Set
elB = {!!}

data U : Set where
  PLUS : U -> U -> U
  TIMES : U -> U -> U
  I : U
  UNIT : U
  K : (a : B) -> U

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b



data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b

el : U -> (Set -> Set)
el (PLUS u u₁) a = Either (el u a) (el u₁ a)
el (TIMES u u₁) a = Pair (el u a) (el u₁ a)
el I = \ x -> x
el UNIT _ = Unit
el (K b) a = elB b

data Fix (u : U) : Set where
  In : el u (Fix u) -> Fix u

--data Fix' (f : Set -> Set) : Set where
--  In' : f (Fix' f) -> Fix' f

map : (u : U) {X Y : Set} -> (X -> Y) -> el u X -> el u Y
map (PLUS u u₁) f (Left x₁) = Left (map u f x₁)
map (PLUS u u₁) f (Right x₁) = Right (map u₁ f x₁)
map (TIMES u u₁) f (x₁ , x₂) = map u f x₁ , map u₁ f x₂
map I f t = f t
map UNIT f t = tt
map (K a) f t = t
