module Demo4 where

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

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b








data U : Set where
  PLUS : U -> U -> U
  TIMES : U -> U -> U
  I : U
  UNIT : U
  K : (a : B) -> U

el : U -> (Set -> Set)
el (PLUS u u₁) a = Either (el u a) (el u₁ a)
el (TIMES u u₁) a = Pair (el u a) (el u₁ a)
el I = \ x -> x
el UNIT _ = Unit
el (K b) a = elB b

data Fix (u : U) : Set where
  In : el u (Fix u) -> Fix u

map : (u : U) {X Y : Set} -> (X -> Y) -> el u X -> el u Y
map (PLUS u u₁) f (Left x₁) = Left (map u f x₁)
map (PLUS u u₁) f (Right x₁) = Right (map u₁ f x₁)
map (TIMES u u₁) f (x₁ , x₂) = map u f x₁ , map u₁ f x₂
map I f t = f t
map UNIT f t = tt
map (K a) f t = t


mapFold : ∀ {a} -> (u v : U) -> (el v a -> a) -> el u (Fix v) -> el u a
mapFold (PLUS u1 u2) v alg (Left x) = Left (mapFold u1 v alg x)
mapFold (PLUS u1 u2) v alg (Right x) = Right (mapFold u2 v alg x)
mapFold (TIMES u u₁) v alg (x , y) = (mapFold u v alg x) , (mapFold u₁ v alg y)
mapFold I v alg (In t) = alg (mapFold v v alg t)
mapFold UNIT v alg t = tt
mapFold (K a) v alg t = t

fold : ∀ {a} -> (u : U) -> (el u a -> a ) -> Fix u -> a
fold u alg (In t) = alg (mapFold u u alg t)




--- Sublists
data _⊆_ {a : Set} : List a -> List a -> Set where
  Stop : Nil ⊆ Nil
  Drop : ∀ {xs y ys} -> xs ⊆ ys -> xs ⊆ (Cons y ys)
  Keep : ∀ {x xs ys} -> xs ⊆ ys -> (Cons x xs) ⊆ (Cons x ys)

exampleLists : (Cons 1 (Cons 2 (Cons 3 Nil))) ⊆ (Cons 1 (Cons 3 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil))))))
exampleLists = Keep (Drop (Keep (Keep (Drop (Drop Stop)))))

filter : {a : Set} -> (a -> Bool) -> List a -> List a
filter p Nil = Nil
filter p (Cons x xs) with p x
filter p (Cons x xs) | True = Cons x (filter p xs)
filter p (Cons x xs) | False = filter p xs

filterLemma : {a : Set} -> (p : a -> Bool) -> (xs : List a) ->
  filter p xs ⊆ xs
filterLemma p Nil = Stop
filterLemma p (Cons x xs) with p x
filterLemma p (Cons x xs) | True = Keep (filterLemma p xs)
filterLemma p (Cons x xs) | False = Drop (filterLemma p xs)



anotherExample : (n : Nat) -> (n + 0) == n
anotherExample Zero = Refl
anotherExample (Succ n) with anotherExample n
anotherExample (Succ n) | eq with n + 0
anotherExample (Succ n) | Refl | .n = Refl


-- Parity
data N : Set where
  Z : N
  S : N -> N

foldNat : {a : Set} -> a -> (a -> a) -> N -> a
foldNat z s Z = z
foldNat z s (S n) = s (foldNat z s n)

natInduction : {P : Nat -> Set} -> P Zero -> ((k : Nat) -> P k -> P (Succ k)) -> (n : Nat) -> P n
natInduction z s Zero = z
natInduction z s (Succ n) = s n (natInduction z s n)

double : Nat -> Nat
double Zero = Zero
double (Succ n) = Succ (Succ (double n))

data Parity : Nat -> Set where
  Even : (k : Nat) -> Parity (double k) -- n = 2 * k
  Odd : (k : Nat) -> Parity (Succ (double k)) -- n = 2 * k + 1

parity : (n : Nat) -> Parity n
parity Zero = Even Zero
parity (Succ n) with parity n
parity (Succ .(double k)) | Even k = Odd k
parity (Succ .(Succ (double k))) | Odd k = Even (Succ k)

halve : Nat -> Nat
halve n with parity n
halve .(double k) | Even k = k
halve .(Succ (double k)) | Odd k = k

byParity : (P : Nat -> Set) -> (n : Nat) -> P n
byParity P n with parity n
byParity P .(double k) | Even k = {!!}
byParity P .(Succ (double k)) | Odd k = {!!}

--- sorting
postulate
  leq : Nat -> Nat -> Bool

data Terminates : List Nat -> Set where
  Base : Terminates Nil
  Step : ∀ {x xs} ->
    Terminates (filter (leq x) xs) ->
    Terminates (filter (\y -> not (leq x y))  xs) ->
    Terminates (Cons x xs)

quickSort : (xs : List Nat) -> Terminates xs -> List Nat
quickSort Nil t = Nil
quickSort (Cons x xs) (Step ltsT gtsT) =
  let stupid = quickSort xs {!!} in
  let lts = filter (leq x) xs in
  let gts = filter (\y -> not (leq x y)) xs in
  quickSort lts ltsT ++ (Cons x (quickSort gts gtsT))

termination : (xs : List Nat) -> Terminates xs
termination Nil = Base
termination (Cons x₁ xs₁) = Step {!termination (filter (leq x₁) xs₁)!} {!!}



-- Lookup
data All {a : Set} (p : a -> Bool) : List a -> Set where
  Base : All p Nil
  Step : ∀ {x xs} -> So (p x) -> All p xs  -> All p (Cons x xs)

xs' : List Bool
xs' = Cons True (Cons True (Cons True Nil))

exampleAll : All id xs'
exampleAll = Step tt (Step tt (Step tt Base))

data Find {a : Set} (p : a -> Bool) : List a -> Set where
  InTheList : forall {xs ys} (x : a) -> So (p x) -> Find p (xs ++ (Cons x ys))
  NotInTheList : ∀ {xs} -> All (\x -> not (p x)) xs -> Find p xs

find : {a : Set} (p : a -> Bool) (xs : List a) -> Find p xs
find p Nil = NotInTheList Base
find p (Cons x xs) with p x
find p (Cons x xs) | True = {!!}
find p (Cons x xs) | False = {!!}
-- with p x
--find p (Cons x xs) | True  = InTheList x {!!}
-- find p (Cons x xs) | False = let ih = find p xs in {!!}



--- Homotopy type theory
