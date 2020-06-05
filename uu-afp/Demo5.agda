module Demo5 where

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

cong : ∀ {a b} {x y : a} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

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

magic : ∀ {a} ->  Empty -> a
magic ()

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

fst : ∀ {a b} -> Pair a b -> a
fst (x , y) = x
snd : ∀ { a b } -> Pair a b -> b
snd (x , y) = y
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

data Inspect {a : Set} (x : a) : Set where
  it : (y : a) -> x == y -> Inspect x

inspect : {a : Set} (x : a) -> Inspect x
inspect x = it x Refl

sotrue : (x : Bool) -> x == True -> So x
sotrue True eq = tt
sotrue False ()

find : {a : Set} (p : a -> Bool) (xs : List a) -> Find p xs
find p Nil = NotInTheList Base
find p (Cons x xs) with inspect (p x)
find p (Cons x xs) | it True eq = InTheList {xs = Nil} {ys = xs} x (sotrue (p x) eq)
find p (Cons x xs) | it False eq with find p xs
find p (Cons x ._) | it False eq | InTheList x₁ x₂ = {!!} --  InTheList {xs = ?} {ys = ?} x₁ x₂
find p (Cons x xs) | it False eq | NotInTheList x₁ = NotInTheList {!!}



module PRINTF where

  postulate
    Char : Set

  {-# BUILTIN CHAR Char #-}

  c : Char
  c = 'c'

  String : Set
  String = List Char

  postulate
    IO : Set -> Set
    putChar : Char -> IO Unit
    return : {a : Set} -> a -> IO a
    printString : String -> IO Unit
    _>>_ : {a b : Set} -> IO a -> IO b -> IO b
    showNat : Nat -> String

  printfType : String -> Set
  printfType Nil = Unit
  printfType (Cons c Nil) = Unit
  printfType (Cons '%' (Cons 'd' cs)) = Pair Nat (printfType cs)
  printfType (Cons '%' (Cons 's' cs)) = Pair String (printfType cs)
  printfType (Cons c cs) = printfType (cs)

  printf : (s : String) -> printfType s -> IO Unit
  printf Nil _ = return tt
  printf (Cons c Nil) _ = putChar c
  printf (Cons '%' (Cons 'd' cs)) args = printString (showNat (fst args)) >> printf cs (snd args)
  printf (Cons '%' (Cons 's' cs)) args = printString (fst args) >> printf cs (snd args)
  printf (Cons c' cs) args = putChar c' >> printf cs {!!}

  data Format : Set where
    S : Format -> Format
    D : Format -> Format
    C : Char -> Format -> Format
    E : Format

  printfTypeF : Format -> Set
  printfTypeF (S f) = Pair String (printfTypeF f)
  printfTypeF (D f) = Pair Nat (printfTypeF f)
  printfTypeF (C _ f) = printfTypeF f
  printfTypeF E = Unit

  toFormat : String -> Format
  toFormat Nil = E
  toFormat (Cons c Nil) = C c E
  toFormat (Cons '%' (Cons 'd' cs)) = D (toFormat cs)
  toFormat (Cons '%' (Cons 's' cs)) = S (toFormat cs)
  toFormat (Cons c cs) = C c (toFormat (cs))

  printfF : (f : Format) -> printfTypeF f -> IO Unit
  printfF (S f) (str , args) = printString str >> printfF f args
  printfF (D f) (n , args) =  printString (showNat n ) >> printfF f args
  printfF (C c f) args =  putChar c >> printfF f args
  printfF E args = return tt

  mainPrintF : (s : String) -> printfTypeF (toFormat s) -> IO Unit
  mainPrintF s args = printfF (toFormat s) args

  eqFormat : (f f' : Format) -> Either (f == f') (f == f' -> Empty)
  eqFormat (S f) (S f') with eqFormat f f'
  ... | Left eq = Left (cong S eq)
  ... | Right neq = Right {!!}
  eqFormat (S f) (D f') = Right \()
  eqFormat (S f) (C x₁ f') = {!!}
  eqFormat (S f) E = {!!}
  eqFormat (D f) (S f') = {!!}
  eqFormat (D f) (D f') = {!!}
  eqFormat (D f) (C x₁ f') = {!!}
  eqFormat (D f) E = {!!}
  eqFormat (C x₁ f) (S f') = {!!}
  eqFormat (C x₁ f) (D f') = {!!}
  eqFormat (C x₁ f) (C x₂ f') = {!!}
  eqFormat (C x₁ f) E = {!!}
  eqFormat E (S f') = {!!}
  eqFormat E (D f') = {!!}
  eqFormat E (C x₁ f') = {!!}
  eqFormat E E = Left Refl

  exmp = mainPrintF (Cons 'H' (Cons 'e' (Cons 'l' (Cons 'l' (Cons 'o' Nil))))) {!!}
  exmp1 = mainPrintF (Cons 'x' (Cons '=' (Cons '%' (Cons 'd' (Cons '!' Nil))))) {!!}
  exmp2 : String -> IO Unit
  exmp2 inp with toFormat inp | eqFormat (toFormat inp) (D E)
  exmp2 inp | .(D E) | Left Refl = {!!}
  exmp2 inp | f | Right x₁ = {!!}

module Eliminators where

  elimList : {a : Set} {P : List a -> Set} ->
    {!!} ->
    {!!} ->
    (xs : List a) -> P xs
  elimList = {!!}

  elimVec : {a : Set} (P : {n : Nat} -> Vec a n -> Set) ->
    {!!} ->
    {!!} ->
    (n : Nat) -> (xs : Vec a n) -> P xs
  elimVec = {!!}

  forget : ∀ {n} -> Fin n -> Nat
  forget i = {!!}

  data Bounds (n : Nat) : Nat -> Set where
    InBounds : ∀ {i : Fin n} -> Bounds n (forget i)
    OutOfBounds : (k : Nat) -> Bounds n (Succ k + n)

module Lam where

  data T : Set where
    i : T
    _=>_ : T -> T -> T

  data Term : Set where
    Lam : {!!} -> Term
    Var : {!!} -> Term
    App : {!!} -> Term

module InsertionSort where


  data _<=_ : Nat -> Nat -> Set where
    Base : forall {n} -> Zero <= n
    Step : forall {n m} ->  n <= m -> Succ n <= Succ m

  unsucc : {n m : Nat} -> Succ n <= Succ m -> n <= m
  unsucc (Step p) = p
  lessThanEq : (n : Nat) -> (m : Nat)  -> Either (n <= m) (n <= m -> Empty)
  lessThanEq Zero m = Left Base
  lessThanEq (Succ n) Zero = Right \()
  lessThanEq (Succ n) (Succ m) with lessThanEq n m
  lessThanEq (Succ n) (Succ m) | Left lt = Left (Step lt)
  lessThanEq (Succ n) (Succ m) | Right gt = Right \p -> gt (unsucc p)

  insert : Nat -> List Nat -> List Nat
  insert x Nil = Cons x Nil
  insert x (Cons y ys) with lessThanEq x y
  insert x (Cons y ys) | Left smaller = Cons x (Cons y ys)
  insert x (Cons y ys) | Right bigger = Cons y (insert x ys)

  data Sorted : List Nat -> Set where
    EmptyList : Sorted Nil
    Singleton : ∀ {x} -> Sorted (Cons x Nil)
    Step : ∀ {x y xs} -> x <= y -> Sorted (Cons y xs) -> Sorted (Cons x (Cons y xs))

  remove-head : (y : Nat) (ys : List Nat) -> Sorted (Cons y ys) -> Sorted ys
  remove-head y .Nil Singleton = EmptyList
  remove-head y .(Cons _ _) (Step x₁ p) = p

  invert : (x y : Nat) -> (x <= y -> Empty) -> y <= x
  invert Zero Zero p = Base
  invert Zero (Succ y) p = magic (p Base)
  invert (Succ n) Zero p = Base
  invert (Succ n) (Succ y) p = let ih = invert n y \q -> p (Step q) in Step ih

  aux : (x y : Nat) (ys : List Nat) -> (x <= y -> Empty) -> Sorted (Cons y ys) -> Sorted (insert x ys) -> Sorted (Cons y (insert x ys))
  aux x y Nil h sort1 sort2 = Step (invert x y h) Singleton
  aux x y (Cons z ys) h sort1 sort2 with lessThanEq x z
  aux x y (Cons z ys) h sort1 sort2 | Left x₁ = Step (invert x y h) sort2
  aux x y (Cons z ys) h (Step x₂ sort1) sort2 | Right x₁ = Step x₂ sort2

  lemma : (x : Nat) -> (xs : List Nat) -> Sorted xs -> Sorted (insert x xs)
  lemma x Nil p = Singleton
  lemma x (Cons y ys) p with lessThanEq x y
  lemma x (Cons y ys) p | Left lt = Step lt p
  lemma x (Cons y ys) p | Right gt = aux x y ys gt p (lemma x ys (remove-head _ _ p))


  sort : List Nat -> List Nat
  sort Nil = Nil
  sort (Cons x xs) = insert x (sort xs)

  correctness : (xs : List Nat) -> Sorted (sort xs)
  correctness Nil = EmptyList
  correctness (Cons x xs) = lemma x (sort xs) (correctness xs)

  data Permutes : List Nat -> List Nat -> Set where


  insertPermutes : (x : Nat) (xs : List Nat) -> Permutes (Cons x xs) (insert x (sort xs))
  insertPermutes x ys = {!!}

  permutesCorrect : (xs : List Nat) -> Permutes xs (sort xs)
  permutesCorrect Nil = {!!}
  permutesCorrect (Cons x xs) = insertPermutes x xs
