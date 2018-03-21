module Demo1 where

data Bool : Set where
  True : Bool
  False : Bool

not : Bool -> Bool
not True = False
not False = True

if_then_else_ : Bool -> Bool -> Bool -> Bool
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

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

_!!_ : {a : Set} -> List a -> Nat -> Maybe a
Nil !! n = Nothing
Cons x xs !! Zero = Just x
Cons x xs !! Succ n = xs !!  n
