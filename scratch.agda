module Scratch where

data Bool : Set where
  True : Bool
  False : Bool

data Other : Set where

g : Bool -> Set
g True = Bool
g False = Other

f : (b : Bool) -> g b
f = {!!}
