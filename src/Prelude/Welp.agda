module Prelude.Welp where

open import Prelude.Nat
open import Prelude.List
open import Prelude.Monad

foo : List Nat
foo = Monad.pure 32
