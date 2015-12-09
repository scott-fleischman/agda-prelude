{-# OPTIONS --without-K #-}

module Prelude.Natural where

open import Agda.Primitive
open import Prelude.Size

module Nat where
  data Nat : Set where
    ze : Nat
    su_ : Nat → Nat
  {-# BUILTIN NATURAL Nat #-}

  _+_ : (m n : Nat) → Nat
  ze + n = n
  (su m) + n = su (m + n)

open Nat public
  using (Nat)
  using (ze)
  using (su_)
  hiding (module Nat)
