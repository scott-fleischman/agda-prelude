{-# OPTIONS --without-K #-}

module Prelude.Finite where

open import Agda.Primitive
open import Prelude.Monoidal.Coproduct
open import Prelude.Natural

module Fin where
  data Fin : (n : Nat) → Set where
    ze
      : ∀ {n}
      → Fin (su n)
    su_
      : ∀ {n}
      → (i : Fin n)
      → Fin (su n)

open Fin public
  hiding (module Fin)
  using (Fin)
  using (ze)
  using (su_)
