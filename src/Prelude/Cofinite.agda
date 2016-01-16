{-# OPTIONS --without-K #-}

module Prelude.Cofinite where

open import Agda.Primitive
open import Prelude.Conatural
open import Prelude.Finite
open import Prelude.Monoidal.Coproduct
open import Prelude.Path

module Fin∞ where
  open Nat∞
    using (π)
    using ([∞])
    using (∞)

  data Fin∞ : (n : Nat∞) → Set where
    ze
      : ∀ {n}
      → Fin∞ (su n)
    su_
      : ∀ {n}
      → (i : Fin∞ (π n))
      → Fin∞ (su n)

  Nat : Set
  Nat = Fin∞ ∞

open Fin∞ public
  hiding (module Fin∞)
  using (Fin∞)
  using (ze)
  using (su_)
