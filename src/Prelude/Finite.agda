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

  max-inj₁ : {m n : Nat} → Fin m → Fin (Nat.max m n)
  max-inj₁ {ze} ()
  max-inj₁ {su m} {ze} i = i
  max-inj₁ {su m} {su n} ze = ze
  max-inj₁ {su m} {su n} (su i) = su (max-inj₁ i)

  max-inj₂ : {m n : Nat} → Fin n → Fin (Nat.max m n)
  max-inj₂ {ze} i = i
  max-inj₂ {su m} {ze} ()
  max-inj₂ {su m} {su n} ze = ze
  max-inj₂ {su m} {su n} (su i) = su (max-inj₂ {m} i)

open Fin public
  hiding (module Fin)
  using (Fin)
  using (ze)
  using (su_)
