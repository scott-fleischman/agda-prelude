{-# OPTIONS --without-K #-}

module Prelude.Finite where

open import Agda.Primitive
open import Prelude.Conatural
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

  ⊆nat : ∀ {n} → Fin n → Nat
  ⊆nat ze = ze
  ⊆nat (su i) = su (⊆nat i)

  ⊆nat∞ : ∀ {n} → Fin n → Nat∞
  ⊆nat∞ ze = ze
  ⊆nat∞ (su i) = su [Nat∞].ι (⊆nat∞ i)

  max-inl : ∀ {m n} → Fin m → Fin (Nat.max m n)
  max-inl {ze} ()
  max-inl {su m} {ze} i = i
  max-inl {su m} {su n} ze = ze
  max-inl {su m} {su n} (su i) = su (max-inl i)

  max-inr : ∀ {m n} → Fin n → Fin (Nat.max m n)
  max-inr {ze} i = i
  max-inr {su m} {ze} ()
  max-inr {su m} {su n} ze = ze
  max-inr {su m} {su n} (su i) = su (max-inr {m} i)

open Fin public
  hiding (module Fin)
  using (Fin)
  using (ze)
  using (su_)
