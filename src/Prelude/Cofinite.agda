{-# OPTIONS --without-K #-}

module Prelude.Cofinite where

open import Agda.Primitive
open import Prelude.Conatural
open import Prelude.Finite
open import Prelude.Monoidal.Coproduct
open import Prelude.Natural
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

  [Nat] : Set
  [Nat] = Fin∞ ∞

  nat⊆[nat] : Nat → [Nat]
  nat⊆[nat] (ze) = ze
  nat⊆[nat] (su n) = su (nat⊆[nat] n)

  [nat]⊆nat : [Nat] → Nat
  [nat]⊆nat (ze) = ze
  [nat]⊆nat (su i) = su ([nat]⊆nat i)

  nat≅[nat] : ∀ {n} → [nat]⊆nat (nat⊆[nat] n) ≡ n
  nat≅[nat] {ze} = ≡.idn
  nat≅[nat] {su n} = ≡.ap¹ su_ nat≅[nat]

  [nat]≅nat : ∀ {i} → nat⊆[nat] ([nat]⊆nat i) ≡ i
  [nat]≅nat {ze} = ≡.idn
  [nat]≅nat {su i} = ≡.ap¹ su_ [nat]≅nat

  fin⊆fin∞ : ∀ {n} → Fin n → Fin∞ (Nat∞.fromNat n)
  fin⊆fin∞ (ze) = ze
  fin⊆fin∞ (su i) = su (fin⊆fin∞ i)

  fin∞⊆fin : ∀ {n} → Fin∞ (Nat∞.fromNat n) → Fin n
  fin∞⊆fin {ze} ()
  fin∞⊆fin {su n} ze = ze
  fin∞⊆fin {su n} (su i) = su (fin∞⊆fin i)

open Fin∞ public
  hiding (module Fin∞)
  using (Fin∞)
  using (ze)
  using (su_)
