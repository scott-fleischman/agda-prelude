{-# OPTIONS --without-K #-}

module Prelude.Conatural where

open import Agda.Primitive
open import Prelude.Natural
  using (module Nat)

module ∞Nat where
  mutual
    data pt : Set where
      ze· : pt
      su·_ : (n : ∞Nat) → pt

    record ∞Nat : Set where
      coinductive
      constructor ι
      field
        π : pt
  open ∞Nat public

  pattern ze = ι ze·
  pattern su_ n = ι (su· n)

  fromNat : Nat.Nat → ∞Nat
  fromNat Nat.ze = ze
  fromNat (Nat.su n) = su (fromNat n)

  instance
    nat⊆∞nat : Nat.⊆ ∞Nat
    nat⊆∞nat = record { fromNat = fromNat }

  ∞ : ∞Nat
  π ∞ = su· ∞

  _+_ : ∞Nat → ∞Nat → ∞Nat
  π (m + n) with π m
  … | ze· = π n
  … | su· o = su· (o + n)

  _*_ : ∞Nat → ∞Nat → ∞Nat
  π (m * n) with π m
  … | ze· = π n
  … | su· o = su· (o * n)

open ∞Nat public
  hiding (module ∞Nat)
  using (∞Nat)
  using (ze·)
  using (su·_)
  using (ze)
  using (su_)
