{-# OPTIONS --without-K #-}

module Prelude.Char where

open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Monoidal.Coproduct
open import Prelude.Natural
open import Prelude.Path
open import Prelude.String
open import Prelude.Unsafe

module Char where
  open import Agda.Builtin.Char public
    using (Char)
    using (primCharEquality)
    using (primCharToNat)

  open import Agda.Builtin.String public
    using (primShowChar)

  show : Char → String
  show = primShowChar

  toNat : Char → Nat
  toNat = primCharToNat

  _≟_ : (c₀ c₁ : Char) → Decidable (c₀ ≡ c₁)
  c₀ ≟ c₁ with primCharEquality c₀ c₁
  … | tt = ⊕.inr Unsafe.trustMe
  … | ff = ⊕.inl void where postulate void : _

  ⟦_≟_⟧ : (c₀ c₁ : Char) → 𝟚
  ⟦_≟_⟧ = primCharEquality

open Char public
  using (Char)
