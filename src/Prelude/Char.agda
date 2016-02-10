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
  postulate
    Char : Set
  {-# BUILTIN CHAR Char #-}

  primitive
    primCharEquality : Char → Char → 𝟚
    primCharToNat : Char → Nat
    primShowChar : Char → String

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
