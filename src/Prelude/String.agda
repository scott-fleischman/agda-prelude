{-# OPTIONS --without-K #-}

module Prelude.String where

open import Agda.Primitive
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Monoidal.Coproduct
open import Prelude.Path
open import Prelude.Unsafe

module String where
  postulate
    String : Set
  {-# BUILTIN STRING String #-}

  primitive
    primStringEquality : String → String → 𝟚
    primShowString : String → String

  _≟_ : (s₀ s₁ : String) → Decidable (s₀ ≡ s₁)
  s₀ ≟ s₁ with primStringEquality s₀ s₁
  … | tt = ⊕.inr Unsafe.trustMe
  … | ff = ⊕.inl void where postulate void : _

  ⟦_≟_⟧ : (s₀ s₁ : String) → 𝟚
  ⟦_≟_⟧ = primStringEquality

open String public
  using (String)
