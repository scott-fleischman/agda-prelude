{-# OPTIONS --without-K #-}

module Prelude.Monad.Indexed where

open import Agda.Primitive
open import Prelude.Families
open import Prelude.Functor.Indexed
open Fam
  using (_⊆_)

record IMonad ..{ℓ₀ ℓ₁ ℓ₂}
  {I : Set ℓ₀}
  (M : ℘ {ℓ₁ = ℓ₁} I → ℘ {ℓ₁ = ℓ₂} I)
  ⦃ fun : IFunctor M ⦄
  : Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂)
  where
  no-eta-equality
  field
    ireturn
      : ∀ {A}
      → A ⊆ M A
    ibind
      : ∀ {A B}
      → (k : A ⊆ M B)
      → M A ⊆ M B
  syntax ibind k m = m ≫i= k

open IMonad ⦃ … ⦄ public
