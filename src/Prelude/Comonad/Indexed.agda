{-# OPTIONS --without-K #-}

module Prelude.Comonad.Indexed where

open import Agda.Primitive
open import Prelude.Families
open import Prelude.Functor.Indexed
open Fam
  using (_⊆_)

record IComonad ..{ℓ₀ ℓ₁ ℓ₂}
  {I : Set ℓ₀}
  (W : ℘ {ℓ₁ = ℓ₁} I → ℘ {ℓ₁ = ℓ₂} I)
  ⦃ fun : IFunctor W ⦄
  : Set (ℓ₀ ⊔ lsuc ℓ₁ ⊔ ℓ₂)
  where
  no-eta-equality
  field
    iextract
      : ∀ {A}
      → W A ⊆ A
    iextend
      : ∀ {A B}
      → (k : W A ⊆ B)
      → W A ⊆ W B
  syntax iextend k m = m =i≫ k

open IComonad ⦃ … ⦄ public
