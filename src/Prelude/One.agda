{-# OPTIONS --without-K #-}

module Prelude.One where

open import Agda.Primitive

module 𝟙 where
  record 𝟙 ..{ℓ} : Set ℓ where
    constructor *

  ! : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} → A → 𝟙 {ℓ₁}
  ! _ = *

  𝟙⁰ : Set
  𝟙⁰ = 𝟙

  !⁰ : ∀ ..{ℓ₀} {A : Set ℓ₀} → A → 𝟙⁰
  !⁰ = !

open 𝟙 public
  using (𝟙)
  using (𝟙⁰)
  using (*)
  hiding (module 𝟙)
