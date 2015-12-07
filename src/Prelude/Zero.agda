{-# OPTIONS --without-K #-}

module Prelude.Zero where

open import Agda.Primitive

module 𝟘 where
  data 𝟘 ..{ℓ} : Set ℓ where

  ¬_ : ∀ ..{ℓ₀ ℓ₁} → Set ℓ₀ → Set (ℓ₀ ⊔ ℓ₁)
  ¬_ {ℓ₁ = ℓ₁} A = A → 𝟘 {ℓ₁}

  ¡ : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} → 𝟘 {ℓ₁} → A
  ¡ ()

  𝟘⁰ : Set
  𝟘⁰ = 𝟘

  ¬⁰_ : ∀ ..{ℓ₀} → Set ℓ₀ → Set ℓ₀
  ¬⁰_ = ¬_ {ℓ₁ = lzero}

  ¡⁰ : ∀ ..{ℓ₀} {A : Set ℓ₀} → 𝟘⁰ → A
  ¡⁰ = ¡

open 𝟘 public
  using (𝟘)
  using (𝟘⁰)
  hiding (module 𝟘)
