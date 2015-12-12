{-# OPTIONS --without-K #-}

module Prelude.Monoidal.Diagonal where

open import Agda.Primitive
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Unit
open import Prelude.Monoidal.Void

open ⇒
  using (↻)
  using (λ⇑)
open ⊗
  using (⟨_,_⟩)
  using (fst)
open ⊕
  using ([_,_])

module Δ ..{ℓ₀} {A : Set ℓ₀} where
  ⁰ : A ⇒ 𝟙
  ⁰ = 𝟙.!

  ¹ : A ⇒ A
  ¹ = ↻

  ² : A ⇒ A ⊗ A
  ² = ⟨ ↻ , ↻ ⟩

  ʲ : ∀ ..{ℓ₁} {B : Set ℓ₁} → A → (B ⇒ A)
  ʲ = λ⇑ fst

  ⁰[_] = ⁰
  ¹[_] = ¹
  ²[_] = ²
  ʲ[_] = ʲ

module ∇ ..{ℓ₀} {A : Set ℓ₀} where
  ⁰ : 𝟘 ⇒ A
  ⁰ = 𝟘.¡

  ¹ : A ⇒ A
  ¹ = ↻

  ² : A ⊕ A ⇒ A
  ² = [ ↻ , ↻ ]

  ⁰[_] = ⁰
  ¹[_] = ¹
  ²[_] = ²
