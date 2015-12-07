{-# OPTIONS --without-K #-}

module Prelude.Families where

open import Agda.Primitive

module 𝔓 where
  t : ∀ ..{ℓ₀} → Set ℓ₀ → Set _
  t {ℓ₀} X = X → Set ℓ₀
