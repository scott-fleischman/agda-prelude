{-# OPTIONS --without-K #-}

module Prelude.Signature.Weighted where

open import Agda.Primitive
open import Prelude.Families
open import Prelude.Functor
open import Prelude.Path
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Product
open import Prelude.Unit
open import Prelude.Void

record Sig : Set₁ where
  constructor _◃[_]_
  field
    op : Set₀
    co : (ϑ : op) → Set₀
    ar : (ϑ : op) → Set₀

module _ (Σ : Sig) where
  open Sig

  infixr 2 ⟦_⟧◃_

  ⟦_⟧◃_ : (X : Set) → Set
  ⟦_⟧◃_ X = ⊕.Σ[ op Σ ∋ ϑ ] (co Σ ϑ ⊗ (ar Σ ϑ → X))

  pattern F◃ ϑ n ρ = ϑ ⊕.Σ., (n ⊗., ρ)

  map◃ : ∀ {X Y} → (X → Y) → (⟦_⟧◃_ X → ⟦_⟧◃_ Y)
  map◃ f (F◃ ϑ n ρ) = F◃ ϑ n (f ⊗.Π.<∘ ρ)
