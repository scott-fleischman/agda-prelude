{-# OPTIONS --without-K #-}

module Prelude.Container.Weighted where

open import Agda.Primitive
open import Prelude.Coproduct
open import Prelude.Coproduct.Indexed
open import Prelude.Diagonal
open import Prelude.Families
open import Prelude.Functor
open import Prelude.One
open import Prelude.Path
open import Prelude.Product
open import Prelude.Zero

record Con : Set₁ where
  constructor _◃[_]_
  field
    op : Set₀
    co : (ϑ : op) → Set₀
    ar : (ϑ : op) → Set₀

module _ (Σ : Con) where
  open Con

  infixr 2 ⟦_⟧◃_

  ⟦_⟧◃_ : (X : Set) → Set
  ⟦_⟧◃_ X = ⊕.Σ.[ op Σ ∋ ϑ ] (co Σ ϑ ⊗ (ar Σ ϑ → X))

  pattern F◃ ϑ n ρ = ϑ ⊕.Σ., (n ⊗., ρ)

  map◃ : ∀ {X Y} → (X → Y) → (⟦_⟧◃_ X → ⟦_⟧◃_ Y)
  map◃ f (F◃ ϑ n ρ) = F◃ ϑ n (f ⊗.Π.<∘ ρ)
