{-# OPTIONS --without-K #-}

module Prelude.Algebra where

open import Agda.Primitive
open import Prelude.Coproduct.Indexed
open import Prelude.Functor

module Alg where

  record Alg ..{ℓ} (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
    no-eta-equality
    constructor Ψ
    field
      {car} : Set ℓ
      act : F car → car
  open Alg public

  record _⇒_ ..{ℓ}
    {F₀ F₁ : Set ℓ → Set ℓ}
    (Ψ₀ : Alg F₀)
    (Ψ₁ : Alg F₁)
      : Set ℓ where
    no-eta-equality
    field
      hom : car Ψ₀ → car Ψ₁

open Alg public
  using (Alg)
  hiding (module Alg)
