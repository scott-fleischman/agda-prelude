{-# OPTIONS --without-K #-}

module Prelude.Coalgebra where

open import Agda.Primitive
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Functor

module CoAlg where
  record CoAlg ..{ℓ} (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
    no-eta-equality
    constructor Ψ
    field
      {car} : Set ℓ
      act : car → F car
  open CoAlg public

  record _⇒_ ..{ℓ}
    {F₀ F₁ : Set ℓ → Set ℓ}
    (Ψ₀ : CoAlg F₀)
    (Ψ₁ : CoAlg F₁)
      : Set ℓ where
    no-eta-equality
    field
      hom : car Ψ₀ → car Ψ₁

open CoAlg public
  using (CoAlg)
  hiding (module CoAlg)
