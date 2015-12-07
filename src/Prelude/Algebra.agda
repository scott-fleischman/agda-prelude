{-# OPTIONS --without-K #-}

module Prelude.Algebra where

open import Agda.Primitive
open import Prelude.Coproduct.Indexed
open import Prelude.Functor

module Alg where
  record # ..{ℓ}
    (F : Set ℓ → Set ℓ)
    ⦃ fun : Functor F ⦄
      : Set (lsuc ℓ) where
    no-eta-equality
    constructor Ψ
    field
      {car} : Set ℓ
      act : F car → car
  open # public

  record _⇒_ ..{ℓ}
    {F₀ F₁ : Set ℓ → Set ℓ}
    ⦃ fun₀ : Functor F₀ ⦄
    ⦃ fun₁ : Functor F₁ ⦄
    (Ψ₀ : # F₀)
    (Ψ₁ : # F₁)
      : Set ℓ where
    no-eta-equality
    field
      hom : car Ψ₀ → car Ψ₁

open Alg public
  renaming (# to Alg)
  hiding (module #)
  using ()
