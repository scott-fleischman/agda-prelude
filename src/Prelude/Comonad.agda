{-# OPTIONS --without-K #-}

module Prelude.Comonad where

open import Agda.Primitive
open import Prelude.Functor as Functor
open import Prelude.Product

module Comonad where
  record # ..{ℓ₀ ℓ₁}
    (W : Set ℓ₀ → Set ℓ₁)
    ⦃ fun : Functor W ⦄
      : Set (lsuc ℓ₀ ⊔ ℓ₁) where
    infixr 0 _≪=_
    infixl 0 _=≫_
    field
      extract : ∀ {A} → W A → A
      extend : ∀ {A B} → (W A → B) → (W A → W B)

    _≪=_ : ∀ {A B} → (W A → B) → (W A → W B)
    _≪=_ = extend

    _=≫_ : ∀ {A B} → W A → (W A → B) → W B
    m =≫ k = extend k m

  module Ext ..{ℓ}
    {W : Set ℓ → Set ℓ}
    ⦃ fun : Functor W ⦄
    ⦃ com : # W ⦄ where

    split : ∀ {A} → W A → W (W A)
    split = #.extend com ⊗.Π.idn
  open Ext ⦃ … ⦄ public

  open # ⦃ … ⦄ public

open Comonad public
  renaming (# to Comonad)
  hiding (module #)
  using ()
