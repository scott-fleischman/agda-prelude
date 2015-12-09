{-# OPTIONS --without-K #-}

module Prelude.Monad where

open import Agda.Primitive
open import Prelude.Applicative
open import Prelude.Functor
open import Prelude.Product.Indexed

module Monad where
  record # ..{ℓ₀ ℓ₁}
    (M : Set ℓ₀ → Set ℓ₁)
    ⦃ fun : Functor M ⦄
      : Set (lsuc ℓ₀ ⊔ ℓ₁) where
    infixr 0 _=≪_
    infixl 0 _≫=_
    field
      return : ∀ {A} → A → M A
      bind : ∀ {A B} → (A → M B) → (M A → M B)

    _=≪_ : ∀ {A B} → (A → M B) → (M A → M B)
    _=≪_ = bind

    _≫=_ : ∀ {A B} → M A → (A → M B) → M B
    m ≫= k = bind k m

    instance
      applicative : Applicative M
      applicative = record
        { pure = return
        ; apply = λ fm fx →
            fm ≫= λ f →
            fx ≫= λ x →
            return (f x)
        }

    open Applicative applicative public

  module Ext ..{ℓ}
    {M : Set ℓ → Set ℓ}
    ⦃ fun : Functor M ⦄
    ⦃ mon : # M ⦄ where

    join : ∀ {A} → M (M A) → M A
    join = #.bind {M = M} {fun = fun} mon Π.idn
  open Ext ⦃ … ⦄ public

  open # ⦃ … ⦄ public

open Monad public
  renaming (# to Monad)
  hiding (module #)
  using ()
