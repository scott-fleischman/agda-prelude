{-# OPTIONS --without-K #-}

module Prelude.Monad where

open import Agda.Primitive
open import Prelude.Applicative
open import Prelude.Functor
open import Prelude.Monoidal.Product.Indexed

infix 0 seq_
infix 0 [_]

pattern seq_ x = x
pattern [_] x = x

record Monad ..{ℓ₀ ℓ₁}
  (M : Set ℓ₀ → Set ℓ₁)
  ⦃ fun : Functor M ⦄
    : Set (lsuc ℓ₀ ⊔ ℓ₁) where
  infixr 1 bind
  infixr 1 _=≪_
  infixl 1 _≫=_

  field
    return_ : ∀ {A} → A → M A
    bind : ∀ {A B} → (A → M B) → (M A → M B)

  _=≪_ : ∀ {A B} → (A → M B) → (M A → M B)
  _=≪_ = bind

  _≫=_ : ∀ {A B} → M A → (A → M B) → M B
  m ≫= k = bind k m

  syntax bind (λ x → v) m = x ← m ▸ v

  applicative : Applicative M ⦃ fun = fun ⦄
  Applicative.pure applicative = return_
  Applicative.apply applicative mf mx =
    seq
      [ f ← mf
      ▸ x ← mx
      ▸ return f x
      ]

  open Applicative applicative public

module Ext ..{ℓ}
  {M : Set ℓ → Set ℓ}
  ⦃ fun : Functor M ⦄
  ⦃ mon : Monad M ⦄
  where

  join : ∀ {A} → M (M A) → M A
  join = Monad.bind {M = M} ⦃ fun = fun ⦄ mon Π.idn

open Ext ⦃ … ⦄ public
open Monad ⦃ … ⦄ public
