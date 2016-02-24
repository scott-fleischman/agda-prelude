{-# OPTIONS --without-K #-}

module Prelude.Monad where

open import Agda.Primitive
open import Prelude.Applicative
open import Prelude.Functor
open import Prelude.Monoidal.Product.Indexed

module Syntax where
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
    return_
      : ∀ {A}
      → (a : A)
      → M A
    bind
      : ∀ {A B}
      → (k : A → M B)
      → (m : M A)
      → M B

  _=≪_
    : ∀ {A B}
    → (k : A → M B)
    → (m : M A)
    → M B
  _=≪_ = bind

  _≫=_
    : ∀ {A B}
    → (m : M A)
    → (k : A → M B)
    → M B
  m ≫= k = bind k m

  syntax bind (λ x → v) m = x ← m ▸ v

  applicative : Applicative M ⦃ fun = fun ⦄
  Applicative.pure applicative =
    return_
  Applicative.apply applicative mf mx =
    bind (λ f → bind (λ x → return f x) mx) mf

  open Applicative applicative public

module Ext ..{ℓ}
  {M : Set ℓ → Set ℓ}
  ⦃ fun : Functor M ⦄
  ⦃ mon : Monad M ⦄
  where

  join
    : ∀ {A}
    → (m : M (M A))
    → M A
  join = Monad.bind {M = M} ⦃ fun = fun ⦄ mon Π.idn

open Ext ⦃ … ⦄ public
open Monad ⦃ … ⦄ public
