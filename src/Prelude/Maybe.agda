{-# OPTIONS --experimental-irrelevance --without-K #-}

module Prelude.Maybe where

open import Agda.Primitive
open import Prelude.Decidable
open import Prelude.Applicative
  using (Applicative)
open import Prelude.Functor
  using (Functor)
open import Prelude.Monad
  using (Monad)
  using (_≫=_)
open import Prelude.Monoidal.Void
open import Prelude.List
open import Prelude.Path
open import Prelude.Size

module Maybe where
  data  Maybe ..{ℓ} (A : Set ℓ) : Set ℓ where
    no : Maybe A
    so : (a : A) → Maybe A

  map
    : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (A → B)
    → (Maybe A → Maybe B)
  map f no = no
  map f (so a) = so (f a)

  bind
    : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (A → Maybe B)
    → (Maybe A → Maybe B)
  bind k no = no
  bind k (so a) = k a

  instance
    functor
      : ∀ ..{ℓ}
      → Functor (Maybe {ℓ = ℓ})
    Functor.map functor = map

    monad
      : ∀ ..{ℓ}
      → Monad (Maybe {ℓ = ℓ})
    Monad.return monad = so
    Monad.bind monad = bind

    applicative
      : ∀ ..{ℓ}
      → Applicative (Maybe {ℓ = ℓ})
    applicative = Monad.applicative monad

  sequence
    : ∀ ..{s ℓ} {A : Set ℓ}
    → List {s} (Maybe A)
    → Maybe (List {s} A)
  sequence [] = so []
  sequence (no   ∷ xs) = no
  sequence (so y ∷ xs) with sequence xs
  sequence (so y ∷ xs) | no    = no
  sequence (so y ∷ xs) | so ys = so (y ∷ ys)

  module ⊢ where
    so-inj
      : {A : Set}{a₀ a₁ : A}
      → so a₀ ≡ so a₁
      → a₀ ≡ a₁
    so-inj refl = refl

    no≢so
      : {A : Set}{a : A}
      → (φ : no ≡ so a)
      → 𝟘
    no≢so ()
open Maybe public
  hiding (module Maybe)
  using (Maybe)
  using (no)
  using (so)
