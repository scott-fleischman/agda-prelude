{-# OPTIONS --without-K #-}

module Prelude.List.Unsized where

open import Agda.Primitive
open import Prelude.Functor using (Functor)
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.Monoidal.Product.Indexed

module List where
  infixr 1 _∷_
  infixr 0 _++_

  data  List ..{ℓ} (A : Set ℓ) : Set ℓ where
    []
      : List A
    _∷_
      : (x : A) (xs : List A) → List A

  _++_
    : ∀ ..{ℓ} {A : Set ℓ}
    → List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  len
    : ∀ ..{ℓ} {A : Set ℓ}
    → List A → Nat
  len [] = ze
  len (_ ∷ xs) = su (len xs)

  map
    : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  return
    : ∀ ..{ℓ} {A : Set ℓ}
    → A → List A
  return = _∷ []

  bind
    : ∀ ..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (A → List B) → (List A → List B)
  bind k [] = []
  bind k (x ∷ xs) = k x ++ bind k xs

  instance
    functor : ∀ ..{ℓ} → Functor (List {ℓ = ℓ})
    Functor.#.map functor = map

    monad : ∀ ..{ℓ} → Monad (List {ℓ = ℓ})
    Monad.#.return monad = return
    Monad.#.bind monad = bind

open List public
  using (List)
  using ([])
  using (_∷_)
  hiding (module List)
