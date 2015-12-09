{-# OPTIONS --without-K #-}

module Prelude.List where

open import Agda.Primitive
open import Prelude.Size
open import Prelude.Functor
  using (Functor)
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.Product.Indexed

module List where
  infixr 1 _∷_
  infixr 0 _++_

  data  List ..{s ℓ} (A : Set ℓ) : Set ℓ where
    [] : List {s} A
    _∷_ : {s′ : Size.< s} (x : A) (xs : List {s′} A) → List {s} A

  _++_ : ∀ ..{s ℓ} {A : Set ℓ}
    → (xs : List {s} A)
    → (ys : List {s} A)
    → List {Size.∞} A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  len : ∀ ..{ℓ} {A : Set ℓ}
    → (xs : List A)
    → Nat
  len [] = ze
  len (_ ∷ xs) = su (len xs)

  map : ∀ ..{s ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (f : A → B)
    → (xs : List {s} A)
    → List {s} B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  return : ∀ ..{ℓ} {A : Set ℓ}
    → (x : A)
    → List A
  return = _∷ []

  bind : ∀ ..{s ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (k : A → List {s} B)
    → ((xs : List {s} A) → List {Size.∞} B)
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
