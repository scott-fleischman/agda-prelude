{-# OPTIONS --without-K #-}

module Prelude.List.Unsized where

open import Agda.Primitive
open import Prelude.Functor using (Functor)
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Path

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

  ++-idn-l
    : ∀ ..{ℓ} {A : Set ℓ}
    → (xs : List A)
    → ([] ++ xs) ≡ xs
  ++-idn-l xs = refl

  ++-idn-r
    : ∀ ..{ℓ} {A : Set ℓ}
    → (xs : List A)
    → (xs ++ []) ≡ xs
  ++-idn-r [] = refl
  ++-idn-r (x ∷ xs) rewrite ++-idn-r xs = refl

  ++-assoc
    : ∀ ..{ℓ} {A : Set ℓ}
    → (xs ys zs : List A)
    → (xs ++ (ys ++ zs)) ≡ ((xs ++ ys) ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

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
