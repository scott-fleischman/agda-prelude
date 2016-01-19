{-# OPTIONS --experimental-irrelevance --without-K #-}

module Prelude.List where

open import Agda.Primitive
open import Prelude.Size
open import Prelude.Functor
  using (Functor)
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.Monoidal.Product.Indexed

module List where
  infixr 1 _∷_
  infixr 0 _++_

  data  List ..{s ℓ} (A : Set ℓ) : Set ℓ where
    []
      : List {s} A
    _∷_
      : .{s′ : Size.< s}
      → (x : A)
      → (xs : List {s′} A)
      → List {s} A

  _++_
    : ∀ .{s}..{ℓ} {A : Set ℓ}
    → List {s} A
    → List {s} A
    → List {Size.∞} A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  len
    : ∀ ..{ℓ} {A : Set ℓ}
    → List A → Nat
  len [] = ze
  len (_ ∷ xs) = su (len xs)

  map
    : ∀ .{s}..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (A → B)
    → List {s} A
    → List {s} B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  return
    : ∀ ..{ℓ} {A : Set ℓ}
    → A → List A
  return = _∷ []

  bind
    : ∀ .{s}..{ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (A → List {s} B)
    → (List {s} A → List {Size.∞} B)
  bind k [] = []
  bind k (x ∷ xs) = k x ++ bind k xs

  instance
    functor : ∀ ..{ℓ} → Functor (List {ℓ = ℓ})
    Functor.#.map functor = map

    monad : ∀ ..{ℓ} → Monad (List {ℓ = ℓ})
    Monad.#.return monad = return
    Monad.#.bind monad = bind

  module ⊢ where
    open import Prelude.Path

    λ⇒
      : ∀ ..{ℓ} {A : Set ℓ}
      → (xs : List A)
      → ([] ++ xs) ≡ xs
    λ⇒ xs = ≡.idn

    λ⇐
      : ∀ ..{ℓ} {A : Set ℓ}
      → (xs : List A)
      → xs ≡ ([] ++ xs)
    λ⇐ xs = λ⇒ xs ≡.⁻¹

    ρ⇒
      : ∀ ..{ℓ} {A : Set ℓ}
      → (xs : List A)
      → (xs ++ []) ≡ xs
    ρ⇒ [] = ≡.idn
    ρ⇒ (x ∷ xs) = ≡.ap¹ (λ X → x ∷ X) (ρ⇒ xs)

    ρ⇐
      : ∀ ..{ℓ} {A : Set ℓ}
      → (xs : List A)
      → xs ≡ (xs ++ [])
    ρ⇐ xs = ρ⇒ xs ≡.⁻¹

    α⇒
      : ∀ ..{ℓ} {A : Set ℓ}
      → (xs ys zs : List A)
      → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
    α⇒ [] ys zs = ≡.idn
    α⇒ (x ∷ xs) ys zs = ≡.ap¹ (λ X → x ∷ X) (α⇒ xs ys zs)

    α⇐
      : ∀ ..{ℓ} {A : Set ℓ}
      → (xs ys zs : List A)
      → (xs ++ (ys ++ zs)) ≡ ((xs ++ ys) ++ zs)
    α⇐ xs ys zs = α⇒ xs ys zs ≡.⁻¹

open List public
  using (List)
  using ([])
  using (_∷_)
  hiding (module List)
