{-# OPTIONS --experimental-irrelevance --without-K #-}

module Prelude.Covector where

open import Agda.Primitive
open import Prelude.Conatural
open import Prelude.Cofinite
open import Prelude.Size

module Vec∞ where
  open Nat∞
    using ([∞])
    using (∞)

  infixr 1 _∷_
  infixr 0 _++_

  mutual
    data Vec∞ ..{s ℓ} (A : Set ℓ) : Nat∞ → Set ℓ where
      []
        : Vec∞ {s} A ze
      _∷_
        : ∀ .{s′ : Size.< s} {n}
        → (x : A)
        → (xs : [Vec∞] {s′} A (Nat∞.π n))
        → Vec∞ {s} A (su n)

    record [Vec∞] ..{s ℓ} (A : Set ℓ) (n : Nat∞) : Set ℓ where
      coinductive
      constructor ι
      field
        π : Vec∞ {s} A n
  open [Vec∞]

  Stream : Set → Set
  Stream A = Vec∞ A ∞

  mutual
    _++_
      : ∀ ..{ℓ} {m n} {A : Set ℓ}
      → Vec∞ A m
      → Vec∞ A n
      → Vec∞ A (m Nat∞.+ n)
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs [++] ys)

    _[++]_
      : ∀ ..{ℓ} {m n} {A : Set ℓ}
      → [Vec∞] A m
      →  Vec∞  A n
      → [Vec∞] A (m Nat∞.+ n)
    π (xs [++] ys) = π xs ++ ys

  mutual
    map
      : ∀ ..{s ℓ}
      → ∀ {A : Set ℓ} {B : Set} {n}
      → (f : A → B)
      → (Vec∞ {s} A n → Vec∞ {s} B n)
    map f [] = []
    map f (x ∷ xs) = f x ∷ [map] f xs

    [map]
      : ∀ .{s}..{ℓ}
      → ∀ {A : Set ℓ} {B : Set} {n}
      → (f : A → B)
      → ([Vec∞] {s} A n → [Vec∞] {s} B n)
    π ([map] f xs) = map f (π xs)

  idx
    : ∀ ..{ℓ} {n} {A : Set ℓ}
    → (Vec∞ A n)
    → (Fin∞ n → A)
  idx (x ∷ xs) (ze) = x
  idx (x ∷ xs) (su i) = idx (π xs) i

  mutual
    tab
      : ∀ ..{ℓ} {n} {A : Set ℓ}
      → (Fin∞ n → A)
      → (Vec∞ A n)
    tab {n = ze} f = []
    tab {n = su n} f = f ze ∷ [tab] f

    [tab]
      : ∀ ..{ℓ} {n} {A : Set ℓ}
      → (Fin∞ (su n) → A)
      → ([Vec∞] A (Nat∞.π n))
    π ([tab] f) = tab λ i → f (su i)

open Vec∞ public
  hiding (module Vec∞)
  using (Vec∞)
  using ([])
  using (_∷_)
