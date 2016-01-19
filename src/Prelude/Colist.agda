{-# OPTIONS --experimental-irrelevance --without-K #-}

module Prelude.Colist where

open import Agda.Primitive
open import Prelude.Conatural
open import Prelude.Size

module List∞ where
  mutual
    data List∞ ..{s ℓ} (A : Set ℓ) : Set ℓ where
      [] : List∞ {s} A
      _∷_ : .{s′ : Size.< s} (x : A) (xs : [List∞] {s′} A) → List∞ {s} A

    record [List∞] ..{s ℓ} (A : Set ℓ) : Set ℓ where
      coinductive
      constructor ι
      field
        π : List∞ {s} A
  open [List∞]

  mutual
    ∞ : ∀ ..{ℓ} {A : Set ℓ} (a : A) → List∞ A
    ∞ a = a ∷ [∞] a

    [∞] : ∀ ..{ℓ} {A : Set ℓ} (a : A) → [List∞] A
    π ([∞] a) = ∞ a

  mutual
    _++_
      : ∀ ..{s ℓ}
      → {A : Set ℓ}
      → List∞ {s} A
      → List∞ {s} A
      → List∞ {Size.∞} A
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs [++] ys)

    _[++]_
      : ∀ ..{s ℓ}
      → {A : Set ℓ}
      → [List∞] {s} A
      →  List∞  {s} A
      → [List∞] {Size.∞} A
    π (xs [++] ys) = π xs ++ ys

  mutual
    map
      : ∀ ..{s ℓ₀ ℓ₁}
      → {A : Set ℓ₀} {B : Set ℓ₁}
      → (A → B)
      → List∞ {s} A
      → List∞ {s} B
    map f [] = []
    map f (x ∷ xs) = f x ∷ [map] f xs

    [map]
      : ∀ ..{s ℓ₀ ℓ₁}
      → {A : Set ℓ₀} {B : Set ℓ₁}
      → (A → B)
      → [List∞] {s} A
      → [List∞] {s} B
    π ([map] f xs) = map f (π xs)

  mutual
    length : ∀ ..{ℓ} {A : Set ℓ} → List∞ A → Nat∞
    length [] = 0
    length (x ∷ xs) = su ([length] xs)

    [length] : ∀ ..{ℓ} {A : Set ℓ} → [List∞] A → [Nat∞]
    [Nat∞].π ([length] xs) = length (π xs)

open List∞ public
  hiding (module List∞)
  using (List∞)
  using ([])
  using (_∷_)
