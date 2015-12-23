{-# OPTIONS --without-K #-}

module Prelude.Colist where

open import Agda.Primitive
open import Prelude.Conatural
open import Prelude.Size

module ∞List where
  mutual
    data pt ..{s ℓ} (A : Set ℓ) : Set ℓ where
      []· : pt {s} A
      _∷·_ : {s′ : Size.< s} (x : A) (xs : ∞List {s′} A) → pt {s} A

    record ∞List ..{s ℓ} (A : Set ℓ) : Set ℓ where
      coinductive
      constructor ∞
      field
        π : pt {s} A
  open ∞List

  pattern [] = ∞ []·
  pattern _∷_ x xs = ∞ (x ∷· xs)

  ω : ∀ ..{ℓ} {A : Set ℓ}
    → A
    → ∞List A
  π (ω a) = a ∷· ω a

  length
    : ∀ ..{ℓ} {A : Set ℓ}
    → ∞List A
    → ∞Nat
  ∞Nat.π (length xs) with π xs
  … | []· = ze·
  … | _ ∷· ys = su· (length ys)

  _++_
    : ∀ ..{s ℓ} {A : Set ℓ}
    → ∞List {s} A
    → ∞List {s} A
    → ∞List {Size.∞} A
  π (xs ++ ys) with π xs
  … | []· = π ys
  … | x ∷· zs = x ∷· (zs ++ ys)

  map
    : ∀ ..{s ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (A → B)
    → ∞List {s} A
    → ∞List {s} B
  π (map f xs) with π xs
  … | []· = []·
  … | y ∷· ys = f y ∷· map f ys

open ∞List public
  hiding (module ∞List)
  using (∞List)
  using ([]·)
  using (_∷·_)
  using ([])
  using (_∷_)
