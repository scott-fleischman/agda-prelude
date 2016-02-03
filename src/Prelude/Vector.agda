{-# OPTIONS --experimental-irrelevance --without-K #-}

module Prelude.Vector where

open import Agda.Primitive
open import Prelude.Natural
open import Prelude.Finite
open import Prelude.Size

module Vec where
  infixr 1 _∷_
  infixr 0 _++_

  data Vec ..{s ℓ} (A : Set ℓ) : Nat → Set ℓ where
    []
      : Vec {s} A ze
    _∷_
      : ∀ .{s′ : Size.< s} {n}
      → (x : A)
      → (xs : Vec {s′} A n)
      → Vec {s} A (su n)

  _++_
    : ∀ ..{ℓ} {m n} {A : Set ℓ}
    → Vec A m → Vec A n
    → Vec A (m Nat.+ n)
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  map
    : ∀ .{s}..{ℓ}
    → ∀ {A : Set ℓ} {B : Set} {n}
    → (f : A → B)
    → (Vec {s} A n → Vec {s} B n)
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  idx
    : ∀ ..{ℓ} {n} {A : Set ℓ}
    → (Vec A n)
    → (Fin n → A)
  idx (x ∷ xs) ze = x
  idx (x ∷ xs) (su i) = idx xs i

  tab
    : ∀ ..{ℓ} {n} {A : Set ℓ}
    → (Fin n → A) → Vec A n
  tab {n = ze} f = []
  tab {n = su n} f = f ze ∷ tab λ i → f (su i)

  head
    : ∀ ..{ℓ} {n} {A : Set ℓ}
    → Vec A (su n)
    → A
  head (x ∷ xs) = x

  tail
    : ∀ ..{ℓ} {n} {A : Set ℓ}
    → Vec A (su n)
    → Vec A n
  tail (x ∷ xs) = xs

open Vec public
  hiding (module Vec)
  using (Vec)
  using ([])
  using (_∷_)
