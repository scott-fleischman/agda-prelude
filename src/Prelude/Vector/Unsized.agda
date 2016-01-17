{-# OPTIONS --without-K #-}

module Prelude.Vector.Unsized where

open import Agda.Primitive
open import Prelude.Natural
open import Prelude.Finite
open import Prelude.Size

module Vec where
  infixr 1 _∷_
  infixr 0 _++_

  data Vec ..{ℓ} (A : Set ℓ) : Nat → Set ℓ where
    []
      : Vec A ze
    _∷_
      : ∀ {n} (x : A) (xs : Vec A n) → Vec A (su n)

  _++_
    : ∀ ..{ℓ} {A : Set ℓ} {m n}
    → Vec A m → Vec A n
    → Vec A (m Nat.+ n)
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  map
    : ∀ ..{ℓ} {A : Set ℓ} {B : Set} {n}
    → (A → B) → (Vec A n → Vec B n)
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  idx
    : ∀ ..{ℓ} {A : Set ℓ} {n}
    → Vec A n → (Fin n → A)
  idx (x ∷ xs) ze = x
  idx (x ∷ xs) (su i) = idx xs i

  tab
    : ∀ ..{ℓ} {A : Set ℓ} {n}
    → (Fin n → A) → Vec A n
  tab {n = ze} f = []
  tab {n = su n} f = f ze ∷ tab λ i → f (su i)

  head
    : ∀ ..{ℓ} {A : Set ℓ} {n}
    → Vec A (su n) → A
  head (x ∷ xs) = x

  tail
    : ∀ ..{ℓ} {A : Set ℓ} {n}
    → Vec A (su n) → Vec A n
  tail (x ∷ xs) = xs

open Vec public
  hiding (module Vec)
  using (Vec)
  using ([])
  using (_∷_)
