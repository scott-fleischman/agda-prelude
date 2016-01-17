{-# OPTIONS --without-K #-}

module Prelude.Stream where

open import Agda.Primitive
open import Prelude.Comonad
open import Prelude.Functor
  using (Functor)
open import Prelude.List
open import Prelude.Natural
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product
open import Prelude.Size

module Stream where

  record Stream ..{s ℓ} (A : Set ℓ) : Set ℓ where
    coinductive
    constructor _∷_
    field
      head : A
      tail : ∀ {s′ : Size.< s} → Stream {s′} A
  open Stream public

  zipWith
    : ∀ ..{s ℓ}
    → {A B C : Set ℓ}
    → (f : A → B → C)
    → (xs : Stream {s} A)
    → (ys : Stream {s} B)
    → Stream {s} C
  head (zipWith f xs ys) = f (head xs) (head ys)
  tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

  repeat
    : ∀ ..{s ℓ}
    → {A : Set ℓ}
    → (a : A)
    → Stream {s} A
  head (repeat xs) = xs
  tail (repeat xs) = repeat xs

  unfold
    : ∀ ..{s ℓ}
    → {A S : Set ℓ}
    → (x : S)
    → (step : S → A ⊗ S)
    → Stream {s} A
  head (unfold xs step) = ⊗.fst (step xs)
  tail (unfold xs step) = unfold (⊗.snd (step xs)) step

  interleave
    : ∀ ..{s ℓ}
    → {A : Set ℓ}
    → (xs : Stream {s} A)
    → (ys : ∀ {s′ : Size.< Size.↑ s} → Stream {s′} A)
    → Stream {s} A
  head (interleave xs ys) = head xs
  tail (interleave xs ys) {s′} = interleave {s = s′} ys (tail xs)

  take
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (n : Nat)
    → (xs : Stream A)
    → List A
  take ze xs = []
  take (su n) xs = head xs ∷ take n (tail xs)

  drop
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (n : Nat)
    → (xs : Stream A)
    → Stream A
  head (drop ze xs) = head xs
  head (drop (su n) xs) = head (drop n (tail xs))
  tail (drop ze xs) = tail xs
  tail (drop (su n) xs) = tail (drop n (tail xs))

  _++_
    : ∀ ..{s ℓ}
    → {A : Set ℓ}
    → (xs : List A)
    → (ys : Stream {Size.↑ s} A)
    → Stream {Size.↑ s} A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  embed
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (xs : List A)
    → (κ : A)
    → Stream A
  embed xs κ = xs ++ repeat κ

  map
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → (f : A → B)
    → (xs : Stream {s} A)
    → Stream {s} B
  head (map f xs) = f (head xs)
  tail (map {i} f xs) {j} = map {j} f (tail xs {j})

  extract
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (xs : Stream A)
    → A
  extract = head

  extend
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → (k : Stream A → B)
    → ((xs : Stream A) → Stream B)
  head (extend k xs) = k xs
  tail (extend k xs) = extend k (tail xs)

  instance
    functor : ∀ ..{ℓ} → Functor (Stream {ℓ = ℓ})
    Functor.#.map functor = map

    comonad : ∀ ..{ℓ} → Comonad (Stream {ℓ = ℓ})
    Comonad.#.extract comonad = extract
    Comonad.#.extend comonad = extend

  tab : ∀ ..{ℓ} {A : Set ℓ}
    → (f : Nat → A)
    → Stream A
  tab f = map f (unfold 0 ⊗.⟨ ⇒.idn , su_ ⟩)

  idx : ∀ ..{ℓ} {A : Set ℓ}
    → (xs : Stream A)
    → ((n : Nat) → A)
  idx xs n = head (drop n xs)

open Stream public
  using (Stream)
  using (_∷_)
  hiding (module Stream)
