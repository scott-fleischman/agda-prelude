{-# OPTIONS --without-K #-}

module Prelude.Stream where

open import Agda.Primitive
open import Prelude.Comonad
open import Prelude.Coproduct
open import Prelude.Coproduct.Indexed
open import Prelude.Function
open import Prelude.Functor
  using (Functor)
open import Prelude.List
open import Prelude.Nat
open import Prelude.Product
open import Prelude.Size

module Stream where

  record Stream ..{s ℓ} (A : Set ℓ) : Set ℓ where
    coinductive
    constructor _∷_
    field
      head : A
      tail : ∀ {s′ : Size.< s} → Stream {s′} A
  open Stream

  zipWith
    : ∀ ..{s ℓ}
    → {A B C : Set ℓ}
    → (f : A → B → C)
    → (α₀ : Stream {s} A)
    → (α₁ : Stream {s} B)
    → Stream {s} C
  head (zipWith f α₀ α₁) = f (head α₀) (head α₁)
  tail (zipWith f α₀ α₁) = zipWith f (tail α₀) (tail α₁)

  repeat
    : ∀ ..{s ℓ}
    → {A : Set ℓ}
    → (a : A)
    → Stream {s} A
  head (repeat α) = α
  tail (repeat α) = repeat α

  unfold
    : ∀ ..{s ℓ}
    → {A S : Set ℓ}
    → (x : S)
    → (step : S → A ⊗ S)
    → Stream {s} A
  head (unfold α step) = ⊗.fst (step α)
  tail (unfold α step) = unfold (⊗.snd (step α)) step

  interleave : ∀ ..{s ℓ} {A : Set ℓ}
    → (α₀ : Stream {s} A)
    → (α₁ : ∀ {s′ : Size.< Size.↑ s} → Stream {s′} A)
    → Stream {s} A
  head (interleave α₀ α₁) = head α₀
  tail (interleave α₀ α₁) {s′} = interleave {s = s′} α₁ (tail α₀)

  take : ∀ ..{ℓ} {A : Set ℓ}
    → (n : Nat)
    → (α : Stream A)
    → List A
  take ze α = []
  take (su n) α = head α ∷ take n (tail α)

  drop : ∀ ..{ℓ} {A : Set ℓ}
    → (n : Nat)
    → (α : Stream A)
    → Stream A
  head (drop ze α) = head α
  head (drop (su n) α) = head (drop n (tail α))
  tail (drop ze α) = tail α
  tail (drop (su n) α) = tail (drop n (tail α))

  _++_ : ∀ ..{s ℓ} {A : Set ℓ}
    → (xs : List A)
    → (α : Stream {Size.↑ s} A)
    → Stream {Size.↑ s} A
  [] ++ α = α
  (x ∷ xs) ++ α = x ∷ (xs ++ α)

  embed : ∀ ..{ℓ} {A : Set ℓ}
    → (xs : List A)
    → (κ : A)
    → Stream A
  embed xs κ = xs ++ repeat κ

  map
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → (f : A → B)
    → (α : Stream {s} A)
    → Stream {s} B
  head (map f α) = f (head α)
  tail (map {i} f α) {j} = map {j} f (tail α {j})

  extract
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → (α : Stream A)
    → A
  extract = head

  extend
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → (k : Stream A → B)
    → ((α : Stream A) → Stream B)
  head (extend k α) = k α
  tail (extend k α) = extend k (tail α)

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
    → (α : Stream A)
    → ((n : Nat) → A)
  idx α n = head (drop n α)
