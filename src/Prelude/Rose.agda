{-# OPTIONS --without-K #-}

module Prelude.Rose where

open import Agda.Primitive
open import Prelude.Applicative
open import Prelude.Comonad
open import Prelude.Functor
  using (Functor)
open import Prelude.List
open import Prelude.Monad
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Size
open import Prelude.String

module Rose where
  data Rose ..{s ℓ} (A : Set ℓ) : Set ℓ where
    node
      : {s′ : Size.< s}
      → (hd : A)
      → (tl : List (Rose {s′} A))
      → Rose {s} A

  map : ∀ ..{s ℓ} {A B : Set ℓ}
    → (f : A → B)
    → (Rose {s} A → Rose {s} B)
  map f (node head tail) = node (f head) (List.map (map f) tail)

  return : ∀ ..{ℓ} {A : Set ℓ}
    → (x : A)
    → Rose A
  return x = node x []

  bind : ∀ ..{s₀ s₁} {ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (k : A → Rose {s₀} B)
    → ((m : Rose {s₁} A) → Rose {Size.∞} B)
  bind {B = B} k (node head tail) with k head
  … | node `head `tail = node `head (bind-tail `tail (List.map (bind k) tail))
    where
    bind-tail : List (Rose B) → List (Rose B) → List (Rose B)
    bind-tail [] ys = ys
    bind-tail (x ∷ xs) ys = x ∷ bind-tail xs ys

  extract : ∀ ..{ℓ} {A : Set ℓ} → (w : Rose A) → A
  extract (node head tail) = head

  extend : ∀ ..{s} {ℓ₀ ℓ₁} {A : Set ℓ₀} {B : Set ℓ₁}
    → (k : Rose {s} A → B)
    → ((w : Rose {s} A) → Rose {s} B)
  extend k (node head tail) =
    node (k (node head tail)) (List.map (extend k) tail)

  instance
    functor : ∀ ..{ℓ} → Functor (Rose {ℓ = ℓ})
    Functor.#.map functor = map

    monad : ∀ ..{ℓ} → Monad (Rose {ℓ = ℓ})
    Monad.#.return monad = return
    Monad.#.bind monad = bind

    applicative : ∀ ..{ℓ} → Applicative (Rose {ℓ = ℓ})
    applicative = Monad.applicative

    comonad : ∀ ..{ℓ} → Comonad (Rose {ℓ = ℓ})
    Comonad.#.extract comonad = extract
    Comonad.#.extend comonad = extend

open Rose public
  using (Rose)
  using (node)
  hiding (module Rose)
