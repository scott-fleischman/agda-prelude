module Prelude.Stage where

open import Agda.Primitive
open import Prelude.Functor
  using (Functor)
open import Prelude.Monad
open import Prelude.Size

mutual
  data Stage ..{s ℓ} (A : Set ℓ) : Set ℓ where
    stop : A → Stage {s} A
    hold : [Stage] {s} A → Stage {s} A

  record [Stage] ..{s ℓ} (A : Set ℓ) : Set ℓ where
    no-eta-equality
    coinductive
    constructor ι
    field
      π : ..{s′ : Size.< s} → Stage {s′} A
open [Stage]

loop : ∀ ..{ℓ} {A : Set ℓ} → [Stage] A
π loop = hold loop

wait : ∀ ..{ℓ} {A : Set ℓ} → Stage A → Stage A
wait x = hold (ι x)

step : ∀ ..{ℓ} {A : Set ℓ} → Stage A → Stage A
step (stop x) = stop x
step (hold m) = π m

return : ∀ ..{s ℓ} {A : Set ℓ} → A → Stage {s} A
return = stop

mutual
  map
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Set ℓ₀}{B : Set ℓ₁}
    → (A → B)
    → (Stage {s} A → Stage {s} B)
  map f (stop x) = stop (f x)
  map f (hold m) = hold ([map] f m)

  [map]
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Set ℓ₀}{B : Set ℓ₁}
    → (A → B)
    → ([Stage] {s} A → [Stage] {s} B)
  π ([map] f m) = map f (π m)

mutual
  bind
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Set ℓ₀}{B : Set ℓ₁}
    → (A → Stage {s} B)
    → (Stage {s} A → Stage {s} B)
  bind k (stop x) = k x
  bind k (hold m) = hold ([bind] k m)

  [bind]
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Set ℓ₀}{B : Set ℓ₁}
    → (A → Stage {s} B)
    → ([Stage] {s} A → [Stage] {s} B)
  π ([bind] k m) = bind k (π m)

instance
  functor : ∀ ..{s ℓ} → Functor (Stage {s}{ℓ})
  Functor.#.map functor = map

  monad : ∀ ..{s ℓ} → Monad (Stage {s}{ℓ})
  Monad.#.return monad = return
  Monad.#.bind monad = bind
