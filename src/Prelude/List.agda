{-# OPTIONS --experimental-irrelevance --without-K #-}

module Prelude.List where

open import Agda.Primitive
open import Prelude.Decidable
open import Prelude.Applicative
  using (Applicative)
open import Prelude.Functor
  using (Functor)
open import Prelude.Monad
  using (Monad)
  using (bind)
  using (_≫=_)
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Void
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Natural
open import Prelude.Size

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
    : ∀ ..{s ℓ}
    → {A : Set ℓ}
    → List {s} A
    → List {s} A
    → List {Size.∞} A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  len
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → List A → Nat
  len [] = ze
  len (_ ∷ xs) = su (len xs)

  map
    : ∀ .{s}..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}{B : Set ℓ₁}
    → (A → B)
    → List {s} A
    → List {s} B
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  pure_
    : ∀ ..{ℓ} {A : Set ℓ}
    → A → List A
  pure_ = _∷ []

  bind*
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Set ℓ₀}{B : Set ℓ₁}
    → (A → List {s} B)
    → (List {s} A → List {Size.∞} B)
  bind* k [] = []
  bind* k (x ∷ xs) = k x ++ bind* k xs

  instance
    functor : ∀ ..{ℓ} → Functor (List {ℓ = ℓ})
    Functor.map functor = map

    monad : ∀ ..{ℓ} → Monad (List {ℓ = ℓ})
    Monad.return monad = pure_
    Monad.bind monad = bind*

    applicative : ∀ ..{ℓ} → Applicative (List {ℓ = ℓ})
    applicative = Monad.applicative monad

  rep
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → Nat
    → A
    → List A
  rep (ze) a = []
  rep (su n) a = a ∷ rep n a

  module ⊢ where
    open import Prelude.Path
    open import Prelude.Monoidal.Exponential

    λ⇒
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → ([] ++ xs) ≡ xs
    λ⇒ xs = ≡.idn

    λ⇐
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → xs ≡ ([] ++ xs)
    λ⇐ [] = ≡.idn
    λ⇐ (x ∷ xs) = ≡.ap¹ (_∷_ x) (λ⇐ xs)

    ρ⇒
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → (xs ++ []) ≡ xs
    ρ⇒ [] = ≡.idn
    ρ⇒ (x ∷ xs) = ≡.ap¹ (_∷_ x) (ρ⇒ xs)

    ρ⇐
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → xs ≡ (xs ++ [])
    ρ⇐ [] = ≡.idn
    ρ⇐ (x ∷ xs) = ≡.ap¹ (_∷_ x) (ρ⇐ xs)

    α⇒
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → {ys zs : List A}
      → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
    α⇒ [] = ≡.idn
    α⇒ (x ∷ xs) = ≡.ap¹ (_∷_ x) (α⇒ xs)

    α⇐
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → {ys zs : List A}
      → (xs ++ (ys ++ zs)) ≡ ((xs ++ ys) ++ zs)
    α⇐ [] = ≡.idn
    α⇐ (x ∷ xs) = ≡.ap¹ (_∷_ x) (α⇐ xs)

    map-↻
      : {A : Set}
      → {xs : List A}
      → xs ≡ map ⇒.↻ xs
    map-↻ {xs = []} =
      ≡.idn
    map-↻ {A}{xs = x ∷ xs} =
      ≡.ap¹ (_∷_ x) map-↻

    map-⟔
      : {A B C : Set}
      → {xs : List A}
      → {f : A → B}
      → {g : B → C}
      → map g (map f xs) ≡ map (g ⇒.⟔ f) xs
    map-⟔ {xs = []}{f}{g} =
      ≡.idn
    map-⟔ {xs = x ∷ xs}{f}{g} =
      ≡.ap¹ (_∷_ (g (f x))) map-⟔

    map-⟓
      : {A B C : Set}
      → {xs : List A}
      → {f : A → B}
      → {g : B → C}
      → map g (map f xs) ≡ map (f ⇒.⟓ g) xs
    map-⟓ = map-⟔

  data ◇ ..{s}..{ℓ₀ ℓ₁}
    {A : Set ℓ₀}
    (φ : A → Set ℓ₁)
    : List A
    → Set (ℓ₀ ⊔ ℓ₁)
    where
    stop
      : ∀ {x xs}
      → φ x
      → ◇ φ (x ∷ xs)
    step
      : ∀ .{s′ : Size.< s}
      → ∀ {x xs}
      → ◇ {s′} φ xs
      → ◇ φ (x ∷ xs)

  data □ ..{s}..{ℓ₀ ℓ₁}
    {A : Set ℓ₀}
    (φ : A → Set ℓ₁)
    : List A
    → Set (ℓ₀ ⊔ ℓ₁)
    where
    stop
      : □ φ []
    step
      : ∀ .{s′ : Size.< s}
      → ∀ {x xs}
      → φ x
      → □ {s′} φ xs
      → □ φ (x ∷ xs)

  ◇?
    : ∀ .{s}..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {Φ : A → Set ℓ₁}
    → (ω : ∀ a → Decidable (Φ a))
    → (xs : List {s} A)
    → Decidable (◇ Φ xs)
  ◇? ω [] = ⊕.inl λ()
  ◇? ω (x ∷ xs) with ω x
  ◇? ω (x ∷ xs) | ⊕.inr φ = ⊕.inr (stop φ)
  ◇? ω (x ∷ xs) | ⊕.inl k with ◇? ω xs
  ◇? ω (x ∷ xs) | ⊕.inl k₀ | ⊕.inl k₁ =
    ⊕.inl λ
      { (stop φ) → k₀ φ
      ; (step φ) → k₁ φ
      }
  ◇? ω (x ∷ xs) | ⊕.inl k  | ⊕.inr φ =
    ⊕.inr (step φ)

  □?
    : ∀ .{s}..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {Φ : A → Set ℓ₁}
    → (ω : ∀ a → Decidable (Φ a))
    → (xs : List {s} A)
    → Decidable (□ Φ xs)
  □? ω [] = ⊕.inr stop
  □? ω (x ∷ xs) with ω x
  □? ω (x ∷ xs) | ⊕.inl k =
    ⊕.inl λ { (step φ _) → k φ }
  □? ω (x ∷ xs) | ⊕.inr φ with □? ω xs
  □? ω (x ∷ xs) | ⊕.inr φ | ⊕.inl k =
    ⊕.inl λ { (step _ φ*) → k φ* }
  □? ω (x ∷ xs) | ⊕.inr φ | ⊕.inr φ* =
    ⊕.inr (step φ φ*)

open List public
  using (List)
  using ([])
  using (_∷_)
  hiding (module List)
