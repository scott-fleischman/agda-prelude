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
    : ∀ ..{ℓ}{m n}
    → {A : Set ℓ}
    → Vec A m → Vec A n
    → Vec A (m Nat.+ n)
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  map
    : ∀ .{s}..{ℓ₀ ℓ₁}{n}
    → {A : Set ℓ₀} {B : Set ℓ₁}
    → (f : A → B)
    → (Vec {s} A n → Vec {s} B n)
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  idx
    : ∀ ..{ℓ}{n}
    → {A : Set ℓ}
    → (Vec A n)
    → (Fin n → A)
  idx (x ∷ xs) ze = x
  idx (x ∷ xs) (su i) = idx xs i

  tab
    : ∀ ..{ℓ}{n}
    → {A : Set ℓ}
    → (Fin n → A) → Vec A n
  tab {n = ze} f = []
  tab {n = su n} f = f ze ∷ tab λ i → f (su i)

  head
    : ∀ ..{ℓ}{n}
    → {A : Set ℓ}
    → Vec A (su n)
    → A
  head (x ∷ xs) = x

  tail
    : ∀ ..{ℓ}{n}
    → {A : Set ℓ}
    → Vec A (su n)
    → Vec A n
  tail (x ∷ xs) = xs

  module ⊢ where
    open import Prelude.Monoidal.Exponential
    open import Prelude.Path

    ap-∷
      : ∀ ..{ℓ}{m n}
      → {A : Set ℓ}
      → {x : A}
      → (xs : Vec A m)
      → (φ : m ≡ n)
      → (x ∷ ≡.coe* (Vec A) φ xs) ≡ ≡.coe* (Vec A) (≡.ap¹ su_ φ) (x ∷ xs)
    ap-∷ xs φ rewrite φ = ≡.idn

    λ⇒
      : ∀ ..{ℓ}{n}
      → {A : Set ℓ}
      → (xs : Vec A n)
      → ([] ++ xs) ≡ xs
    λ⇒ xs = ≡.idn

    λ⇐
      : ∀ ..{ℓ}{n}
      → {A : Set ℓ}
      → (xs : Vec A n)
      → xs ≡ ([] ++ xs)
    λ⇐ xs = λ⇒ xs ≡.⁻¹

    ρ⇒
      : ∀ ..{ℓ}{n}
      → {A : Set ℓ}
      → (xs : Vec A n)
      → (xs ++ []) ≡ ≡.coe* (Vec A) Nat.⊢.ρ⇐ xs
    ρ⇒ [] =
      ≡.idn
    ρ⇒ {n = su n}(x ∷ xs) =
      ≡.ap¹ (_∷_ x) (ρ⇒ xs)
      ≡.⟓ ap-∷ xs Nat.⊢.ρ⇐

    ρ⇐
      : ∀ ..{ℓ}{n}
      → {A : Set ℓ}
      → (xs : Vec A n)
      → ≡.coe* (Vec A) Nat.⊢.ρ⇐ xs ≡ (xs ++ [])
    ρ⇐ [] =
      ≡.idn
    ρ⇐ (x ∷ xs) =
      ≡.ap¹ (_∷_ x) (ρ⇐ xs)
      ≡.⟔ ap-∷ xs Nat.⊢.ρ⇐ ≡.⁻¹

    α⇒
      : ∀ ..{ℓ}{m n o}
      → {A : Set ℓ}
      → (xs : Vec A m)
      → {ys : Vec A n}
      → {zs : Vec A o}
      → ((xs ++ ys) ++ zs) ≡ ≡.coe* (Vec A) (Nat.⊢.α⇐ m) (xs ++ (ys ++ zs))
    α⇒ [] =
      ≡.idn
    α⇒ {m = su m}(x ∷ xs){ys}{zs} =
      ≡.ap¹ (_∷_ x) (α⇒ xs)
      ≡.⟓ ap-∷ (xs ++ ys ++ zs) (Nat.⊢.α⇐ m)

    α⇐
      : ∀ ..{ℓ}{m n o}
      → {A : Set ℓ}
      → (xs : Vec A m)
      → {ys : Vec A n}
      → {zs : Vec A o}
      → ≡.coe* (Vec A) (Nat.⊢.α⇐ m) (xs ++ (ys ++ zs)) ≡ ((xs ++ ys) ++ zs)
    α⇐ [] =
      ≡.idn
    α⇐ {m = su m}(x ∷ xs){ys}{zs} =
      ≡.ap¹ (_∷_ x) (α⇐ xs)
      ≡.⟔ ap-∷ (xs ++ ys ++ zs) (Nat.⊢.α⇐ m) ≡.⁻¹

    map-↻
      : ∀ ..{ℓ}{n}
      → {A : Set ℓ}
      → {xs : Vec A n}
      → xs ≡ map ⇒.↻ xs
    map-↻ {xs = []} =
      ≡.idn
    map-↻ {n = su n}{A}{xs = x ∷ xs} =
      ≡.ap¹ (_∷_ x) map-↻

    map-⟔
      : ∀ ..{ℓ₀ ℓ₁ ℓ₂}{n}
      → {A : Set ℓ₀}{B : Set ℓ₁}{C : Set ℓ₂}
      → {xs : Vec A n}
      → {f : A → B}
      → {g : B → C}
      → map g (map f xs) ≡ map (g ⇒.⟔ f) xs
    map-⟔ {xs = []}{f}{g} =
      ≡.idn
    map-⟔ {xs = x ∷ xs}{f}{g} =
      ≡.ap¹ (_∷_ (g (f x))) map-⟔

    map-⟓
      : ∀ ..{ℓ₀ ℓ₁ ℓ₂}{n}
      → {A : Set ℓ₀}{B : Set ℓ₁}{C : Set ℓ₂}
      → {A B C : Set}
      → {xs : Vec A n}
      → {f : A → B}
      → {g : B → C}
      → map g (map f xs) ≡ map (f ⇒.⟓ g) xs
    map-⟓ = map-⟔

open Vec public
  hiding (module Vec)
  using (Vec)
  using ([])
  using (_∷_)
