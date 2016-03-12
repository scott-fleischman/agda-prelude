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
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Monoidal.Void
open import Prelude.Natural
open import Prelude.Size

module List where
  infixr 2 _∷_

  data  List ..{s ℓ} (A : Set ℓ) : Set ℓ where
    []
      : List {s} A
    _∷_
      : .{s′ : Size.< s}
      → (x : A)
      → (xs : List {s′} A)
      → List {s} A

  private
    module Ext where
      infixr 2 _++_

      _++_
        : ∀ ..{s ℓ}
        → {A : Set ℓ}
        → List {s} A
        → List {s} A
        → List {Size.∞} A
      [] ++ ys = ys
      (x ∷ xs) ++ ys = x ∷ xs ++ ys

      map
        : ∀ .{s}..{ℓ₀ ℓ₁}
        → {A : Set ℓ₀}{B : Set ℓ₁}
        → (A → B)
        → List {s} A
        → List {s} B
      map f [] = []
      map f (x ∷ xs) = f x ∷ map f xs

  module ◇ where
    open import Prelude.Monoidal.Coproduct
    open import Prelude.Monoidal.Diagonal
    open import Prelude.Families
    open import Prelude.Monoidal.Void
    open 𝟘
      using (¬_)
    open Fam
      using (_⊆_)

    data ◇ ..{s}..{ℓ₀ ℓ₁}
      {A : Set ℓ₀}
      (P : A → Set ℓ₁)
      : List A
      → Set (ℓ₀ ⊔ ℓ₁)
      where
      stop
        : ∀ {x xs}
        → (◇ε : P x)
        → ◇ P (x ∷ xs)
      step
        : ∀ .{s′ : Size.< s}
        → ∀ {x xs}
        → (◇δ : ◇ {s′} P xs)
        → ◇ P (x ∷ xs)

    map
      : ∀ ..{s}..{ℓ₀ ℓ₁}
      → {I : Set ℓ₀}
      → {F G : I → Set ℓ₁}
      → (f : F ⊆ G)
      → ◇ {s} F ⊆ ◇ {s} G
    map f (stop □ε) = stop (f □ε)
    map f (step □δ) = step (map f □δ)

    _⊢?_
      : ∀ .{s}..{ℓ₀ ℓ₁}
      → {A : Set ℓ₀}
      → {P : A → Set ℓ₁}
      → (ω : ∀ a → Decidable (P a))
      → (xs : List {s} A)
      → Decidable (◇ P xs)
    ω ⊢? [] = ⊕.inl λ()
    ω ⊢? (x ∷ xs) with ω x
    ω ⊢? (x ∷ xs) | ⊕.inr ε = ⊕.inr (stop ε)
    ω ⊢? (x ∷ xs) | ⊕.inl k with ω ⊢? xs
    ω ⊢? (x ∷ xs) | ⊕.inl k₀ | ⊕.inl k₁ =
      ⊕.inl λ
        { (stop ε) → k₀ ε
        ; (step δ) → k₁ δ
        }
    ω ⊢? (x ∷ xs) | ⊕.inl k | ⊕.inr δ =
      ⊕.inr (step δ)

    inl
      : {I : Set}
      → {P : I → Set}
      → {is js : List I}
      → ◇ P is
      → ◇ P (is Ext.++ js)
    inl (stop ε) = stop ε
    inl (step δ) = step (inl δ)

    inr
      : {I : Set}
      → {P : I → Set}
      → {is js : List I}
      → ◇ P js
      → ◇ P (is Ext.++ js)
    inr {is = []} ε = ε
    inr {is = i ∷ is} δ = step (inr {is = is} δ)

    split
      : {I : Set}
      → {P : I → Set}
      → ∀ {is js}
      → ◇ P (is Ext.++ js)
      → ◇ P is ⊕ ◇ P js
    split {is = []} (stop ε) =
      ⊕.inr (stop ε)
    split {is = []} (step δ) =
      ⊕.inr (step δ)
    split {is = i ∷ is} (stop ε) =
      ⊕.inl (stop ε)
    split {is = i ∷ is} (step δ) with split {is = is} δ
    … | ⊕.inl δ-λ = ⊕.inl (step δ-λ)
    … | ⊕.inr ε-ρ = ⊕.inr ε-ρ

    absurd
      : {I : Set}
      → (is : List I)
      → 𝟘.¬ (◇ Δ.ʲ[ 𝟘 ] is)
    absurd _ (stop ())
    absurd _ (step fs) = absurd _ fs
  open ◇ public
    hiding (module ◇)
    using (◇)

  module □ where
    open import Prelude.Families
    open import Prelude.Monoidal.Diagonal
    open import Prelude.Monoidal.Product
    open import Prelude.Monoidal.Unit
    open Fam
      using (_⊆_)

    data □ ..{s}..{ℓ₀ ℓ₁}
      {A : Set ℓ₀}
      (P : A → Set ℓ₁)
      : List A
      → Set (ℓ₀ ⊔ ℓ₁)
      where
      stop
        : □ P []
      step
        : ∀ .{s′ : Size.< s}
        → ∀ {x xs}
        → (□ε : P x)
        → (□δ : □ {s′} P xs)
        → □ P (x ∷ xs)

    map
      : ∀ ..{s}..{ℓ₀ ℓ₁}
      → {I : Set ℓ₀}
      → {F G : I → Set ℓ₁}
      → (f : F ⊆ G)
      → □ {s} F ⊆ □ {s} G
    map f (stop) = stop
    map f (step □ε □δ) = step (f □ε) (map f □δ)

    _⊢?_
      : ∀ .{s}..{ℓ₀ ℓ₁}
      → {A : Set ℓ₀}
      → {P : A → Set ℓ₁}
      → (ω : ∀ a → Decidable (P a))
      → (xs : List {s} A)
      → Decidable (□ P xs)
    ω ⊢? [] = ⊕.inr stop
    ω ⊢? (x ∷ xs) with ω x
    ω ⊢? (x ∷ xs) | ⊕.inl k =
      ⊕.inl λ { (step φ _) → k φ }
    ω ⊢? (x ∷ xs) | ⊕.inr φ with ω ⊢? xs
    ω ⊢? (x ∷ xs) | ⊕.inr φ | ⊕.inl k =
      ⊕.inl λ { (step _ φ*) → k φ* }
    ω ⊢? (x ∷ xs) | ⊕.inr φ | ⊕.inr φ* =
      ⊕.inr (step φ φ*)

    pair
      : {I : Set}
      → {P : I → Set}
      → {is js : List I}
      → □ P is
      → □ P js
      → □ P (is Ext.++ js)
    pair (□.stop) ε = ε
    pair (□.step ε δ-λ) δ-ρ = □.step ε (pair δ-λ δ-ρ)

    split
      : {I : Set}
      → {P : I → Set}
      → ∀ is {js}
      → □ P (is Ext.++ js)
      → □ P is ⊗ □ P js
    split [] δ-ρ =
      stop , δ-ρ
    split (i ∷ is) (step ε δ) with split is δ
    … | δ-λ , δ-ρ =
      step ε δ-λ , δ-ρ

    take
      : {I : Set}
      → {P : I → Set}
      → ∀ is {js}
      → □ P (is Ext.++ js)
      → □ P (is)
    take is δ = ⊗.fst (split is δ)

    drop
      : {I : Set}
      → {P : I → Set}
      → ∀ is {js}
      → □ P (is Ext.++ js)
      → □ P (js)
    drop is δ = ⊗.snd (split is δ)

    trivial
      : {I : Set}
      → (is : List I)
      → □ Δ.ʲ[ 𝟙 ] is
    trivial [] = stop
    trivial (i ∷ is) = step * (trivial is)
  open □ public
    hiding (module □)
    using (□)

  open Ext public

  len
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → List A → Nat
  len [] = ze
  len (_ ∷ xs) = su (len xs)

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
    functor
      : ∀ ..{ℓ}
      → Functor (List {ℓ = ℓ})
    Functor.map functor = map

    monad
      : ∀ ..{ℓ}
      → Monad (List {ℓ = ℓ})
    Monad.return monad = pure_
    Monad.bind monad = bind*

    applicative
      : ∀ ..{ℓ}
      → Applicative (List {ℓ = ℓ})
    applicative = Monad.applicative monad

  rep
    : ∀ ..{ℓ}
    → {A : Set ℓ}
    → Nat
    → A
    → List A
  rep (ze) a = []
  rep (su n) a = a ∷ rep n a

  zip
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → List A
    → List B
    → List (A ⊗ B)
  zip [] ys =
    []
  zip (x ∷ xs) [] =
    []
  zip (x ∷ xs) (y ∷ ys) =
    (x , y) ∷ zip xs ys

  zipAp
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → List (A → B)
    → List A
    → List B
  zipAp [] xs =
    []
  zipAp (f ∷ fs) [] =
    []
  zipAp (f ∷ fs) (x ∷ xs) =
    f x ∷ zipAp fs xs

  zipWith
    : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → {C : Set ℓ₂}
    → (f : A → B → C)
    → List A
    → List B
    → List C
  zipWith f [] ys =
    []
  zipWith f (x ∷ xs) [] =
    []
  zipWith f (x ∷ xs) (y ∷ ys) =
    f x y ∷ zipWith f xs ys

  unzip
    : ∀ ..{ℓ₀ ℓ₁}
    → {A : Set ℓ₀}
    → {B : Set ℓ₁}
    → List (A ⊗ B)
    → List A ⊗ List B
  unzip [] =
    [] , []
  unzip ((a , b) ∷ as⊗bs) =
    let (as , bs) = unzip as⊗bs in
    a ∷ as , b ∷ bs

  module ⊢ where
    open import Prelude.Path
    open import Prelude.Monoidal.Exponential

    λ⇒
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → [] ++ xs ≡ xs
    λ⇒ xs = ≡.idn

    λ⇐
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → xs ≡ [] ++ xs
    λ⇐ [] = ≡.idn
    λ⇐ (x ∷ xs) = ≡.ap¹ (_∷_ x) (λ⇐ xs)

    ρ⇒
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → xs ++ [] ≡ xs
    ρ⇒ [] = ≡.idn
    ρ⇒ (x ∷ xs) = ≡.ap¹ (_∷_ x) (ρ⇒ xs)

    ρ⇐
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → xs ≡ xs ++ []
    ρ⇐ [] = ≡.idn
    ρ⇐ (x ∷ xs) = ≡.ap¹ (_∷_ x) (ρ⇐ xs)

    α⇒
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → {ys zs : List A}
      → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    α⇒ [] = ≡.idn
    α⇒ (x ∷ xs) = ≡.ap¹ (_∷_ x) (α⇒ xs)

    α⇐
      : ∀ ..{ℓ}
      → {A : Set ℓ}
      → (xs : List A)
      → {ys zs : List A}
      → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
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

    map-++
      : {A B : Set}
      → ∀ xs {ys : List A}
      → {f : A → B}
      → map f xs ++ map f ys ≡ map f (xs ++ ys)
    map-++ [] =
      ≡.idn
    map-++ (x ∷ xs) =
      ≡.ap¹ (_∷_ _) (map-++ xs)

open List public
  using (List)
  using ([])
  using (_∷_)
  hiding (module List)
