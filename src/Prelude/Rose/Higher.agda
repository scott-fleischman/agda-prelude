{-# OPTIONS --experimental-irrelevance --without-K #-}

module Prelude.Rose.Higher where

open import Agda.Primitive
open import Prelude.Applicative
  using (Applicative)
  using (pure_)
open import Prelude.Functor
  using (Functor)
open import Prelude.Monad
  using (Monad)
  using (_≫=_)
open import Prelude.Natural
open import Prelude.Size

private
  module M where
    open import Prelude.Monoidal.Unit public

mutual
  data Tree⇑ ..{s} (A : Set) (n : Nat) : Set where
    leaf⇑
      : Tree⇑ A n
    [_]
      : (ψ : Rose⇑ {s} A n)
      → Tree⇑ A n

  data Rose⇑ ..{s} (A : Set) : (n : Nat) → Set where
    node⇑
      : ∀ .{s′ : Size.< s}
      → ∀ {n}
      → (a : A)
      → (ω : Tree⇑ (Rose⇑ {s′} A (su n)) n)
      → Rose⇑ A (su n)

module Void where
  Void : (A : Set) → Set
  Void A = Rose⇑ A 0
  {-# DISPLAY Rose⇑ A 0 = Void #-}

  module _ {A : Set} where
    absurd : {X : Set} → Void A → X
    absurd ()
open Void
  using (Void)

module Unit where
  Unit : (A : Set) → Set
  Unit A = Tree⇑ A 0
  {-# DISPLAY Tree⇑ A 0 = Unit #-}

  module _ {A : Set} where
    * : Unit A
    * = leaf⇑

    bang : {X : Set} → X → Unit A
    bang _ = *
open Unit
  using (Unit)
  using (*)

module Identity where
  Identity : (A : Set) → Set
  Identity A = Rose⇑ A 1
  {-# DISPLAY Rose⇑ A 1 = Identity A #-}

  module _ {A : Set} where
    id : A → Identity A
    id x = node⇑ x *
open Identity
  using (Identity)
  using (id)

module Maybe where
  Maybe : (A : Set) → Set
  Maybe A = Tree⇑ A 1
  {-# DISPLAY Tree⇑ A 1 = Maybe A #-}

  module _ {A : Set} where
    none : Maybe A
    none = leaf⇑

    some : A → Maybe A
    some x = [ id x ]
open Maybe
  using (Maybe)
  using (none)
  using (some)

module List+ where
  List+ : (A : Set) → Set
  List+ A = Rose⇑ A 2
  {-# DISPLAY Rose⇑ A 2 = List+ A #-}

  module _ {A : Set} where
    infixr 0 _∷▸_

    []▸ : A → List+ A
    []▸ a = node⇑ a none

    _∷▸_ : A → List+ A → List+ A
    x ∷▸ xs = node⇑ x (some xs)
open List+
  using (List+)
  using ([]▸)
  using (_∷▸_)

module List where
  List : (A : Set) → Set
  List A = Tree⇑ A 2
  {-# DISPLAY Tree⇑ A 2 = List A #-}

  module _ {A : Set} where
    infixr 0 _∷_

    [] : List A
    [] = leaf⇑

    _∷_ : A → List A → List A
    x ∷ leaf⇑ = [ []▸ x ]
    x ∷ [ xs ] = [ x ∷▸ xs ]
open List
  using (List)
  using ([])
  using (_∷_)

module Positive where
  Positive : Set
  Positive = Rose⇑ M.𝟙 2

  one : Positive
  one = []▸ M.*

  succ : Positive → Positive
  succ n = M.* ∷▸ n

module Rose where
  Rose : (A : Set) → Set
  Rose A = Rose⇑ A 3
  {-# DISPLAY Rose⇑ A 3 = Rose A #-}

  module _ {A : Set} where
    rose : A → List (Rose A) → Rose A
    rose = node⇑
open Rose
  using (Rose)
  using (rose)

module Tree where
  Tree : (A : Set) → Set
  Tree A = Tree⇑ A 3
  {-# DISPLAY Tree⇑ A 3 = Tree A #-}

  module _ {A : Set} where
    leaf : Tree A
    leaf = leaf⇑

    node : A → List (Rose A) → Tree A
    node x xs = [ rose x xs ]
open Tree
  using (Tree)
  using (leaf)
  using (node)

mutual
  tree-map
    : ∀ {n}
    → {A B : Set}
    → (k : A → B)
    → (Tree⇑ A n → Tree⇑ B n)
  tree-map k leaf⇑ = leaf⇑
  tree-map k [ ψ ] = [ rose-map k ψ ]

  rose-map
    : ∀ ..{s}
    → ∀ {n}
    → {A B : Set}
    → (k : A → B)
    → (Rose⇑ {s} A n → Rose⇑ {s} B n)
  rose-map k (node⇑ a ω) = node⇑ (k a) (tree-map (rose-map k) ω)

mutual
  tree-rose-∷
    : ∀ {n}
    → {A : Set}
    → A
    → Tree⇑ (Rose⇑ A (su n)) n
    → Tree⇑ (Rose⇑ A (su n)) n
  tree-rose-∷ {ze} v ω = ω
  tree-rose-∷ {su n} v leaf⇑ = [ node⇑ (node⇑ v leaf⇑) leaf⇑ ]
  tree-rose-∷ {su n} v [ node⇑ ψ ω ] = [ node⇑ (node⇑ v [ node⇑ ψ leaf⇑ ]) ω ]

  tree-∷
    : ∀ {n}
    → {A : Set}
    → A
    → Tree⇑ A (su (su n))
    → Tree⇑ A (su (su n))
  tree-∷ v leaf⇑ = [ node⇑ v leaf⇑ ]
  tree-∷ v [ node⇑ a ω ] = [ node⇑ v (tree-rose-∷ v ω) ]

mutual
  rose-rose-++
    : ∀ {n}
    → {A : Set}
    → Rose⇑ (Rose⇑ A (su n)) n
    → Rose⇑ (Rose⇑ A (su n)) n
    → Rose⇑ (Rose⇑ A (su n)) n
  rose-rose-++ (node⇑ ψ₀ ω₀) (node⇑ ψ₁ ω₁) = node⇑ (rose-++ ψ₀ ψ₁) (tree-rose-++ ω₀ ω₁)

  rose-tree-++
    : ∀ {n}
    → {A : Set}
    → Rose⇑ (Tree⇑ A (su n)) n
    → Rose⇑ (Tree⇑ A (su n)) n
    → Rose⇑ (Tree⇑ A (su n)) n
  rose-tree-++ (node⇑ ψ₀ ω₀) (node⇑ ψ₁ ω₁) = node⇑ (tree-++ ψ₀ ψ₁) (tree-rose-++ ω₀ ω₁)

  tree-rose-++
    : ∀ {n}
    → {A : Set}
    → Tree⇑ (Rose⇑ A (su n)) n
    → Tree⇑ (Rose⇑ A (su n)) n
    → Tree⇑ (Rose⇑ A (su n)) n
  tree-rose-++ leaf⇑ ys = ys
  tree-rose-++ xs leaf⇑ = xs
  tree-rose-++ [ ψ₀ ] [ ψ₁ ] = [ rose-rose-++ ψ₀ ψ₁ ]

  tree-tree-++
    : ∀ {n}
    → {A : Set}
    → Tree⇑ (Tree⇑ A (su n)) n
    → Tree⇑ (Tree⇑ A (su n)) n
    → Tree⇑ (Tree⇑ A (su n)) n
  tree-tree-++ leaf⇑ ys = ys
  tree-tree-++ xs leaf⇑ = xs
  tree-tree-++ [ ψ₀ ] [ ψ₁ ] = [ rose-tree-++ ψ₀ ψ₁ ]

  rose-++
    : ∀ {n}
    → {A : Set}
    → Rose⇑ A n
    → Rose⇑ A n
    → Rose⇑ A n
  rose-++ (node⇑ a₀ ω₀) (node⇑ a₁ ω₁) = node⇑ a₀ (tree-rose-++ ω₀ (tree-rose-∷ a₁ ω₁))

  tree-++
    : ∀ {n}
    → {A : Set}
    → Tree⇑ A n
    → Tree⇑ A n
    → Tree⇑ A n
  tree-++ ω₀ leaf⇑ = ω₀
  tree-++ leaf⇑ ω₁ = ω₁
  tree-++ [ ψ₀ ] [ ψ₁ ] = [ rose-++ ψ₀ ψ₁ ]

tree-sequence
  : ∀ ..{s}
  → ∀ {n}
  → {A : Set}
  → Rose⇑ {s} (Tree⇑ A (su n)) n
  → Tree⇑ (Rose⇑ A (su n)) n
tree-sequence (node⇑ leaf⇑ ω₁) = leaf⇑
tree-sequence (node⇑ [ ψ₀ ] leaf⇑) = [ node⇑ ψ₀ leaf⇑ ]
tree-sequence (node⇑ [ ψ₀ ] [ ψ₁ ]) = [ node⇑ ψ₀ (tree-sequence (rose-map tree-sequence ψ₁)) ]

rose-pure
  : ∀ {n}
  → {A : Set}
  → A
  → Rose⇑ A (su n)
rose-pure a = node⇑ a leaf⇑

rose-bind
  : ∀ ..{s₀ s₁}
  → ∀ {n}
  → {A B : Set}
  → (A → Rose⇑ {s₀} B n)
  → (Rose⇑ {s₁} A n → Rose⇑ B n)
rose-bind {n = ze}   k ()
rose-bind {n = su n} k (node⇑ a₀ ω₀) with k a₀
… | node⇑ a₁ ω₁ = node⇑ a₁ (tree-rose-++ ω₁ (tree-map (rose-bind k) ω₀))

tree-pure
  : ∀ {n}
  → {A : Set}
  → A
  → Tree⇑ A (su n)
tree-pure a = [ rose-pure a ]

tree-bind
  : ∀ ..{s₀ s₁}
  → ∀ {n}
  → {A B : Set}
  → (A → Tree⇑ {s₀} B n)
  → (Tree⇑ {s₁} A n → Tree⇑ B n)
tree-bind k leaf⇑ = leaf⇑
tree-bind k [ node⇑ a₀ leaf⇑  ] = k a₀
tree-bind k [ node⇑ a₀ [ ψ₀ ] ] with k a₀
… | leaf⇑ = leaf⇑
… | [ node⇑ a₁ ω₁ ] =
  [
    node⇑ a₁
      (tree-rose-++
        ω₁
        (tree-sequence (rose-map (λ x → tree-bind k [ x ]) ψ₀)))
  ]

instance
  rose-functor
    : ∀ {n}
    → Functor (λ X → Rose⇑ X n)
  Functor.map rose-functor = rose-map

  rose-monad
    : ∀ {n}
    → Monad (λ X → Rose⇑ X (su n))
  Monad.return rose-monad = rose-pure
  Monad.bind rose-monad = rose-bind

  rose-applicative
    : ∀ {n}
    → Applicative (λ X → Rose⇑ X (su n))
  rose-applicative = Monad.applicative rose-monad

instance
  tree-functor : ∀ {n} → Functor (λ X → Tree⇑ X n)
  Functor.map tree-functor = tree-map

  tree-monad
    : ∀ {n}
    → Monad (λ X → Tree⇑ X (su n))
  Monad.return tree-monad = tree-pure
  Monad.bind tree-monad = tree-bind

  tree-applicative
    : ∀ {n}
    → Applicative (λ X → Tree⇑ X (su n))
  tree-applicative = Monad.applicative tree-monad
