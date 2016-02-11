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

infixl 0 _∷_

private
  module M where
    open import Prelude.Monoidal.Unit public

mutual
  data Rose⇑ ..{s} (A : Set) : (n : Nat) → Set where
    _∷_
      : ∀ .{s′ : Size.< s}
      → ∀ {n}
      → (a : A)
      → (ω : Tree⇑ (Rose⇑ {s′} A (su n)) n)
      → Rose⇑ A (su n)

  data Tree⇑ ..{s} (A : Set) (n : Nat) : Set where
    []  : Tree⇑ A n
    [_] : (ψ : Rose⇑ {s} A n) → Tree⇑ A n

Rose[_] : ∀ (n : Nat) ..{s} (A : Set) → Set
Rose[ n ] {s} A = Rose⇑ {s} A n
{-# DISPLAY Rose⇑ {s} A n = Rose[ n ] {s} A #-}

Tree[_] : ∀ (n : Nat) ..{s} (A : Set) → Set
Tree[ n ] {s} A = Tree⇑ {s} A n
{-# DISPLAY Tree⇑ {s} A n = Tree[ n ] {s} A #-}

module Void where
  Void : (A : Set) → Set
  Void A = Rose[ 0 ] A
  {-# DISPLAY Rose⇑ A 0 = Void #-}

  module _ {A : Set} where
    absurd : {X : Set} → Void A → X
    absurd ()
open Void
  using (Void)

module Unit where
  Unit : (A : Set) → Set
  Unit A = Tree[ 0 ] A
  {-# DISPLAY Tree⇑ A 0 = Unit #-}

  module _ {A : Set} where
    * : Unit A
    * = []

    bang : {X : Set} → X → Unit A
    bang _ = *
open Unit
  using (Unit)
  using (*)

module Identity where
  Identity : (A : Set) → Set
  Identity A = Rose[ 1 ] A
  {-# DISPLAY Rose⇑ A 1 = Identity A #-}

  module _ {A : Set} where
    id : A → Identity A
    id x = x ∷ *
open Identity
  using (Identity)
  using (id)

module Maybe where
  Maybe : (A : Set) → Set
  Maybe A = Tree[ 1 ] A
  {-# DISPLAY Tree⇑ A 1 = Maybe A #-}

  module _ {A : Set} where
    none : Maybe A
    none = []

    some : A → Maybe A
    some x = [ id x ]
open Maybe
  using (Maybe)
  using (none)
  using (some)

module List+ where
  List+ : (A : Set) → Set
  List+ A = Rose[ 2 ] A
  {-# DISPLAY Rose⇑ A 2 = List+ A #-}

  module _ {A : Set} where
    infixr 0 _∷+_

    []+ : A → List+ A
    []+ a = a ∷ none

    _∷+_ : A → List+ A → List+ A
    x ∷+ xs = x ∷ some xs
open List+
  using (List+)
  using ([]+)
  using (_∷+_)

module List where
  List : (A : Set) → Set
  List A = Tree[ 2 ] A
  {-# DISPLAY Tree⇑ A 2 = List A #-}

  module _ {A : Set} where
    infixr 0 _∷·_

    []· : List A
    []· = []

    _∷·_ : A → List A → List A
    x ∷· [] = [ []+ x ]
    x ∷· [ xs ] = [ x ∷+ xs ]
open List
  using (List)
  using ([]·)
  using (_∷·_)

module Positive where
  Positive : Set
  Positive = Rose[ 2 ] M.𝟙

  one : Positive
  one = []+ M.*

  succ : Positive → Positive
  succ n = M.* ∷+ n

module Rose where
  Rose : (A : Set) → Set
  Rose A = Rose[ 3 ] A
  {-# DISPLAY Rose⇑ A 3 = Rose A #-}

  module _ {A : Set} where
    pattern rose x xs = x ∷ xs
open Rose
  using (Rose)
  using (rose)

module Tree where
  Tree : (A : Set) → Set
  Tree A = Tree[ 3 ] A
  {-# DISPLAY Tree⇑ A 3 = Tree A #-}

  module _ {A : Set} where
    leaf : Tree A
    leaf = []

    node : A → List (Rose A) → Tree A
    node x xs = [ rose x xs ]
open Tree
  using (Tree)
  using (leaf)
  using (node)

mutual
  tree-map
    : ∀ ..{s}
    → ∀ {n}
    → {A B : Set}
    → (k : A → B)
    → (Tree[ n ] {s} A → Tree[ n ] {s} B)
  tree-map k [] = []
  tree-map k [ ψ ] = [ rose-map k ψ ]

  rose-map
    : ∀ ..{s}
    → ∀ {n}
    → {A B : Set}
    → (k : A → B)
    → (Rose[ n ] {s} A → Rose[ n ] {s} B)
  rose-map k (a ∷ ω) = k a ∷ tree-map (rose-map k) ω

mutual
  tree-rose-∷
    : ∀ {n}
    → {A : Set}
    → A
    → Tree[ n ] (Rose[ su n ] A)
    → Tree[ n ] (Rose[ su n ] A)
  tree-rose-∷ {ze} v ω = ω
  tree-rose-∷ {su n} v [] = [ v ∷ [] ∷ [] ]
  tree-rose-∷ {su n} v [ ψ ∷ ω ] = [ v ∷ [ ψ ∷ [] ] ∷ ω ]

  tree-∷
    : ∀ {n}
    → {A : Set}
    → A
    → Tree[ su su n ] A
    → Tree[ su su n ] A
  tree-∷ v [] = [ v ∷ [] ]
  tree-∷ v [ a ∷ ω ] = [ v ∷ tree-rose-∷ v ω ]

mutual
  rose-rose-++
    : ∀ {n}
    → {A : Set}
    → Rose[ n ] (Rose[ su n ] A)
    → Rose[ n ] (Rose[ su n ] A)
    → Rose[ n ] (Rose[ su n ] A)
  rose-rose-++ (ψ₀ ∷ ω₀) (ψ₁ ∷ ω₁) = rose-++ ψ₀ ψ₁ ∷ tree-rose-++ ω₀ ω₁

  rose-tree-++
    : ∀ {n}
    → {A : Set}
    → Rose[ n ] (Tree[ su n ] A)
    → Rose[ n ] (Tree[ su n ] A)
    → Rose[ n ] (Tree[ su n ] A)
  rose-tree-++ (ψ₀ ∷ ω₀) (ψ₁ ∷ ω₁) = tree-++ ψ₀ ψ₁ ∷ tree-rose-++ ω₀ ω₁

  tree-rose-++
    : ∀ {n}
    → {A : Set}
    → Tree[ n ] (Rose[ su n ] A)
    → Tree[ n ] (Rose[ su n ] A)
    → Tree[ n ] (Rose[ su n ] A)
  tree-rose-++ [] ys = ys
  tree-rose-++ xs [] = xs
  tree-rose-++ [ ψ₀ ] [ ψ₁ ] = [ rose-rose-++ ψ₀ ψ₁ ]

  tree-tree-++
    : ∀ {n}
    → {A : Set}
    → Tree[ n ] (Tree[ su n ] A)
    → Tree[ n ] (Tree[ su n ] A)
    → Tree[ n ] (Tree[ su n ] A)
  tree-tree-++ [] ys = ys
  tree-tree-++ xs [] = xs
  tree-tree-++ [ ψ₀ ] [ ψ₁ ] = [ rose-tree-++ ψ₀ ψ₁ ]

  rose-++
    : ∀ {n}
    → {A : Set}
    → Rose[ n ] A
    → Rose[ n ] A
    → Rose[ n ] A
  rose-++ (a₀ ∷ ω₀) (a₁ ∷ ω₁) = a₀ ∷ tree-rose-++ ω₀ (tree-rose-∷ a₁ ω₁)

  tree-++
    : ∀ {n}
    → {A : Set}
    → Tree[ n ] A
    → Tree[ n ] A
    → Tree[ n ] A
  tree-++ ω₀ [] = ω₀
  tree-++ [] ω₁ = ω₁
  tree-++ [ ψ₀ ] [ ψ₁ ] = [ rose-++ ψ₀ ψ₁ ]

tree-sequence
  : ∀ ..{s}
  → ∀ {n}
  → {A : Set}
  → Rose[ n ] {s} (Tree[ su n ] A)
  → Tree[ n ] (Rose[ su n ] A)
tree-sequence ([] ∷ ω₁) = []
tree-sequence ([ ψ₀ ] ∷ []) = [ ψ₀ ∷ [] ]
tree-sequence ([ ψ₀ ] ∷ [ ψ₁ ]) = [ ψ₀ ∷ tree-sequence (rose-map tree-sequence ψ₁) ]

rose-pure
  : ∀ {n}
  → {A : Set}
  → A
  → Rose[ su n ] A
rose-pure a = a ∷ []

rose-bind
  : ∀ ..{s₀ s₁}
  → ∀ {n}
  → {A B : Set}
  → (A → Rose[ n ] {s₀} B)
  → (Rose[ n ] {s₁} A → Rose[ n ] B)
rose-bind {n = ze} k ()
rose-bind {n = su n} k (a₀ ∷ ω₀) with k a₀
… | a₁ ∷ ω₁ = a₁ ∷ tree-rose-++ ω₁ (tree-map (rose-bind k) ω₀)

tree-pure
  : ∀ {n}
  → {A : Set}
  → A
  → Tree[ su n ] A
tree-pure a = [ rose-pure a ]

tree-bind
  : ∀ ..{s₀ s₁}
  → ∀ {n}
  → {A B : Set}
  → (A → Tree[ n ] {s₀} B)
  → (Tree[ n ] {s₁} A → Tree[ n ] B)
tree-bind k [] = []
tree-bind k [ a₀ ∷ [] ] = k a₀
tree-bind k [ a₀ ∷ [ ψ₀ ] ] with k a₀
… | [] = []
… | [ a₁ ∷ ω₁ ] =
  [
    a₁ ∷
      (tree-rose-++
        ω₁
        (tree-sequence (rose-map (λ x → tree-bind k [ x ]) ψ₀)))
  ]

instance
  rose-functor
    : ∀ {n}
    → Functor Rose[ n ]
  Functor.map rose-functor = rose-map

  rose-monad
    : ∀ {n}
    → Monad Rose[ su n ]
  Monad.return rose-monad = rose-pure
  Monad.bind rose-monad = rose-bind

  rose-applicative
    : ∀ {n}
    → Applicative Rose[ su n ]
  rose-applicative = Monad.applicative rose-monad

instance
  tree-functor
    : ∀ {n}
    → Functor Tree[ n ]
  Functor.map tree-functor = tree-map

  tree-monad
    : ∀ {n}
    → Monad Tree[ su n ]
  Monad.return tree-monad = tree-pure
  Monad.bind tree-monad = tree-bind

  tree-applicative
    : ∀ {n}
    → Applicative Tree[ su n ]
  tree-applicative = Monad.applicative tree-monad
