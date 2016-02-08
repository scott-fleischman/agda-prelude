{-# OPTIONS --experimental-irrelevance #-}
module Prelude.Rose.Higher where

open import Prelude.Natural
open import Prelude.Size

private
  module M where
    open import Prelude.Monoidal.Unit public

mutual
  data Tree⇑ (A : Set) (n : Nat) : Set where
    leaf⇑
      : Tree⇑ A n
    [_]
      : (ψ : Rose⇑ A n)
      → Tree⇑ A n

  data Rose⇑ ..{s} (A : Set) : (n : Nat) → Set where
    node⇑
      : ∀ .{s′ : Size.< s}
      → ∀ {n}
      → (a : A)
      → (ω : Tree⇑ (Rose⇑ {s′} A (su n)) n)
      → Rose⇑ A (su n)

mutual
  map-tree
    : ∀ {n}
    → {A B : Set}
    → (k : A → B)
    → (Tree⇑ A n → Tree⇑ B n)
  map-tree k leaf⇑ = leaf⇑
  map-tree k [ ψ ] = [ map-rose k ψ ]

  map-rose
    : ∀ ..{s}
    → ∀ {n}
    → {A B : Set}
    → (k : A → B)
    → (Rose⇑ {s} A n → Rose⇑ {s} B n)
  map-rose k (node⇑ a ω) = node⇑ (k a) (map-tree (map-rose k) ω)

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
