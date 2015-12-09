{-# OPTIONS --without-K #-}

module Prelude.Bifree where

open import Agda.Primitive
open import Prelude.Container
open import Prelude.Coproduct
open import Prelude.Coproduct.Indexed
open import Prelude.Diagonal
open import Prelude.Product
open import Prelude.Void
open import Prelude.Wellfounded

data Fix : Set where
  + × : Fix

biprod : Fix → Con → Con → Con
biprod + A B = A Con.+◃ B
biprod × A B = A Con.×◃ B

bifree : (⊛ : Fix) (Σ : Con) (A : Set) → Set
bifree ⊛ Σ A = W (biprod ⊛ (Con.κ◃ A) Σ)

free : (Σ : Con) (A : Set) → Set
free Σ A = bifree + Σ A

cofree : (Σ : Con) (A : Set) → Set
cofree Σ A = bifree × Σ A

module Free where
  module π where
    pattern leaf ⊥ a = W.sup (⊕.inl a) ⊥
    pattern fork ϑ κ = W.sup (⊕.inr ϑ) κ

  leaf : {Σ : Con} {A : Set} → A → free Σ A
  leaf {Σ = op ◃ ar} = π.leaf 𝟘.¡

  fork : {Σ : Con} {A : Set} → Con.⟦ Σ ⟧◃ (free Σ A) → free Σ A
  fork {Σ = op ◃ ar} = Σ.el π.fork

module Cofree where
  node : {Σ : Con} {A : Set} → A → Con.⟦ Σ ⟧◃ (cofree Σ A) → cofree Σ A
  node {Σ = op ◃ ar} a (ϑ Σ., ρ) = W.sup (a ⊗., ϑ) ⊕.[ 𝟘.¡ , ρ ]
