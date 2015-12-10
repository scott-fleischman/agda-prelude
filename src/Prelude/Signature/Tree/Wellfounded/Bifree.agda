{-# OPTIONS --without-K #-}

module Prelude.Signature.Tree.Wellfounded.Bifree where

open import Agda.Primitive
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Product
open import Prelude.Signature
open import Prelude.Signature.Tree.Wellfounded
open import Prelude.Void

data Fix : Set where
  + × : Fix

biprod : Fix → (Σ₀ Σ₁ : Sig) → Sig
biprod + Σ₀ Σ₁ = Σ₀ Sig.+◃ Σ₁
biprod × Σ₀ Σ₁ = Σ₀ Sig.×◃ Σ₁

bifree : (⊛ : Fix) (Σ : Sig) (A : Set) → Set
bifree ⊛ Σ A = W (biprod ⊛ (Sig.κ◃ A) Σ)

free : (Σ : Sig) (A : Set) → Set
free Σ A = bifree + Σ A

cofree : (Σ : Sig) (A : Set) → Set
cofree Σ A = bifree × Σ A

module Free where
  module π where
    pattern leaf ⊥ a = W.sup (⊕.inl a) ⊥
    pattern fork ϑ κ = W.sup (⊕.inr ϑ) κ

  leaf : {Σ : Sig} {A : Set} → A → free Σ A
  leaf {Σ = op ◃ ar} = π.leaf 𝟘.¡

  fork : {Σ : Sig} {A : Set} → Sig.⟦ Σ ⟧◃ (free Σ A) → free Σ A
  fork {Σ = op ◃ ar} = Σ.el π.fork

module Cofree where
  node : {Σ : Sig} {A : Set} → A → Sig.⟦ Σ ⟧◃ (cofree Σ A) → cofree Σ A
  node {Σ = op ◃ ar} a (ϑ Σ., ρ) = W.sup (a ⊗., ϑ) ⊕.[ 𝟘.¡ , ρ ]
