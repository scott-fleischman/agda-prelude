{-# OPTIONS --without-K #-}

module Prelude.Antifounded where

open import Agda.Primitive
open import Prelude.Algebra
open import Prelude.Coalgebra
open import Prelude.Container
open import Prelude.Coproduct.Indexed
open import Prelude.Diagonal
open import Prelude.Families
open import Prelude.Functor
open import Prelude.Nat
open import Prelude.One
open import Prelude.Product.Indexed
open import Prelude.Size
open import Prelude.Wellfounded

module M where
  record M ..{s} (Σ : Con) : Set where
    coinductive
    constructor inf
    field
      head : Con.op Σ
      tail : ∀ {s′ : Size.< s} → Con.ar Σ head → M {s′} Σ

  module _ {Σ : Con} where
    from : CoAlg Con.⟦ Σ ⟧◃_
    from = CoAlg.Ψ act where
      act : M Σ → Con.⟦ Σ ⟧◃ M Σ
      act = Σ.⟨ M.head , (λ x → M.tail x) ⟩

    into : Alg Con.⟦ Σ ⟧◃_
    into = Alg.Ψ act where
      act : Con.⟦ Σ ⟧◃ M Σ → M Σ
      act (head Σ., tail) = inf head tail

    iter
      : (ψ : CoAlg Con.⟦ Σ ⟧◃_)
      → ((x : CoAlg.car ψ) → M Σ)
    M.head (iter ψ x) = Σ.fst (CoAlg.act ψ x)
    M.tail (iter ψ x) = λ α → iter ψ (Σ.snd (CoAlg.act ψ x) α)

  emb : ∀ ..{s} {Σ} → W {s} Σ → M {s} Σ
  emb {s}{Σ} = iter (CoAlg.Ψ act) where
    act : W {s} Σ → Con.⟦ Σ ⟧◃ W {s} Σ
    act (W.sup {s′} π₀ π₁) = π₀ Σ., π₁

open M public
  using (M)
  hiding (module M)
