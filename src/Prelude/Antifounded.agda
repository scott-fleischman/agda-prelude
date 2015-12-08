{-# OPTIONS --without-K #-}

module Prelude.Antifounded where

open import Agda.Primitive
open import Prelude.Algebra
open import Prelude.Coalgebra
open import Prelude.Container
open import Prelude.Coproduct.Indexed
open import Prelude.Diagonal
open import Prelude.Families
open import Prelude.Function
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
      tail : ∀ ..{s′ : Size.< s} → Con.ar Σ head → M {s′} Σ

  tail#
    : ∀ ..{s} ..{s′ : Size.< s}
    → {Σ : Con}
    → (m : M {s} Σ)
    → (α : Con.ar Σ (M.head m))
    → M {s′} Σ
  tail# m = M.tail m

  inf#
    : {Σ : Con}
    → (head : Con.op Σ)
    → (tail : Con.ar Σ head → M Σ)
    → M Σ
  inf# head tail = inf head tail

  module _ {Σ : Con} where
    from : CoAlg ⟦ Σ ⟧◃
    CoAlg.car from = M Σ
    CoAlg.act from = Σ.⟨ M.head , tail# ⟩

    into : Alg ⟦ Σ ⟧◃
    Alg.car into = M Σ
    Alg.act into = Σ.el inf#

    iter
      : ∀ ..{s}
      → (ψ : CoAlg ⟦ Σ ⟧◃)
      → ((x : CoAlg.car ψ) → M {s} Σ)
    M.head (iter ψ x) = Σ.fst (CoAlg.act ψ x)
    M.tail (iter ψ x) = iter ψ ⇒.<∘ Σ.snd (CoAlg.act ψ x)

  emb : ∀ ..{s} {Σ} → W {s} Σ → M {s} Σ
  emb {s}{Σ} = iter coalg where
    coalg : CoAlg ⟦ Σ ⟧◃
    CoAlg.car coalg = W Σ
    CoAlg.act coalg (W.sup ϑ α) = (ϑ Σ., α)

open M public
  using (M)
  hiding (module M)
