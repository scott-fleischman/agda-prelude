{-# OPTIONS --experimental-irrelevance --without-K #-}

module Prelude.Signature.Tree.Antifounded where

open import Agda.Primitive
open import Prelude.Algebra
open import Prelude.Coalgebra
open import Prelude.Families
open import Prelude.Functor
open import Prelude.Natural
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Exponential
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Monoidal.Unit
open import Prelude.Signature
open import Prelude.Signature.Tree.Wellfounded
open import Prelude.Size

module M where
  record M ..{s} (Σ : Sig) : Set where
    coinductive
    constructor inf
    field
      head : Sig.op Σ
      tail : ∀ .{s′ : Size.< s} → Sig.ar Σ head → M {s′} Σ

  tail#
    : ∀ ..{s} ..{s′ : Size.< s}
    → {Σ : Sig}
    → (m : M {s} Σ)
    → (α : Sig.ar Σ (M.head m))
    → M {s′} Σ
  tail# m = M.tail m

  inf#
    : {Σ : Sig}
    → (head : Sig.op Σ)
    → (tail : Sig.ar Σ head → M Σ)
    → M Σ
  inf# head tail = inf head tail

  module _ {Σ : Sig} where
    -- from : CoAlg ⟦ Σ ⟧◃
    -- CoAlg.car from = M Σ
    -- CoAlg.act from = Σ.⟨ M.head ▸ tail# ⟩

    into : Alg ⟦ Σ ⟧◃
    Alg.car into = M Σ
    Alg.act into = Σ.el inf#

    iter
      : ∀ ..{s}
      → (ψ : CoAlg ⟦ Σ ⟧◃)
      → ((x : CoAlg.car ψ) → M {s} Σ)
    M.head (iter ψ x) = Σ.fst (CoAlg.act ψ x)
    M.tail (iter ψ x) = iter ψ ⇒.⟔ Σ.snd (CoAlg.act ψ x)

  emb : ∀ ..{s} {Σ} → W {s} Σ → M {s} Σ
  emb {s}{Σ} = iter coalg where
    coalg : CoAlg ⟦ Σ ⟧◃
    CoAlg.car coalg = W Σ
    CoAlg.act coalg (W.sup ϑ α) = (ϑ ▸ α)

open M public
  using (M)
  hiding (module M)
