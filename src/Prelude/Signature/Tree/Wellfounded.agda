{-# OPTIONS --experimental-irrelevance --without-K #-}

module Prelude.Signature.Tree.Wellfounded where

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
open import Prelude.Size

module W where
  data W ..{s} (Σ : Sig) : Set where
    sup
      : ∀ .{s′ : Size.< s}
      → (head : Sig.op Σ)
      → (tail : Sig.ar Σ head → W {s′} Σ)
      → W {s} Σ

  module _ ..{s} {Σ : Sig} where
    head : W {s} Σ → Sig.op Σ
    head (sup h _) = h

    tail
      : (w : W {s} Σ)
      → ∀ ..{s′ : Size.< s}
      → Sig.ar Σ (head w)
      → W Σ
    tail (sup _ t) = t

  module _ {Σ : Sig} where
    from : CoAlg ⟦ Σ ⟧◃
    CoAlg.car from = W Σ
    CoAlg.act from (sup ϑ α) = (ϑ ▸ α)

    into : Alg ⟦ Σ ⟧◃
    Alg.car into = W Σ
    Alg.act into (ϑ ▸ α) = sup ϑ α

    iter
      : ∀ ..{s}
      → (ψ : Alg ⟦ Σ ⟧◃)
      → (W {s} Σ → Alg.car ψ)
    iter ψ (sup ϑ ρ) = Alg.act ψ (ϑ ▸ iter ψ ⇒.⟔ ρ)

open W public
  using (W)
  hiding (module W)
