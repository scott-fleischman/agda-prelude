{-# OPTIONS --without-K #-}

module Prelude.Signature.Tree.Wellfounded where

open import Agda.Primitive
open import Prelude.Algebra
open import Prelude.Coalgebra
open import Prelude.Coproduct.Indexed
open import Prelude.Diagonal
open import Prelude.Families
open import Prelude.Function
open import Prelude.Functor
open import Prelude.Natural
open import Prelude.Product.Indexed
open import Prelude.Signature
open import Prelude.Size
open import Prelude.Unit

module W where
  data W ..{s} (Σ : Sig) : Set where
    sup
      : ∀ ..{s′ : Size.< s}
      → (π₀ : Sig.op Σ)
      → (π₁ : Sig.ar Σ π₀ → W {s′} Σ)
      → W {s} Σ

  module _ ..{s} {Σ : Sig} where
    head : W {s} Σ → Sig.op Σ
    head (sup π₀ _) = π₀

    tail
      : (w : W {s} Σ)
      → ∀ ..{s′ : Size.< s}
      → Sig.ar Σ (head w)
      → W Σ
    tail (sup _ tail) = tail

  module _ {Σ : Sig} where
    from : CoAlg ⟦ Σ ⟧◃
    CoAlg.car from = W Σ
    CoAlg.act from (sup ϑ α) = (ϑ Σ., α)

    into : Alg ⟦ Σ ⟧◃
    Alg.car into = W Σ
    Alg.act into (ϑ Σ., α) = sup ϑ α

    iter
      : ∀ ..{s}
      → (ψ : Alg ⟦ Σ ⟧◃)
      → (W {s} Σ → Alg.car ψ)
    iter ψ (sup ϑ κ) = Alg.act ψ (ϑ Σ., iter ψ ⇒.<∘ κ)

open W public
  using (W)
  hiding (module W)
