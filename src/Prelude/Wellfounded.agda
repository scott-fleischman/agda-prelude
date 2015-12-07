module Prelude.Wellfounded where

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

module W where
  data W ..{s} (Σ : Con) : Set where
    sup
      : ∀ ..{s′ : Size.< s}
      → (π₀ : Con.op Σ)
      → (π₁ : Con.ar Σ π₀ → W {s′} Σ)
      → W {s} Σ

  module _ ..{s} {Σ : Con} where
    head : W {s} Σ → Con.op Σ
    head (sup π₀ _) = π₀

    tail
      : (w : W {s} Σ)
      → ∀ ..{s′ : Size.< s}
      → Con.ar Σ (head w)
      → W Σ
    tail (sup _ tail) = tail

  module _ {Σ : Con} where
    from : CoAlg Con.⟦ Σ ⟧◃_
    from = CoAlg.Ψ act where
      act : W Σ → Con.⟦ Σ ⟧◃ W Σ
      act (sup π₀ π₁) = (π₀ Σ., π₁)

    into : Alg Con.⟦ Σ ⟧◃_
    into = Alg.Ψ act where
      act : Con.⟦ Σ ⟧◃ W Σ → W Σ
      act (π₀ Σ., π₁) = sup π₀ π₁

    iter
      : ∀ ..{s}
      → (ψ : Alg Con.⟦ Σ ⟧◃_)
      → (W {s} Σ → Alg.car ψ)
    iter ψ (sup ϑ κ) = Alg.act ψ (ϑ Σ., iter ψ Π.<∘ κ)

open W public
  using (W)
  hiding (module W)
