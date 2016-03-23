{-# OPTIONS --without-K #-}

module Prelude.Natural where

open import Agda.Primitive
  hiding (_⊔_)
open import Prelude.Decidable
open import Prelude.Monoidal
  hiding (*)
open import Prelude.Path
  hiding (refl)
open import Prelude.Size

module Nat where
  infix 0 _≟_
  infix 0 _≤?_
  infix 0 _<?_
  infix 0 _≥?_
  infix 0 _>?_

  open import Agda.Builtin.Nat public
    using (Nat)
    using (_+_)
    using (_-_)
    renaming (zero to ze; suc to su_)

  record ⊆ (A : Set) : Set where
    no-eta-equality
    field
      fromNat : Nat → A
  open ⊆ ⦃ … ⦄ public
  {-# BUILTIN FROMNAT fromNat #-}

  instance
    nat⊆nat : ⊆ Nat
    nat⊆nat = record { fromNat = λ x → x }

  pred : Nat → Nat
  pred ze = ze
  pred (su n) = n

  module ≤ where
    infix 0 _≤_
    infix 0 _<_
    infix 0 _≥_
    infix 0 _>_

    data _≤_ (m : Nat) : Nat → Set where
      stop : m ≤ m
      step : ∀ {n} (φ : m ≤ n) → m ≤ su n

    _<_ : (m n : Nat) → Set
    m < n = su m ≤ n

    _≥_ : (n m : Nat) → Set
    n ≥ m = m ≤ n

    _>_ : (n m : Nat) → Set
    n > m = n ≥ su m

    idn : ∀ {n} → n ≤ n
    idn = stop

    cmp : ∀ {m n o} → n ≤ o → m ≤ n → m ≤ o
    cmp (stop) p = p
    cmp (step q) p = step (cmp q p)

    seq : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
    seq p q = cmp q p

    z≤n : ∀ {n} → 0 ≤ n
    z≤n {ze} = stop
    z≤n {su n} = step z≤n

    s≤s : ∀ {m n} → m ≤ n → su m ≤ su n
    s≤s stop = stop
    s≤s (step φ) = step (s≤s φ)

    p≤p : ∀ {m n} → su m ≤ su n → m ≤ n
    p≤p stop = stop
    p≤p (step stop) = step stop
    p≤p (step (step φ)) = step (p≤p (step φ))
  open ≤ public
    hiding (module _≤_)
    using (_≤_)
    using (_<_)
    using (_≥_)
    using (_>_)
    using (stop)
    using (step)
  open ≤

  min : (m n : Nat) → Nat
  min ze n = ze
  min m ze = ze
  min (su m) (su n) = su (min m n)

  _⊓_ = min
  {-# DISPLAY min m n = m ⊓ n #-}

  max : (m n : Nat) → Nat
  max ze n = n
  max m ze = m
  max (su m) (su n) = su (max m n)

  _⊔_ = max
  {-# DISPLAY max m n = m ⊔ n #-}

  _≟_ : (m n : Nat) → Decidable (m ≡ n)
  ze ≟ ze = ⊕.inr ≡.idn
  ze ≟ su n = ⊕.inl λ()
  su m ≟ ze = ⊕.inl λ()
  su m ≟ su n with m ≟ n
  su m ≟ su n | ⊕.inl k =
    ⊕.inl (k ⇒.⟔ λ φ → ≡.coe* (λ x → m ≡ pred x) φ ≡.idn)
  su m ≟ su n | ⊕.inr φ =
    ⊕.inr (≡.ap¹ su_ φ)

  _≤?_ : (m n : Nat) → Decidable (m ≤ n)
  ze ≤? n = ⊕.inr z≤n
  su m ≤? ze = ⊕.inl λ()
  su m ≤? su n with m ≤? n
  su m ≤? su n | ⊕.inl k =
    ⊕.inl (k ⇒.⟔ p≤p)
  su m ≤? su n | ⊕.inr φ =
    ⊕.inr (s≤s φ)

  _<?_ : (m n : Nat) → Decidable (m < n)
  m <? n = su m ≤? n

  _≥?_ : (n m : Nat) → Decidable (n ≥ m)
  n ≥? m = m ≤? n

  _>?_ : (n m : Nat) → Decidable (n > m)
  n >? m = n ≥? su m

  module ⊢ where
    open import Prelude.Path

    λ⇒
      : ∀ {n}
      → 0 + n ≡ n
    λ⇒ = ≡.idn

    λ⇐
      : ∀ {n}
      → n ≡ 0 + n
    λ⇐ {ze} = ≡.idn
    λ⇐ {su n} = ≡.ap¹ su_ λ⇐

    ρ⇒
      : ∀ {n}
      → n + 0 ≡ n
    ρ⇒ {ze} = ≡.idn
    ρ⇒ {su n} = ≡.ap¹ su_ ρ⇒

    ρ⇐
      : ∀ {n}
      → n ≡ n + 0
    ρ⇐ {ze} = ≡.idn
    ρ⇐ {su n} = ≡.ap¹ su_ ρ⇐

    α⇒
      : ∀ m {n o}
      → (m + n) + o ≡ m + (n + o)
    α⇒ ze = ≡.idn
    α⇒ (su m) = ≡.ap¹ su_ (α⇒ m)

    α⇐
      : ∀ m {n o}
      → m + (n + o) ≡ (m + n) + o
    α⇐ ze = ≡.idn
    α⇐ (su m) = ≡.ap¹ su_ (α⇐ m)

open Nat public
  using (Nat)
  using (ze)
  using (su_)
  hiding (module Nat)
