{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.PCF.Domain-Equations where

open import Examples.PCF.Abstract-Syntax
open import Notation
open Notation.Flat.Booleans using (Bool; Bool⊥)
open Notation.Flat.Naturals using (Nat⊥; eqNat)

𝒟 : Types → Domain       -- standard domains
𝒟 ι        = Nat⊥        -- natural numbers
𝒟 o        = Bool⊥       -- truth-values
𝒟 (σ ⇒ τ)  = 𝒟 σ →ᶜ 𝒟 τ  -- functions
variable x y z : ⟪ 𝒟 σ ⟫

Env = (σ : Types) → ⟪ Vars σ →ˢ 𝒟 σ ⟫  -- typed environments
variable ρ : Env
ρ⊥ : Env                               -- initial environment
ρ⊥ _ _ = ⊥

open Notation.Flat.Booleans using (Eq; _==_)
open Notation.Updates using (_[_/_])
_==ⱽ_ : Vars σ → Vars σ → Bool
open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public
(α i σ ==ⱽ α i′ σ)  =  (i ==ᴺ i′)
instance
  eqV : Eq (Vars σ)
  _==_ {{eqV}} = _==ⱽ_
open Notation.Updates using (MaybeEq; _==?_; just; nothing; refl; _[_←_])
instance
  eqT : MaybeEq Types
  eqT ._==?_ ι ι = just refl
  eqT ._==?_ o o = just refl
  eqT ._==?_ (σ ⇒ τ) (σ₁ ⇒ τ₁) with σ ==? σ₁  | τ ==? τ₁
  eqT ._==?_ (σ ⇒ τ) (σ₁ ⇒ τ₁)    | just refl | just refl = just refl
  eqT ._==?_ (σ ⇒ τ) (σ₁ ⇒ τ₁)    | _         | _         = nothing
  eqT ._==?_ _ _ = nothing

_[_/_]′ : Env → ⟪ 𝒟 σ ⟫ → Vars σ → Env
-- ρ [ v / x ]′ maps x to v, and other x′ to ρ x′
_[_/_]′ {σ} ρ x v = ρ [ σ ← ρ σ [ x / v ] ]