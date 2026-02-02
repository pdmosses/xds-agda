\begin{code}
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module PCF.Environments where

open import Data.Bool.Base 
  using (Bool; if_then_else_)
open import Data.Maybe.Base
  using (Maybe; just; nothing)
open import Agda.Builtin.Nat
  using (Nat; _==_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; trans; cong)

open import PCF.Domain-Notation
  using (⟪_⟫; ⊥)
open import PCF.Types
  using (Types; ι; o; _⇒_; 𝒟)
open import PCF.Variables
  using (𝒱; var; Env)

-- ρ⊥ is the initial environment

ρ⊥ : Env
ρ⊥ α = ⊥

-- (ρ [ x / α ]) α′ = x when α and α′ are identical, otherwise ρ α′

_[_/_] : {σ : Types} → Env → ⟪ 𝒟 σ ⟫ → 𝒱 σ → Env
ρ [ x / α ] = λ α′ → h ρ x α α′ (α ==V α′) where

  h : {σ τ : Types} → Env → ⟪ 𝒟 σ ⟫ → 𝒱 σ → 𝒱 τ → Maybe (σ ≡ τ) → ⟪ 𝒟 τ ⟫
  h ρ x α α′ (just refl)  = x
  h ρ x α α′ nothing      = ρ α′

  _==T_ : (σ τ : Types) → Maybe (σ ≡ τ)
  (σ ⇒ τ) ==T (σ′ ⇒ τ′) = f (σ ==T σ′) (τ ==T τ′) where
        f : Maybe (σ ≡ σ′) → Maybe (τ ≡ τ′) → Maybe ((σ ⇒ τ) ≡ (σ′ ⇒ τ′))
        f = λ { (just p) (just q) → just (trans (cong (_⇒ τ) p) (cong (σ′ ⇒_) q))
              ; _ _ → nothing }
  ι       ==T ι         = just refl
  o       ==T o         = just refl
  _       ==T _         = nothing

  _==V_ : {σ τ : Types} → 𝒱 σ → 𝒱 τ → Maybe (σ ≡ τ)
  var i σ ==V var i′ τ = 
    if i == i′ then σ ==T τ else nothing
\end{code}