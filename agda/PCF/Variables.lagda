\begin{code}
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module PCF.Variables where

open import Agda.Builtin.Nat
  using (Nat)

open import PCF.Domain-Notation
  using (⟪_⟫; _→ᶜ_; _→ˢ_)
open import PCF.Types
  using (Types; σ; 𝒟)

-- Syntax

data 𝒱 : Types → Set where
  var : Nat → (σ : Types) → 𝒱 σ

variable α : 𝒱 σ

-- Environments

Env = {σ : Types} → 𝒱 σ → ⟪ 𝒟 σ ⟫

variable ρ : Env

-- Semantics

_⟦_⟧ : ⟪ Env →ˢ 𝒱 σ →ˢ 𝒟 σ ⟫

ρ ⟦ α ⟧ = ρ α
\end{code}