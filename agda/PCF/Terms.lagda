\begin{code}
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module PCF.Terms where

open import PCF.Domain-Notation
  using (⟪_⟫; _→ᶜ_; _→ˢ_)
open import PCF.Types
  using (Types; _⇒_; σ; 𝒟)
open import PCF.Constants
  using (ℒ; 𝒜⟦_⟧; c)
open import PCF.Variables
  using (𝒱; Env; _⟦_⟧)
open import PCF.Environments
  using (_[_/_])

-- Syntax

data Terms : Types → Set where
  𝑉     : {σ   : Types} → 𝒱 σ → Terms σ                      -- variables
  𝐿     : {σ   : Types} → ℒ σ → Terms σ                      -- constants
  _␣_   : {σ τ : Types} → Terms (σ ⇒ τ) → Terms σ → Terms τ  -- application
  ƛ_␣_  : {σ τ : Types} → 𝒱 σ → Terms τ → Terms (σ ⇒ τ)      -- λ-abstraction

variable M N : Terms σ
infixl 20 _␣_

-- Semantics

𝒜′⟦_⟧ : Terms σ → ⟪ Env →ˢ 𝒟 σ ⟫

𝒜′⟦ 𝑉 α      ⟧ ρ = ρ ⟦ α ⟧
𝒜′⟦ 𝐿 c      ⟧ ρ = 𝒜⟦ c ⟧
𝒜′⟦ M ␣ N    ⟧ ρ = 𝒜′⟦ M ⟧ ρ (𝒜′⟦ N ⟧ ρ) 
𝒜′⟦ ƛ α ␣ M  ⟧ ρ = λ x → 𝒜′⟦ M ⟧ (ρ [ x / α ])
\end{code}