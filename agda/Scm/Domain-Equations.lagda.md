# Domain Equations

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Domain-Equations where

open import Notation
open Lifted
open Booleans
open Naturals
open Sums
open Products
open Sequences
open import Scm.Abstract-Syntax using (Ide; Int)
```

## Domain declarations

```agda
postulate  𝐋   :  Domain  -- locations
variable   α   :  ⟪ 𝐋 ⟫
𝐍              :  Domain  -- natural numbers
𝐓              :  Domain  -- booleans
𝐑              :  Domain  -- numbers
𝐏              :  Domain  -- pairs
𝐌              :  Domain  -- miscellaneous
variable   μ   :  ⟪ 𝐌 ⟫
𝐅              :  Domain  -- procedure values
variable   φ   :  ⟪ 𝐅 ⟫
postulate  𝐄   :  Domain  -- expressed values
variable   ϵ   :  ⟪ 𝐄 ⟫
𝐒              :  Domain  -- stores
variable   σ   :  ⟪ 𝐒 ⟫
𝐔              :  Domain  -- environments
variable   ρ   :  ⟪ 𝐔 ⟫
𝐂              :  Domain  -- command continuations
variable   θ   :  ⟪ 𝐂 ⟫
postulate  𝐀   :  Domain  -- answers

𝐄⋆             =  𝐄 ⋆
variable   ϵ⋆  :  ⟪ 𝐄⋆ ⟫
```

## Domain Definitions

```agda
data Misc : Set where
  null unallocated undefined unspecified : Misc

𝐍     =  Nat⊥
𝐓     =  Bool⊥
𝐑     =  Int +⊥
𝐏     =  𝐋 × 𝐋
𝐌     =  Misc +⊥
𝐅     =  𝐄⋆ →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂
-- 𝐄  =  𝐓 + 𝐑 + 𝐏 + 𝐌 + 𝐅
-- postulate instance
--   E+=T : 𝐓 ⇌ 𝐄
--   E+=R : 𝐑 ⇌ 𝐄
--   E+=P : 𝐏 ⇌ 𝐄
--   E+=M : 𝐌 ⇌ 𝐄
--   E+=F : 𝐅 ⇌ 𝐄
𝐒     =  𝐋 →ᶜ 𝐄
𝐔     =  Ide →ˢ 𝐋
𝐂     =  𝐒 →ᶜ 𝐀
```

## Operations

```agda
postulate
  Eq : Domain → Set
  _==⊥_ : {D : Domain} → {{Eq D}} → ⟪ D →ᶜ D →ᶜ 𝐓 ⟫
  instance
    eqL : Eq 𝐋
    eqM : Eq 𝐌
    eqN : Eq 𝐍
    eqR : Eq 𝐑
    eqT : Eq 𝐓

postulate
  _<ᴿ_   : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐓 ⟫
  _+ᴿ_   : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐑 ⟫
  _∧ᵀ_   : ⟪ 𝐓 →ᶜ 𝐓 →ᶜ 𝐓 ⟫
```