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
𝐋              :  Domain  -- locations
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
postulate Loc : Set -- elements of 𝐋

data Misc : Set where
  null unallocated undefined unspecified : Misc

𝐋     =  Loc +⊥
𝐍     =  Nat⊥
𝐓     =  Bool⊥
𝐑     =  Int +⊥
𝐏     =  𝐋 × 𝐋
𝐌     =  Misc +⊥
𝐅     =  𝐄⋆ →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂
-- 𝐄  =  𝐓 + 𝐑 + 𝐏 + 𝐌 + 𝐅
-- The mutual recursion of 𝐄 and 𝐅 would make type-checking non-terminating.
-- The following postulates have been moved to Scm.Auxiliary-Functions,
-- otherwise Scm.Semantic-Functions can't find them!
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