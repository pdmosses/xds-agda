# Auxiliary Functions

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Auxiliary-Functions where

open import Notation
open Lifted
open Booleans
open Naturals
open Sums
open Products
open Sequences
open import Scm.Abstract-Syntax
open import Scm.Domain-Equations
-- If the following postulates are moved to Scm.Domain-Equations,
-- then Scm.Semantic-Functions can't find them!
postulate instance
  E+=T : 𝐓 ⇌ 𝐄
  E+=R : 𝐑 ⇌ 𝐄
  E+=P : 𝐏 ⇌ 𝐄
  E+=M : 𝐌 ⇌ 𝐄
  E+=F : 𝐅 ⇌ 𝐄
```

## Environments `ρ : 𝐔 = Ide →ˢ 𝐋`

```agda
postulate _==_ : Ide → Ide → Bool

_[_/_] : ⟪ 𝐔 →ᶜ 𝐋 →ᶜ Ide →ˢ 𝐔 ⟫
ρ [ α / I ] = λ I′ → ⌊ I == I′ ⌋ ⟶ α , ρ I′

postulate unknown : ⟪ 𝐋 ⟫
-- ρ I = unknown represents the lack of a binding for I in ρ

postulate initial-env : ⟪ 𝐔 ⟫
-- initial-env shoud include various procedures and values
```

## Stores `σ : 𝐒 = 𝐋 →ᶜ 𝐄`

```agda
_[_/_]′ : ⟪ 𝐒 →ᶜ 𝐄 →ᶜ 𝐋 →ᶜ 𝐒 ⟫
σ [ ϵ / α ]′ = λ α′ → (α ==⊥ α′) ⟶ ϵ , σ α′

assign : ⟪ 𝐋 →ᶜ 𝐄 →ᶜ 𝐂 →ᶜ 𝐂 ⟫
assign = λ α ϵ θ σ → θ (σ [ ϵ / α ]′)

hold : ⟪ 𝐋 →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂 ⟫
hold = λ α κ σ → κ (σ α) σ

postulate new : ⟪ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫
-- new κ σ = κ α σ′ where σ α = unallocated, σ′ α ≠ unallocated

alloc : ⟪ 𝐄 →ᶜ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫
alloc = λ ϵ κ → new (λ α → assign α ϵ (κ α))
-- should be ⊥ when ϵ |⊥ 𝐌 == ⌊ unallocated ⌋

initial-store : ⟪ 𝐒 ⟫
initial-store = λ α → ⌊ unallocated ⌋ in⊥ 𝐄

postulate finished : ⟪ 𝐂 ⟫
-- normal termination with answer depending on final store
```

## Truth Values

```agda
truish : ⟪ 𝐄 →ᶜ 𝐓 ⟫
truish =
  λ ϵ → (ϵ ∈⊥ 𝐓) ⟶
      (((ϵ |⊥ 𝐓) ==⊥ ⌊ false ⌋) ⟶ ⌊ false ⌋ , ⌊ true ⌋) ,
    ⌊ true ⌋
```

## Lists

```agda
cons : ⟪ 𝐅 ⟫
cons =
  λ ϵ⋆ κ →
      (# ϵ⋆ ==⊥ ⌊ 2 ⌋) ⟶ alloc (ϵ⋆ ↓ 1) (λ α₁ →
                        alloc (ϵ⋆ ↓ 2) (λ α₂ →
                          κ ((α₁ , α₂) in⊥ 𝐄))) , 
    ⊥

list : ⟪ 𝐅 ⟫
list = fix {D = 𝐅} λ list′ →
  λ ϵ⋆ κ →
    (# ϵ⋆ ==⊥ ⌊ 0 ⌋) ⟶ κ (⌊ null ⌋ in⊥ 𝐄) ,
      list′ (ϵ⋆ † 1) (λ ϵ → cons ⟨ (ϵ⋆ ↓ 1) , ϵ ⟩ κ)

car : ⟪ 𝐅 ⟫
car =
  λ ϵ⋆ κ → (# ϵ⋆ ==⊥ ⌊ 1 ⌋) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓²1) κ , ⊥

cdr : ⟪ 𝐅 ⟫
cdr =
  λ ϵ⋆ κ → (# ϵ⋆ ==⊥ ⌊ 1 ⌋) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓²2) κ , ⊥

setcar : ⟪ 𝐅 ⟫
setcar =
  λ ϵ⋆ κ →
      (# ϵ⋆ ==⊥ ⌊ 2 ⌋) ⟶ assign  (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓²1)
                             (ϵ⋆ ↓ 2)
                             (κ (⌊ unspecified ⌋ in⊥ 𝐄)) ,
    ⊥

setcdr : ⟪ 𝐅 ⟫
setcdr =
  λ ϵ⋆ κ →
      (# ϵ⋆ ==⊥ ⌊ 2 ⌋) ⟶ assign  (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓²2)
                             (ϵ⋆ ↓ 2)
                             (κ (⌊ unspecified ⌋ in⊥ 𝐄)) , 
    ⊥
```