# Auxiliary Functions

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}
module Scm.Auxiliary-Functions where
open import Scm.Abstract-Syntax
open import Scm.Domain-Equations
import Notation
open Notation.Domains using (⟪_⟫; ⊥)
open Notation.Functions using (_→ᶜ_; fix)
open Notation.Flat using (⌊_⌋)
open Notation.Flat.Booleans using (_⟶_,_; Eq⊥; _==⊥_; true; false)
open Notation.Sums using (_⇌_; _in⊥_; _∈⊥_; _|⊥_)
open Notation.Products using (_,_; _↓²1; _↓²2)
open Notation.Products.Sequences using (⟨_⟩; #; _↓_; _†_)
open Notation.Updates using (Eq; _[_/_]⊥)
```

## Operations

```agda
postulate instance
  eqL : Eq⊥ 𝐋
  eqM : Eq⊥ 𝐌
  eqR : Eq⊥ 𝐑
postulate
  _<ᴿ_   : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐓 ⟫
  _+ᴿ_   : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐑 ⟫
  _∧ᵀ_   : ⟪ 𝐓 →ᶜ 𝐓 →ᶜ 𝐓 ⟫
```

## Environments

```agda
postulate instance eqIde : Eq Ide
postulate unknown : ⟪ 𝐋 ⟫
postulate initial-env : ⟪ 𝐔 ⟫
```

## Stores

```agda
assign : ⟪ 𝐋 →ᶜ 𝐄 →ᶜ 𝐂 →ᶜ 𝐂 ⟫
assign α ϵ θ σ = θ (σ [ ϵ / α ]⊥)

hold : ⟪ 𝐋 →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂 ⟫
hold α κ σ = κ (σ α) σ

postulate new : ⟪ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫

alloc : ⟪ 𝐄 →ᶜ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫
alloc ϵ κ = new (λ α → assign α ϵ (κ α))

initial-store : ⟪ 𝐒 ⟫
initial-store α = ⌊ unallocated ⌋ in⊥ 𝐄

postulate finished : ⟪ 𝐂 ⟫
```

## Truth Values

```agda
truish : ⟪ 𝐄 →ᶜ 𝐓 ⟫
truish ϵ =
  (ϵ ∈⊥ 𝐓) ⟶ (((ϵ |⊥ 𝐓) ==⊥ ⌊ false ⌋) ⟶ ⌊ false ⌋ , ⌊ true ⌋) ,
  ⌊ true ⌋
```

## Lists

```agda
cons : ⟪ 𝐅 ⟫
cons ϵ⋆ κ =
  (# ϵ⋆ ==⊥ ⌊ 2 ⌋) ⟶
    alloc (ϵ⋆ ↓ 1) (λ α₁ → alloc (ϵ⋆ ↓ 2) (λ α₂ → κ ((α₁ , α₂) in⊥ 𝐄))) ,
  ⊥

list : ⟪ 𝐅 ⟫
list =
  fix {D = 𝐅} λ list′ → λ ϵ⋆ κ →
    (# ϵ⋆ ==⊥ ⌊ 0 ⌋) ⟶ κ (⌊ null ⌋ in⊥ 𝐄) ,
    list′ (ϵ⋆ † 1) (λ ϵ → cons ⟨ (ϵ⋆ ↓ 1) , ϵ ⟩ κ)

car : ⟪ 𝐅 ⟫
car ϵ⋆ κ = (# ϵ⋆ ==⊥ ⌊ 1 ⌋) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓²1) κ , ⊥

cdr : ⟪ 𝐅 ⟫
cdr ϵ⋆ κ = (# ϵ⋆ ==⊥ ⌊ 1 ⌋) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓²2) κ , ⊥

setcar : ⟪ 𝐅 ⟫
setcar ϵ⋆ κ =
  (# ϵ⋆ ==⊥ ⌊ 2 ⌋) ⟶
    assign (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓²1) (ϵ⋆ ↓ 2) (κ (⌊ unspecified ⌋ in⊥ 𝐄)) ,
  ⊥

setcdr : ⟪ 𝐅 ⟫
setcdr ϵ⋆ κ =
  (# ϵ⋆ ==⊥ ⌊ 2 ⌋) ⟶
    assign (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓²2) (ϵ⋆ ↓ 2) (κ (⌊ unspecified ⌋ in⊥ 𝐄)) ,
  ⊥
```