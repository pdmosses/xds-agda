# Auxiliary Functions

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Auxiliary-Functions where

  open import Scm.Abstract-Syntax
  open import Scm.Domain-Equations
  import Notation
  open Notation.Domains using (⟪_⟫; ⊥)
  open Notation.Functions using (_→ᶜ_; fix)
  open Notation.Flat using (↑)
  open Notation.Flat.Booleans using (_⟶_,_; Eq; _==⊥_; true; false)
  open Notation.Sums using (_in⊥_; _∈⊥_; _|⊥_)
  open Notation.Products using (_,_; _↓₁; _↓₂)
  open Notation.Products.Sequences using (⟨_⟩; #; _↓_; _†_)
  open Notation.Updates using (_[_/_]⊥)
```

## Operations

The following postulates instantiate the operation `_==⊥_` on the flat
domains `𝐋`, `𝐌`, and `𝐑`, and illustrate declaration of further
operations on `𝐑` and `𝐓`.

```agda
  postulate instance
    eqL   : Eq Loc
    eqM   : Eq Misc
    eqR   : Eq Int
  
  postulate
    _<ᴿ_  : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐓 ⟫
    _+ᴿ_  : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐑 ⟫
    _∧ᵀ_  : ⟪ 𝐓 →ᶜ 𝐓 →ᶜ 𝐓 ⟫
```

## Environments

An environment `ρ` is a function from the defined type `Ide` to the carrier of
the domain `𝐋`. The instance `Eq Ide` supports the conventional notation
`ρ [ α / I ]` for updating `ρ` to map `I` to location `α`.

```agda
  postulate instance
    eqIde : Eq Ide

  postulate unknown : Loc

  postulate initial-env : ⟪ 𝐔 ⟫
```

The `initial-env` could map predefined identifiers to initialised locations
in the initial store, and all other identifiers to `unknown`. 

## Stores

A store `σ` is a function from the flat domain `𝐋` of locations to the
postulated domain `𝐄`. The instance `Eq⊥ 𝐋` (declared above) supports the
notation `σ [ ϵ / α ]⊥` for updating `σ` to map `α` to `ϵ`.[^update]

[^update]:
    In conventional denotational definitions, the notation for updating
    a store `σ` is the same as that for updating an environment `ρ`.

```agda
  assign : ⟪ 𝐋 →ᶜ 𝐄 →ᶜ 𝐂 →ᶜ 𝐂 ⟫      -- assign α ϵ stores ϵ at location α
  assign α ϵ θ σ = θ (σ [ ϵ / α ]⊥)

  hold : ⟪ 𝐋 →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂 ⟫      -- hold α gives the value stored at α
  hold α κ σ = κ (σ α) σ
```

The function `new` is for use in continuation-passing style. An application
`new κ σ` should apply `κ` to a location `α` mapped to `↑ unallocated` in `σ`;
if all locations have already been allocated, it should discard `κ`.

```agda
  postulate new : ⟪ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫  -- new gives an unallocated location

  alloc : ⟪ 𝐄 →ᶜ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫     -- alloc ϵ allocates a location for ϵ
  alloc ϵ κ = new (λ α → assign α ϵ (κ α))

  postulate initial-store : ⟪ 𝐒 ⟫    -- may have initialised locations
```

The `initial-store` could map initialised locations to their values, and all
other locations to `↑ unallocated`. 

```agda
  postulate finished : ⟪ 𝐒 →ᶜ 𝐀 ⟫    -- obtain answer from the final store
```

The continuation `finished` maps the final store to an element of the
postulated domain `𝐀` of answers.

## Truth Values

`truish ϵ` is false when `ϵ` is false, and `true` for all other non-⊥ values.
As `𝐄` is not a flat domain, the definition has to check `ϵ ∈⊥ 𝐓` before
testing for equality. 

```agda
  truish : ⟪ 𝐄 →ᶜ 𝐓 ⟫  -- truish ε is true for all ε except false
  truish ϵ =  (ϵ ∈⊥ 𝐓) ⟶ (((ϵ |⊥ 𝐓) ==⊥ ↑ false) ⟶ ↑ false , ↑ true) ,
              ↑ true
```

## Lists

The following definitions of standard Scheme functions for list processing
use conventional notation for pairs `α₁ , α₂` and sequences `⟨ ϵ⋆ ⟩`.

```agda
  cons : ⟪ 𝐅 ⟫         -- cons ⟨ ϵ₁ , ϵ₂ ⟩ allocates and initialises a pair
  cons ϵ⋆ κ =  (# ϵ⋆ ==⊥ ↑ 2) ⟶
                 alloc (ϵ⋆ ↓ 1) (λ α₁ →
                   alloc (ϵ⋆ ↓ 2) (λ α₂ → κ ((α₁ , α₂) in⊥ 𝐄))) ,
               ⊥
```

The recursive definition of the `list` function requires an explicit fixed
point in Agda:

```agda
  list : ⟪ 𝐅 ⟫         -- list ϵ⋆ allocates and initialises a list
  list =  fix λ (list′ : ⟪ 𝐅 ⟫) → λ ϵ⋆ κ →
            (# ϵ⋆ ==⊥ ↑ 0) ⟶ κ (↑ null in⊥ 𝐄) ,
            list′ (ϵ⋆ † 1) (λ ϵ → cons ⟨ (ϵ⋆ ↓ 1) , ϵ ⟩ κ)

  car : ⟪ 𝐅 ⟫          -- car ⟨ ϵ ⟩ gives the head of the list ϵ
  car ϵ⋆ κ = (# ϵ⋆ ==⊥ ↑ 1) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₁) κ , ⊥

  cdr : ⟪ 𝐅 ⟫          -- cdr ⟨ ϵ ⟩ gives the tail of the list ϵ
  cdr ϵ⋆ κ = (# ϵ⋆ ==⊥ ↑ 1) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₂) κ , ⊥

  setcar : ⟪ 𝐅 ⟫       -- setcar ⟨ ϵ₁ , ϵ₂ ⟩ stores ϵ₂ in the head of list ϵ₁
  setcar ϵ⋆ κ =
    (# ϵ⋆ ==⊥ ↑ 2) ⟶
      assign (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₁) (ϵ⋆ ↓ 2) (κ (↑ unspecified in⊥ 𝐄)) ,
    ⊥

  setcdr : ⟪ 𝐅 ⟫       -- setcdr ⟨ ϵ₁ , ϵ₂ ⟩ stores ϵ₂ in the tail of list ϵ₁
  setcdr ϵ⋆ κ =
    (# ϵ⋆ ==⊥ ↑ 2) ⟶
      assign (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₂) (ϵ⋆ ↓ 2) (κ (↑ unspecified in⊥ 𝐄)) ,
    ⊥
```