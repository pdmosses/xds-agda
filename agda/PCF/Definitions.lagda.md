```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module PCF.Definitions where

open import Notation
```

## Abstract Syntax

```agda
module Abstract-Syntax where
```

### Types

```agda
  module Types where

    data Types : Set where
      ι    : Types                  -- natural numbers
      o    : Types                  -- Boolean truthvalues
      _⇒_  : Types → Types → Types  -- functions

    variable σ τ : Types

    infixr 1 _⇒_
```

### Variables

```agda
  module Variables where

    open Types
    
    data 𝒱 : Types → Set where
      var : Nat → (σ : Types) → 𝒱 σ

    variable α : 𝒱 σ
```

### Constants

```agda
  module Constants where

    open Types
    
    data ℒ : Types → Set where
      tt   : ℒ o
      ff   : ℒ o
      ⊃ᵢ   : ℒ (o ⇒ ι ⇒ ι ⇒ ι)
      ⊃ₒ   : ℒ (o ⇒ o ⇒ o ⇒ o)
      Y    : ℒ ((σ ⇒ σ) ⇒ σ)
      k    : Nat → ℒ ι
      +1′  : ℒ (ι ⇒ ι)
      -1′  : ℒ (ι ⇒ ι)
      Z    : ℒ (ι ⇒ o)

    variable c : ℒ σ
```

### Terms

```agda
  module Terms where

    open Types
    open Variables
    open Constants
    
    data Terms : Types → Set where
      𝑉     : 𝒱 σ → Terms σ                      -- variables
      𝐿     : ℒ σ → Terms σ                      -- constants
      _␣_   : Terms (σ ⇒ τ) → Terms σ → Terms τ  -- application
      ƛ_␣_  : 𝒱 σ → Terms τ → Terms (σ ⇒ τ)      -- λ-abstraction

    variable M N : Terms σ
    infixl 20 _␣_
```

## Domain equations

```agda
module Domain-Equations where

  open Abstract-Syntax
  open Types
  open Lifted
  open Booleans
  open Naturals

  𝒟 : Types → Domain

  𝒟 ι        = Nat⊥
  𝒟 o        = Bool⊥
  𝒟 (σ ⇒ τ)  = 𝒟 σ →ᶜ 𝒟 τ

  variable x y z : ⟪ 𝒟 σ ⟫

  open Maps
  open Variables

  Env = {σ : Types} → 𝒱 σ → ⟪ 𝒟 σ ⟫

  variable ρ : Env
```

## Semantic functions

```agda
module Semantic-Functions where

  open Abstract-Syntax
  open Types
```

### Variables

```agda
  open Variables
  open Domain-Equations

  _⟦_⟧ : ⟪ Env →ˢ 𝒱 σ →ˢ 𝒟 σ ⟫

  ρ ⟦ α ⟧ = ρ α
```

### Constants

```agda
  open Constants
  open Lifted
  open Booleans
  open Naturals

  𝒜⟦_⟧ : ℒ σ → ⟪ 𝒟 σ ⟫

  𝒜⟦ tt   ⟧ =  ⌊ true ⌋
  𝒜⟦ ff   ⟧ =  ⌊ false ⌋
  𝒜⟦ ⊃ᵢ   ⟧ =  _⟶_,_
  𝒜⟦ ⊃ₒ   ⟧ =  _⟶_,_
  𝒜⟦ Y    ⟧ =  fix
  𝒜⟦ k n  ⟧ =  ⌊ n ⌋
  𝒜⟦ +1′  ⟧ =  (λ n → ⌊ n + 1 ⌋) ♯
  𝒜⟦ -1′  ⟧ =  (λ n → if n ≡ᵇ 0 then ⊥ else ⌊ n ∸ 1 ⌋) ♯
  𝒜⟦ Z    ⟧ =  (λ n → ⌊ n ≡ᵇ 0 ⌋) ♯
```

### Terms

```agda
  open Terms
  open Maps
  
  _==ⱽ_ : 𝒱 σ → 𝒱 σ → Bool
  var n σ ==ⱽ var n′ σ  =  (n ≡ᵇ n′)

  instance
    eqVar : Eq (𝒱 σ)
    _==_ {{eqVar}} = _==ⱽ_
  
-- 169,41-42: error: [UnequalTerms]
-- σ != σ₁ of type Types
-- when checking that the expression x has type ⟪ 𝒟 σ₁ ⟫

  𝒜′⟦_⟧ : Terms σ → ⟪ Env →ˢ 𝒟 σ ⟫

  𝒜′⟦ 𝑉 α      ⟧ ρ = ρ ⟦ α ⟧
  𝒜′⟦ 𝐿 c      ⟧ ρ = 𝒜⟦ c ⟧
  𝒜′⟦ M ␣ N    ⟧ ρ = 𝒜′⟦ M ⟧ ρ (𝒜′⟦ N ⟧ ρ) 
  𝒜′⟦ ƛ α ␣ M  ⟧ ρ = λ x → 𝒜′⟦ M ⟧ (ρ [ x / α ])
```