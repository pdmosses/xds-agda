```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module PCF.Definitions where

open import Notation
open Functions
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
      α : Nat → (σ : Types) → 𝒱 σ
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

  𝒟 ι        =  Nat⊥
  𝒟 o        =  Bool⊥
  𝒟 (σ ⇒ τ)  = 𝒟 σ →ᶜ 𝒟 τ

  variable x y z : ⟪ 𝒟 σ ⟫
```

Environments are type-preserving maps from variables to values. They are
naturally modeled by a dependent type:

```agda
  open Maps
  open Variables

  Env = (σ : Types) → 𝒱 σ → ⟪ 𝒟 σ ⟫

  ρ⊥ : Env
  ρ⊥ = λ σ → λ _ → ⊥

  variable ρ : Env
```

Extension or overriding environments requires instances of the equality tests
for both variables and types:

```agda
  _==ⱽ_ : 𝒱 σ → 𝒱 σ → Bool
  α n σ ==ⱽ α n′ σ  =  (n ≡ᵇ n′)

  instance
    eqV : Eq (𝒱 σ)
    _==_ {{eqV}} = _==ⱽ_

  instance
    eqT : EqMaybe Types
    _==?_ {{eqT}} ι ι = just refl
    _==?_ {{eqT}} o o = just refl
    _==?_ {{eqT}} (σ ⇒ τ) (σ₁ ⇒ τ₁) with σ ==? σ₁
    _==?_ {{eqT}} (σ ⇒ τ) (σ₁ ⇒ τ₁)    | nothing = nothing
    _==?_ {{eqT}} (σ ⇒ τ) (.σ ⇒ τ₁)    | just refl with τ ==? τ₁
    _==?_ {{eqT}} (σ ⇒ τ) (.σ ⇒ τ₁)    | just refl    | nothing   = nothing
    _==?_ {{eqT}} (σ ⇒ τ) (.σ ⇒ .τ)    | just refl    | just refl = just refl
    _==?_ {{eqT}} _ _ = nothing
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

  ρ ⟦ α n σ ⟧ = ρ σ (α n σ)
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

  𝒜′⟦_⟧ : Terms σ → ⟪ Env →ˢ 𝒟 σ ⟫

  𝒜′⟦ 𝑉 (α n σ)    ⟧ ρ =  ρ ⟦ α n σ ⟧
  𝒜′⟦ 𝐿 c          ⟧ ρ =  𝒜⟦ c ⟧
  𝒜′⟦ M ␣ N        ⟧ ρ =  𝒜′⟦ M ⟧ ρ (𝒜′⟦ N ⟧ ρ) 
  𝒜′⟦ ƛ α n σ ␣ M  ⟧ ρ =  λ x → 𝒜′⟦ M ⟧ (ρ [ ρ σ [ x / α n σ ] / σ ]′)
```