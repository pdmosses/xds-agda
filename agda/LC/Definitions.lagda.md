# LC Definitions

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module LC.Definitions where

open import Notation
```

## Abstract Syntax

```agda
module Abstract-Syntax where
```

### Variables

```agda
  open import Data.Nat  using (ℕ; _≡ᵇ_)

  data Var : Set where
    x : ℕ → Var  -- variables

  variable v : Var
```

### Terms

```agda
  data Exp : Set where
    var_  : Var → Exp         -- variable value
    lam   : Var → Exp → Exp   -- lambda abstraction
    app   : Exp → Exp → Exp   -- application

  variable e : Exp
```

## Domain equations

```agda
module Domain-Equations where

  open Abstract-Syntax
  open Notation.Lifted.Maps
  open Notation.Recursion

  postulate
    D∞ : Domain
  
  postulate instance
    eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)

  Env = Var → ⟪ D∞ ⟫

  variable ρ : Env

  postulate instance
    eqVar : Eq Var
```

## Semantic functions

```agda
module Semantic-Functions where

  open Abstract-Syntax
  open Domain-Equations
  open Notation.Lifted.Maps
  open Notation.Recursion

  ⟦_⟧ : Exp → Env → ⟪ D∞ ⟫

  ⟦ var  v      ⟧ ρ  = ρ v
  ⟦ lam  v e    ⟧ ρ  = fold ( λ d → ⟦ e ⟧ (ρ [ d / v ]) )
  ⟦ app  e₁ e₂  ⟧ ρ  = unfold ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )
```


open import Data.Bool using (Bool)

_==_ : Var → Var → Bool
x n == x n′ = (n ≡ᵇ n′)

_[_/_] : Env → ⟪ D∞ ⟫ → Var → Env
ρ [ d / v ] = λ v′ → if v == v′ then d else ρ v′
