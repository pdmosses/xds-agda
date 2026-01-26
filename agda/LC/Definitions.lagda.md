# LC Definitions

This module defines a denotational semantics of the untyped λ-calculus in Agda,
corresponding to Dana Scott's original $D_\infty$ model. 

The following options are needed in connection with the lightweight
formalisation of domains in Agda.

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

A variable  is written `x n`. The argument `n` merely distinguishes between
variables – `n` is not a De Bruin index.

```agda
  open import Data.Nat.Base using (ℕ; _≡ᵇ_)

  data Var : Set where
    x : ℕ → Var  -- variables

  variable v : Var
```

### Terms

The term constructor `val` below merely includes variables in terms.

Agda does not support the use of the conventional notation `λ _ . _`
for the abstract syntax of lambda abstraction terms, nor juxtaposition `_ _`
for the abstract syntax of application terms. The Unicode symbols `ƛ` and `␣`
allow abstract syntax terms to be written reasonably suggestively.

```agda
  data Exp : Set where
    val_  : Var → Exp         -- variable value
    ƛ_␣_  : Var → Exp → Exp   -- lambda abstraction
    _␣_   : Exp → Exp → Exp   -- application

  infixl 20 _␣_

  variable e : Exp
```

Abstract syntax does not need to be regarded as a domain. Abstract syntax terms
are well-founded, and functions on them can be defined inductively.

## Domain equations

The domain equation `D∞ ≅ (D∞ →ᶜ D∞)` below declares the functions
`unfold : ⟪ D∞ →ᶜ (D∞ →ᶜ D∞) ⟫ and `fold : ⟪ (D∞ →ᶜ D∞) →ᶜ D∞ ⟫`,
corresponging to an isomorphism between the postulated domain `D∞` and
the domain of all continuous endofunctions on `D∞`. (Simply defining
`D∞ = (D∞ →ᶜ D∞)` would lead to non-termination of the Agda type-checker.)

```agda
module Domain-Equations where

  open Abstract-Syntax
  open Notation.Recursion public

  postulate
    D∞ : Domain
  
  postulate instance
    eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)
```

The one-point domain is a trivial solution for the above domain equation.
It coud be excluded by postulating an embedding of any non-trivial domain
into `D∞`.

Environments `ρ` map variables to elements of the carrier of the postulated
domain `D∞`. The type `Env` could be treated as a domain by ordering the maps
pointwise.

```agda
  Env = Var → ⟪ D∞ ⟫

  variable ρ : Env
```

The following definitions instantiate the conventional notation `ρ [ d / v ]`
for the environment that maps `v` to `d`, and maps other arguments as `ρ` does. 

```agda
  open import Data.Bool.Base using (Bool)
  open Notation.Lifted.Maps public

  _==ⱽ_ : Var → Var → Bool
  x n ==ⱽ x n′ = (n ≡ᵇ n′)

  instance
    eqVar : Eq Var
    _==_ {{eqVar}} = _==ⱽ_
```

## Semantic functions

The semantic equations below correspond closely to those found in textbooks
on denotational semantics. (The inverse functions `unfold` and `fold` between
domains and their definitions reflect that solutions of domain equations are
defined up to isomorphism, and are conventionally elided.)

```agda
module Semantic-Functions where

  open Abstract-Syntax
  open Domain-Equations

  ⟦_⟧ : Exp → Env → ⟪ D∞ ⟫

  ⟦ val  v   ⟧ ρ  = ρ v
  ⟦ ƛ v ␣ e  ⟧ ρ  = fold ( λ d → ⟦ e ⟧ (ρ [ d / v ]) )
  ⟦ e₁ ␣ e₂  ⟧ ρ  = unfold ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )
```

See the [LC.Tests] module for some examples of abstract syntax terms and their
denotations.

[LC.Tests]: LC.Tests/index.md