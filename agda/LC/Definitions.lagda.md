# LC Definitions

This module defines a denotational semantics of the untyped λ-calculus in Agda,
corresponding to Dana Scott's original $D_\infty$ model. 

The following options are needed in connection with the lightweight
formalisation of [function domains] in Agda.

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
variables – it is *not* a De Bruin index.

```agda
  open import Agda.Builtin.Nat public using (Nat)
  data Var : Set where
    x : Nat → Var
  variable v : Var
```

### Terms

The term constructor `var` below merely includes variables in terms.

In Agda, mixfix notation requires arguments to be separated by characters
other than spaces. Below, the notation for application `⦅ e₁ ␣ e₂ ⦆` and
λ-abstraction `⦅λ v ␣ e ⦆` uses the Unicode character `␣` (representing a
space) as a separator. Application terms are also parenthesised, but using
`⦅…⦆` instead of ordinary parentheses.

```agda
  data Exp : Set where
    var_    : Var → Exp        -- variable reference
    ⦅λ_␣_⦆  : Var → Exp → Exp  -- function abstraction
    ⦅_␣_⦆   : Exp → Exp → Exp  -- function application
  variable e e₁ e₂ : Exp
```

Abstract syntax is *not* regarded as a domain. All abstract syntax terms
are finite, and semantic functions are defined inductively.

## Domain equations

The domain equation `D∞ ≅ (D∞ →ᶜ D∞)` below declares the functions
`unfold : ⟪ D∞ →ᶜ (D∞ →ᶜ D∞) ⟫` and `fold : ⟪ (D∞ →ᶜ D∞) →ᶜ D∞ ⟫`,
corresponging to a bijection between the postulated domain `D∞` and
the domain of all continuous endofunctions on `D∞`. (Simply defining
`D∞ = (D∞ →ᶜ D∞)` would lead to non-termination of the Agda type-checker.)

```agda
module Domain-Equations where

  open Abstract-Syntax
  open Notation.Recursion using (_≅_; fold; unfold) public
  postulate
    D∞ : Domain                      -- corresponds to Scott's domain 
    instance eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)  -- bijection
  variable δ : ⟪ D∞ ⟫
```

The one-point domain `𝟙` is a trivial solution for the above domain equation.
It could be excluded by postulating an embedding of any non-trivial domain
into `D∞`. 

Environments `ρ` map variables to elements of the carrier of the postulated
domain `D∞`. The type `Env` could be treated as a domain by ordering the maps
pointwise.

```agda
  Env = Var →ˢ D∞  -- environments
  variable ρ : ⟪ Env ⟫
```

The following definitions instantiate the conventional notation `ρ [ δ / v ]`
for the environment that maps `v` to `δ`, and maps other arguments as `ρ` does. 

```agda
  open Notation.Flat.Booleans using (Bool; Eq; _==_)
  open Notation.Flat.Naturals using (eqNat)
  _==ⱽ_ : Var → Var → Bool
  open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public
  open Notation.Updates using (_[_/_]) public
  (x n ==ⱽ x n′) = (n ==ᴺ n′)
  instance eqVar : Eq Var; _==_ {{eqVar}} = _==ⱽ_
```

## Semantic functions

The semantic equations below correspond closely to those found in textbooks
on denotational semantics. (The inverse functions `unfold` and `fold` between
domains and their definitions reflect that solutions of domain equations are
up to isomorphism, and are conventionally elided.)

```agda
module Semantic-Functions where

  open Abstract-Syntax
  open Domain-Equations
  ⟦_⟧ : Exp → ⟪ Env →ᶜ D∞ ⟫
  ⟦ var v ⟧ ρ        = ρ v
  ⟦ ⦅λ v ␣ e ⦆ ⟧ ρ   = fold ( λ δ → ⟦ e ⟧ (ρ [ δ / v ]) )
  ⟦ ⦅ e₁ ␣ e₂ ⦆ ⟧ ρ  = unfold ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )
```

See the [Tests] module for some examples of abstract syntax terms and
equivalence proofs.

[Function domains]: ../../Notation/index.md#function-domains
[Tests]: ../Tests/index.md