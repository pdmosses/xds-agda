# Abstract Syntax

Abstract syntax is *not* regarded as a domain.
In conventional Scott–Strachey style denotational semantics,
abstract syntax is generally first-order:
terms are finite, totally-defined elements.

A variable is written `x n`. The argument `n` merely distinguishes between variables –
it is *not* a De Bruijn index.
The term constructor `var` below includes variables in terms.

In Agda, mixfix notation requires argument positions `_` to be separated by characters other than spaces.
The term constructors for function abstraction and application use the Unicode character `␣` as a separator.
```agda
{-# OPTIONS --rewriting --confluence-check #-}

module Examples.LC.Abstract-Syntax where

open import Agda.Builtin.Nat public using (Nat)

data Var : Set where
  x : Nat → Var
variable v : Var

data Exp : Set where
  var_    : Var → Exp        -- variable reference
  ⦅λ_␣_⦆  : Var → Exp → Exp  -- function abstraction
  ⦅_␣_⦆   : Exp → Exp → Exp  -- function application
variable e e₁ e₂ : Exp
```