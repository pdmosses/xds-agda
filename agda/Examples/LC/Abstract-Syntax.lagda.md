# Abstract Syntax

Abstract syntax is *not* regarded as a domain.
In conventional Scott–Strachey style denotational semantics,
abstract syntax is generally first-order:
terms are finite, totally-defined elements.

A variable is written `x n`. The argument `n` merely distinguishes between variables –
it is *not* a De Bruin index.
The term constructor `var` below includes variables in terms.

In Agda, mixfix notation requires argument positions `_` to be separated by characters other than spaces.
The term constructors for function abstraction and application use the Unicode character `␣` as a separator.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Examples.LC.Abstract-Syntax where
--"hide"

open import Agda.Builtin.Nat public using (Nat)

--"/hide"
data Var : Set where
  x : Nat → Var
--"hide"
variable v : Var

--"/hide"
data Exp : Set where
  var_    : Var → Exp        -- variable reference
  ⦅λ_␣_⦆  : Var → Exp → Exp  -- function abstraction
  ⦅_␣_⦆   : Exp → Exp → Exp  -- function application
--"hide"
variable e e₁ e₂ : Exp
--"/hide"
```