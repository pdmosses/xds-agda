# Abstract Syntax

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Abstract-Syntax where

open import Data.Integer.Base  renaming (ℤ to Int) public
open import Data.String.Base   using (String) public

data       Con    : Set     -- constants, *excluding* quotations
variable   K      : Con
Ide               = String  -- identifiers (variables)
variable   I      : Ide
data       Exp    : Set     -- expressions
variable   E      : Exp
data       Exp⋆   : Set     -- expression sequences
variable   E⋆     : Exp⋆

data       Body   : Set     -- body expression or definition
variable   B      : Body
data       Body⁺  : Set     -- body sequences
variable   B⁺     : Body⁺
data       Prog   : Set     -- programs
variable   Π      : Prog
```

## Literal Constants

```agda
data Con where                -- basic constants
  int  : Int → Con            -- integer numerals
  #t   : Con                  -- true
  #f   : Con                  -- false
```

## Expressions

```agda
data Exp where                          -- expressions
  con          : Con → Exp              -- K
  ide          : Ide → Exp              -- I
  ⦅_␣_⦆        : Exp → Exp⋆ → Exp       -- (E E⋆)
  ⦅lambda_␣_⦆  : Ide → Exp → Exp        -- (lambda I E)
  ⦅if_␣_␣_⦆    : Exp → Exp → Exp → Exp  -- (if E E₁ E₂)
  ⦅set!_␣_⦆    : Ide → Exp → Exp        -- (set! I E)

data Exp⋆ where                         -- expression sequences
  ␣␣␣          : Exp⋆                   -- empty sequence
  _␣␣_         : Exp → Exp⋆ → Exp⋆      -- prefix sequence E E⋆
```

## Definitions and Programs

```agda
data Body where
  ␣␣_          : Exp → Body             -- side-effect expression E
  ⦅define_␣_⦆  : Ide → Exp → Body       -- definition (define I E)
  ⦅begin_⦆     : Body⁺ → Body           -- block (begin B⁺)

data Body⁺ where                        -- body sequence
  ␣␣_          : Body → Body⁺           -- single body sequence B
  _␣␣_         : Body → Body⁺ → Body⁺   -- prefix body sequence B B⁺

data Prog where                         -- programs
  ␣␣␣          : Prog                   -- empty program
  ␣␣_          : Body⁺ → Prog           -- non-empty program B⁺

infix 30 ␣␣_
infixr 20 _␣␣_
```