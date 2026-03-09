# Abstract Syntax

```agda
{-# OPTIONS --rewriting --confluence-check #-}

module Scm.Abstract-Syntax where
```

## Identifiers

In the concrete syntax of the full Scheme programming language, identifiers
can be almost arbitrary sequences of characters. For abstract syntax in Agda,
it is convenient to represent identifiers as strings.

```agda
  open import Data.String.Base public using (String)
  Ide = String      -- identifiers
  variable I : Ide
```

## Literal Constants

The abstract syntax of the Scm sublanguage restricts constants to integers
and truth values. THe Agda formalisation uses the constructor `int` to include
integers as ASTs in `Con`, and the standard Scheme notation `#t` and `#f` for
the truth values.

```agda
  open import Data.Integer.Base public renaming (ℤ to Int) using ()
  data Con  : Set where  -- constants
    int     : Int → Con  -- integer numerals
    #t      : Con        -- true
    #f      : Con        -- false
  variable K : Con
```

## Expressions

Scheme expressions include function application, lambda-abstraction,
conditional choice, and assignment. The constructors used in the Agda
formalisation correspond closely to the concrete syntax of Scheme.

```agda
  mutual
    data Exp       : Set where              -- expressions
      con          : Con → Exp              -- constants
      ide          : Ide → Exp              -- identifiers
      ⦅_␣_⦆        : Exp → Exp⋆ → Exp       -- procedure application 
      ⦅lambda_␣_⦆  : Ide → Exp → Exp        -- procedure abstraction
      ⦅if_␣_␣_⦆    : Exp → Exp → Exp → Exp  -- conditional choice
      ⦅set!_␣_⦆    : Ide → Exp → Exp        -- assignment
    data Exp⋆      : Set where              -- expression sequences
      ␣␣␣          : Exp⋆                   -- empty sequence
      _␣␣_         : Exp → Exp⋆ → Exp⋆      -- sequence prefix
  variable E : Exp; E⋆ : Exp⋆
```

Procedure application can take any number of argument expressions. The Agda
formalisation of the abstract syntax represents the empty sequence by `␣␣␣`,
and sequence prefixing by `E ␣␣ E⋆`. The full Scheme language includes several
forms of lambda-expression, allowing a fixed number of arguments to be named;
for simplicity, the Scm sublanguage includes only the form where a single
identifier corresponds to the entire sequence of argument values.

## Definitions and Programs

The Scheme standards do not specify abstract syntax for definitions and
programs. The Agda formalisation of them in the Scm sublanguage uses notation
close to their concrete syntax in Scheme.

```agda
  mutual
    data Body      : Set where             -- bodies
      ␣␣_          : Exp → Body            -- expression body
      ⦅define_␣_⦆  : Ide → Exp → Body      -- definition body
      ⦅begin_⦆     : Body⁺ → Body          -- body sequence
    data Body⁺     : Set where             -- body sequences
      ␣␣_          : Body → Body⁺          -- empty sequence
      _␣␣_         : Body → Body⁺ → Body⁺  -- sequence prefix
  data Prog        : Set where             -- programs
    ␣␣␣            : Prog                  -- empty program
    ␣␣_            : Body⁺ → Prog          -- body sequence program
  variable B : Body; B⁺ : Body⁺; Π : Prog
```