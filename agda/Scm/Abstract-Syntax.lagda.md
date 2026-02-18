# Abstract Syntax

```agda
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Abstract-Syntax where
```

## Identifiers

In the concrete syntax of the full Scheme programming language, identifiers
can be almost arbitrary sequences of characters. For abstract syntax in Agda,
it is convenient to represent identifiers as strings.

```agda
  open import Data.String.Base using (String) public
  Ide = String
  variable I : Ide
```

## Literal Constants

The abstract syntax of the Scm sublanguage restricts constants to integers
and truth values. THe Agda formalisation uses the constructor `int` to include
integers as ASTs in `Con`, and the standard Scheme notation `#t` and `#f` for
the truth values.

```agda
  open import Data.Integer.Base renaming (ℤ to Int) using () public
  data Con : Set where
    int : Int → Con
    #t #f : Con
  variable K : Con
```

## Expressions

Scheme expressions include function application, lambda-abstraction,
conditional choice, and assignment. The constructors used in the Agda
formalisation correspond closely to the concrete syntax of Scheme.

```agda
  mutual
    data Exp : Set where
      con          : Con → Exp
      ide          : Ide → Exp
      ⦅_␣_⦆        : Exp → Exp⋆ → Exp
      ⦅lambda_␣_⦆  : Ide → Exp → Exp
      ⦅if_␣_␣_⦆    : Exp → Exp → Exp → Exp
      ⦅set!_␣_⦆    : Ide → Exp → Exp
    data Exp⋆ : Set where
      ␣␣␣ : Exp⋆
      _␣␣_ : Exp → Exp⋆ → Exp⋆
  variable E : Exp; E⋆ : Exp⋆
```

Function application can take any number of argument expressions. The Agda
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
    data Body : Set where
      ␣␣_          : Exp → Body
      ⦅define_␣_⦆  : Ide → Exp → Body
      ⦅begin_⦆     : Body⁺ → Body
    data Body⁺ : Set where
      ␣␣_ : Body → Body⁺
      _␣␣_ : Body → Body⁺ → Body⁺
  data Prog : Set where
    ␣␣␣ : Prog; ␣␣_ : Body⁺ → Prog
  variable B : Body; B⁺ : Body⁺; Π : Prog
```