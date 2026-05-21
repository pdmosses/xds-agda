# Abstract Syntax

The following abstract syntax of well-formed PCF terms in Agda uses indexed datatype definitions.
PCF function types $\sigma \to \tau$ are written `σ ⇒ τ`, and variables $\alpha_i^\sigma$ are written `α i σ`
(where the argument `i` merely distinguishes between variables – it is *not* a De Bruin index).
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Examples.PCF.Abstract-Syntax where

--"hide"
open import Notation

--"/hide"
data Types  : Set where                          -- type terms
  ι         : Types                              -- individuals
  o         : Types                              -- truth-values
  _⇒_       : Types → Types → Types              -- functions
--"hide"
infixr 1 _⇒_
variable σ τ : Types

open import Agda.Builtin.Nat public using (Nat)
--"/hide"

data Vars   : Types → Set where                  -- typed variables
  α         : Nat → (σ : Types) → Vars σ         -- α i σ is a variable of type σ
--"hide"
variable i  : Nat
--"/hide"

data ℒᴬ     : Types → Set where                  -- typed constants
  tt        : ℒᴬ o                               -- true
  ff        : ℒᴬ o                               -- false
  ⊃         : ℒᴬ (o ⇒ σ ⇒ σ ⇒ σ)                 -- conditional
  Y         : ℒᴬ ((σ ⇒ σ) ⇒ σ)                   -- fixed point
  k         : Nat → ℒᴬ ι                         -- numerals
  ⦅+1⦆      : ℒᴬ (ι ⇒ ι)                         -- successor
  ⦅−1⦆      : ℒᴬ (ι ⇒ ι)                         -- predecessor
  Z         : ℒᴬ (ι ⇒ o)                         -- zero test
--"hide"
variable c  : ℒᴬ σ
--"/hide"

data Terms  : Types → Set where                  -- typed terms
  𝑉_        : Vars σ → Terms σ                   -- variable
  𝐿_        : ℒᴬ σ → Terms σ                     -- constant
  ⦅_␣_⦆     : Terms (σ ⇒ τ) → Terms σ → Terms τ  -- function application
  ⦅λ_␣_⦆    : Vars σ → Terms τ → Terms (σ ⇒ τ)   -- function abstraction
--"hide"
variable M N : Terms σ
--"/hide"
```