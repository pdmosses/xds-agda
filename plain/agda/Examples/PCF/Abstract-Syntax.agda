{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.PCF.Abstract-Syntax where

open import Notation

data Types  : Set where                          -- type terms
  ι         : Types                              -- individuals
  o         : Types                              -- truth-values
  _⇒_       : Types → Types → Types              -- functions
infixr 1 _⇒_
variable σ τ : Types

open import Agda.Builtin.Nat public using (Nat)

data Vars   : Types → Set where                  -- typed variables
  α         : Nat → (σ : Types) → Vars σ         -- α i σ is a variable of type σ
variable i  : Nat

data ℒᴬ     : Types → Set where                  -- typed constants
  tt        : ℒᴬ o                               -- true
  ff        : ℒᴬ o                               -- false
  ⊃         : ℒᴬ (o ⇒ σ ⇒ σ ⇒ σ)                 -- conditional
  Y         : ℒᴬ ((σ ⇒ σ) ⇒ σ)                   -- fixed point
  k         : Nat → ℒᴬ ι                         -- numerals
  ⦅+1⦆      : ℒᴬ (ι ⇒ ι)                         -- successor
  ⦅−1⦆      : ℒᴬ (ι ⇒ ι)                         -- predecessor
  Z         : ℒᴬ (ι ⇒ o)                         -- zero test
variable c  : ℒᴬ σ

data Terms  : Types → Set where                  -- typed terms
  𝑉_        : Vars σ → Terms σ                   -- variable
  𝐿_        : ℒᴬ σ → Terms σ                     -- constant
  ⦅_␣_⦆     : Terms (σ ⇒ τ) → Terms σ → Terms τ  -- function application
  ⦅λ_␣_⦆    : Vars σ → Terms τ → Terms (σ ⇒ τ)   -- function abstraction
variable M N : Terms σ