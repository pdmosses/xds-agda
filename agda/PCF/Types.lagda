\begin{code}
module PCF.Types where

open import Data.Bool.Base 
  using (Bool)
open import Agda.Builtin.Nat
  using (Nat)

open import PCF.Domain-Notation
  using (_+⊥)

-- Syntax

data Types : Set where
  ι    : Types                  -- natural numbers
  o    : Types                  -- Boolean truthvalues
  _⇒_  : Types → Types → Types  -- functions

variable σ τ : Types

infixr 1 _⇒_

-- Semantics 𝒟

𝒟 : Types → Set  -- Set should be a sort of domains

𝒟 ι        = Nat  +⊥
𝒟 o        = Bool +⊥
𝒟 (σ ⇒ τ)  = 𝒟 σ → 𝒟 τ

variable x y z : 𝒟 σ
\end{code}