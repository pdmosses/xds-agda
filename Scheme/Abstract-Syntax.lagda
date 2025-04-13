\begin{code}

module Scheme.Abstract-Syntax where

open import Scheme.Domain-Notation using (_⋆′)

-- 7.2.1. Abstract syntax

postulate Con  : Set   -- constants, including quotations
postulate Ide  : Set   -- identifiers (variables)
data      Exp  : Set   -- expressions
Com            = Exp   -- commands

data Exp where
  con                : Con → Exp                          -- K
  ide                : Ide → Exp                          -- I
  ⦅_␣_⦆              : Exp → Exp ⋆′ → Exp                 -- (E₀ E⋆′)
  ⦅lambda␣⦅_⦆_␣_⦆    : Ide ⋆′ → Com ⋆′ → Exp → Exp        -- (lambda (I⋆′) Γ⋆′ E₀)
  ⦅lambda␣⦅_·_⦆_␣_⦆  : Ide ⋆′ → Ide → Com ⋆′ → Exp → Exp  -- (lambda (I⋆′.I) Γ⋆′ E₀)
  ⦅lambda_␣_␣_⦆      : Ide → Com ⋆′ → Exp → Exp           -- (lambda I Γ⋆′ E₀)
  ⦅if_␣_␣_⦆          : Exp → Exp → Exp → Exp              -- (if E₀ E₁ E₂)
  ⦅if_␣_⦆            : Exp → Exp → Exp                    -- (if E₀ E₁)
  ⦅set!_␣_⦆          : Ide → Exp → Exp                    -- (set! I E)

variable
  K   : Con
  I   : Ide
  I⋆  : Ide ⋆′
  E   : Exp
  E⋆  : Exp ⋆′
  Γ   : Com
  Γ⋆  : Com ⋆′

\end{code}