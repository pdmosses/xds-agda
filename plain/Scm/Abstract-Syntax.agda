
{-# OPTIONS --rewriting --confluence-check #-}

module Scm.Abstract-Syntax where

  open import Data.String.Base public using (String)
  Ide = String      -- identifiers
  variable I : Ide

  open import Data.Integer.Base public renaming (ℤ to Int) using ()
  data Con  : Set where  -- constants
    int     : Int → Con  -- integer numerals
    #t      : Con        -- true
    #f      : Con        -- false
  variable K : Con

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
