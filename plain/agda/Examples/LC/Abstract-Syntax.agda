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