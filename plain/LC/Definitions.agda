
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module LC.Definitions where

open import Notation

module Abstract-Syntax where

  open import Agda.Builtin.Nat public using (Nat)
  data Var : Set where
    x : Nat → Var
  variable v : Var

  data Exp : Set where
    var_    : Var → Exp        -- variable reference
    ⦅λ_␣_⦆  : Var → Exp → Exp  -- function abstraction
    ⦅_␣_⦆   : Exp → Exp → Exp  -- function application
  variable e e₁ e₂ : Exp

module Domain-Equations where

  open Abstract-Syntax
  open Notation.Recursion using (_≅_; fold; unfold) public
  postulate
    D∞ : Domain                      -- corresponds to Scott's domain 
    instance eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)  -- bijection
  variable δ : ⟪ D∞ ⟫

  Env = Var →ˢ D∞  -- environments
  variable ρ : ⟪ Env ⟫

  open Notation.Flat.Booleans using (Bool; Eq; _==_)
  open Notation.Flat.Naturals using (eqNat)
  _==ⱽ_ : Var → Var → Bool
  open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public
  open Notation.Updates using (_[_/_]) public
  (x n ==ⱽ x n′) = (n ==ᴺ n′)
  instance eqVar : Eq Var; _==_ {{eqVar}} = _==ⱽ_

module Semantic-Functions where

  open Abstract-Syntax
  open Domain-Equations
  ⟦_⟧ : Exp → ⟪ Env →ᶜ D∞ ⟫
  ⟦ var v ⟧ ρ        = ρ v
  ⟦ ⦅λ v ␣ e ⦆ ⟧ ρ   = fold ( λ δ → ⟦ e ⟧ (ρ [ δ / v ]) )
  ⟦ ⦅ e₁ ␣ e₂ ⦆ ⟧ ρ  = unfold ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )
