{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.LC.Domain-Equations where

open import Examples.LC.Abstract-Syntax
open import Notation
open Recursion using (_≅_; fold; unfold) public

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
instance eqVar : Eq Var
_==_ {{eqVar}} = _==ⱽ_