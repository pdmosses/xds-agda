# Domain Equations

Simply defining `D∞ = (D∞ →ᶜ D∞)` would lead to non-termination of the Agda type-checker.
Instead, we postulate the domain `D∞`, together with a bijection `D∞ ≅ (D∞ →ᶜ D∞)`.
This declares `unfold : ⟪ D∞ →ᶜ (D∞ →ᶜ D∞) ⟫` and `fold : ⟪ (D∞ →ᶜ D∞) →ᶜ D∞ ⟫`.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Examples.LC.Domain-Equations where
--"hide"

open import Examples.LC.Abstract-Syntax
open import Notation
open Recursion using (_≅_; fold; unfold) public

--"/hide"
postulate
  D∞ : Domain                      -- corresponds to Scott's domain 
  instance eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)  -- bijection
--"hide"
variable δ : ⟪ D∞ ⟫

--"/hide"
Env = Var →ˢ D∞  -- environments
--"hide"
variable ρ : ⟪ Env ⟫
--"/hide"
```
Use of the conventional notation `ρ [ δ / v ]` for updating an environment `ρ` to map `v` to `d`
requires an equality test for variables@latex, elided here@/latex.
```agda
--"hide"
open Notation.Flat.Booleans using (Bool; Eq; _==_)
open Notation.Flat.Naturals using (eqNat)
_==ⱽ_ : Var → Var → Bool
open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public
open Notation.Updates using (_[_/_]) public
(x n ==ⱽ x n′) = (n ==ᴺ n′)
instance eqVar : Eq Var
_==_ {{eqVar}} = _==ⱽ_
--"/hide"
```