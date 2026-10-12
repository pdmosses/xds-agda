# Domain Equations

Simply defining `D∞ = (D∞ →ᶜ D∞)` would lead to non-termination of the Agda type-checker.
Instead, we postulate the domain `D∞`, together with a bijection `D∞ ≅ (D∞ →ᶜ D∞)`.
This declares the operations
`unfold : ⟪ D∞ →ᶜ (D∞ →ᶜ D∞) ⟫` and `fold : ⟪ (D∞ →ᶜ D∞) →ᶜ D∞ ⟫`
associated with [recursive domains].
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Examples.LC.Domain-Equations where
--"hide"

  open import Examples.LC.Abstract-Syntax
  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Recursion
  open import Notation.Flat.Booleans
  open import Notation.Flat.Naturals
  open import Notation.Updates
  open import Agda.Builtin.Nat renaming (_==_ to _==ᴺ_) public

--"/hide"
  postulate
    D∞ : Domain                      -- corresponds to Scott's domain 
    instance eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)  -- bijection
--"hide"
  variable δ : ⟪ D∞ ⟫

--"/hide"
  Env = Var →ˢ D∞                    -- environments
--"hide"
  variable ρ : ⟪ Env ⟫
--"/hide"
```
Use of the conventional notation `ρ [ δ / v ]` for updating an environment `ρ` to map `v` to `δ`
requires an equality test for variables@latex; its definition is elided here@/latex.
```agda
--"hide"
  _==ⱽ_ : Var → Var → Bool
  (x n ==ⱽ x n′) = (n ==ᴺ n′)
  instance eqVar : Eq Var
  _==_ {{eqVar}} = _==ⱽ_
--"/hide"
```

[recursive domains]: ../../Notation/Recursion.md#recursive-domains
