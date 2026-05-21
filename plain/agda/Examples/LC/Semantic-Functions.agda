{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Examples.LC.Semantic-Functions where

open import Examples.LC.Abstract-Syntax
open import Examples.LC.Domain-Equations
open import Notation

⟦_⟧ : Exp → ⟪ Env →ᶜ D∞ ⟫
⟦ var v ⟧ ρ        = ρ v
⟦ ⦅λ v ␣ e ⦆ ⟧ ρ   = fold ( λ δ → ⟦ e ⟧ (ρ [ δ / v ]) )
⟦ ⦅ e₁ ␣ e₂ ⦆ ⟧ ρ  = unfold ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )