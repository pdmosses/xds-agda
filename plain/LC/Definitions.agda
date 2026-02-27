
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module LC.Definitions where

open import Notation

module Abstract-Syntax where

  open import Data.Nat.Base renaming (ℕ to Nat) using () public
  data Var : Set where
    x : Nat → Var
  variable v : Var

  data Exp : Set where
    val_    : Var → Exp
    ⦅λ_␣_⦆  : Var → Exp → Exp
    ⦅_␣_⦆   : Exp → Exp → Exp
  variable e e₁ e₂ : Exp

module Domain-Equations where
  open Abstract-Syntax
  open Notation.Recursion using (_≅_; fold; unfold) public
  postulate
    D∞ : Domain
    instance eqD∞ : D∞ ≅ (D∞ →ᶜ D∞)

  Env = Var →ˢ D∞
  variable ρ : ⟪ Env ⟫

  open Notation.Flat.Booleans using (Bool; Eq; _==_)
  _==ⱽ_ : Var → Var → Bool
  open import Data.Nat.Base using (_≡ᵇ_) public
  open Notation.Updates using (_[_/_]) public
  (x n ==ⱽ x n′) = (n ≡ᵇ n′)
  instance eqVar : Eq Var; _==_ {{eqVar}} = _==ⱽ_

module Semantic-Functions where
  open Abstract-Syntax
  open Domain-Equations
  ⟦_⟧ : Exp → ⟪ Env →ᶜ D∞ ⟫
  ⟦ val v ⟧ ρ        = ρ v
  ⟦ ⦅λ v ␣ e ⦆ ⟧ ρ   = fold ( λ δ → ⟦ e ⟧ (ρ [ δ / v ]) )
  ⟦ ⦅ e₁ ␣ e₂ ⦆ ⟧ ρ  = unfold ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )
