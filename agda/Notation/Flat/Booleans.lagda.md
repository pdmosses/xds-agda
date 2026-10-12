# Booleans

The McCarthy conditional operation `β ⟶ δ₁ , δ₂` extends the usual ternary
conditional choice to domains. It returns `⊥` whenever its first argument is `⊥`.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Notation.Flat.Booleans where
--"hide"

  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Flat
--"/hide"
  open import Data.Bool.Base public using (Bool; false; true; if_then_else_; not)

  Bool⊥ = Bool +⊥
  _⟶_,_ : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫    -- β ⟶ δ₁ , δ₂ is conditional choice
  _⟶_,_ = (λ b δ₁ δ₂ → if b then δ₁ else δ₂) ♯  
--"hide"
  infixr 20 _⟶_,_
--"/hide"
```
This module also defines `Eq A` for use as an instance parameter,
restricting operation definitions to types `A` such that `_==_ : A → A → Bool`:
```agda
  record Eq (A : Set) : Set where field _==_ : A → A → Bool
  open Eq {{...}} public
```
The `Bool⊥`-valued operation `δ₁ ==⊥ δ₂` on `A +⊥` gives `⊥` when either operand is `⊥`:
```agda
  _==⊥_ : {{Eq A}} → ⟪ (A +⊥) →ᶜ (A +⊥) →ᶜ Bool⊥ ⟫
  δ₁ ==⊥ δ₂ = ((λ a₁ → (((λ a₂ → ↑ (a₁ == a₂)) ♯) δ₂)) ♯) δ₁

  instance 
    eqBool : Eq Bool
    _==_ {{eqBool}} b₁ b₂ = if b₁ then b₂ else not b₂
```
