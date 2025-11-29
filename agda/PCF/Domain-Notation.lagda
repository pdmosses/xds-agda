\begin{code}
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module PCF.Domain-Notation where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_) public

------------------------------------------------------------------------
-- Domains

postulate
  Domain  : Set₁
  ⟪_⟫     : Domain → Set

variable
  D E : Domain
  P : Set
  d₁ d₂ : Set

postulate
  ⊥ : ⟪ D ⟫  -- bottom element

------------------------------------------------------------------------
-- Function domains

postulate
  _→ᶜ_     : Domain → Domain → Domain      -- assume continuous
  _→ˢ_     : Set    → Domain → Domain      -- always continuous
  dom-cts  : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  set-cts  : ⟪ P →ˢ E ⟫ ≡ (P → ⟪ E ⟫)

{-# REWRITE dom-cts set-cts #-}

postulate
  fix : ⟪ (D →ᶜ D) →ᶜ D ⟫  -- fixed point of endofunction

  -- Properties
  fix-fix : (f : ⟪ D →ᶜ D ⟫) → fix f ≡ f (fix f)

-- Flat domains

postulate
  _+⊥    : Set → Domain               -- lifted set
  η      : ⟪ P →ˢ P +⊥ ⟫              -- inclusion
  _♯     : ⟪ (P →ˢ D) →ᶜ P +⊥ →ᶜ D ⟫  -- Kleisli extension

  -- Properties
  elim-♯-η  : (f : ⟪ P →ˢ D ⟫) (p : P) →  (f ♯) (η p)  ≡ f p
  elim-♯-⊥  : (f : ⟪ P →ˢ D ⟫) →          (f ♯) ⊥      ≡ ⊥

-- McCarthy conditional

-- t ⟶ d₁ , d₂ : ⟪ D ⟫  (t : Bool +⊥ ; d₁, d₂ : ⟪ D ⟫)

open import Data.Bool.Base
  using (Bool; true; false; if_then_else_) public

postulate
  _⟶_,_  : ⟪ Bool +⊥ →ᶜ D →ᶜ D →ᶜ D ⟫   -- McCarthy conditional

  -- Properties
  true-cond    : {d₁ d₂ : ⟪ D ⟫} → (η true ⟶ d₁ , d₂)  ≡ d₁
  false-cond   : {d₁ d₂ : ⟪ D ⟫} → (η false ⟶ d₁ , d₂) ≡ d₂
  bottom-cond  : {d₁ d₂ : ⟪ D ⟫} → (⊥ ⟶ d₁ , d₂)       ≡ ⊥

infixr 0  _→ᶜ_
infixr 0  _→ˢ_
infix  10   _+⊥
infixr 20  _⟶_,_
\end{code}