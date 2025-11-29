\begin{code}
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module Scm.Notation where

open import Data.Bool.Base    using (Bool; false; true) public
open import Data.Nat.Base     renaming (ℕ to Nat) using (suc) public
open import Data.String.Base  using (String) public
open import Data.Unit.Base    using (⊤)
open import Function          using (id; _∘_) public

postulate
  Domain  : Set₁
  ⟪_⟫     : Domain → Set

variable
  A B C   : Set
  D E F   : Domain
  n       : Nat

------------------------------------------------------------------------
-- Domains

postulate
  ⊥ : ⟪ D ⟫  -- bottom element

------------------------------------------------------------------------
-- Function domains

postulate
  _→ᶜ_     : Domain → Domain → Domain      -- assume continuous
  _→ˢ_     : Set    → Domain → Domain      -- always continuous
  dom-cts  : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  set-cts  : ⟪ A →ˢ E ⟫ ≡ (A → ⟪ E ⟫)

{-# REWRITE dom-cts set-cts #-}

postulate
  fix : ⟪ (D →ᶜ D) →ᶜ D ⟫  -- fixed point of endofunction

------------------------------------------------------------------------
-- Flat domains

postulate
  _+⊥    : Set → Domain               -- lifted set
  η      : ⟪ A →ˢ A +⊥ ⟫              -- inclusion
  _♯     : ⟪ (A →ˢ D) →ᶜ A +⊥ →ᶜ D ⟫  -- Kleisli extension

Bool⊥    = Bool +⊥                    -- truth value domain
Nat⊥     = Nat +⊥                     -- natural number domain
String⊥  = String +⊥                  -- meta-string domain

postulate
  _==⊥_  : ⟪ Nat⊥ →ᶜ Nat →ˢ Bool⊥ ⟫   -- strict numerical equality
  _>=⊥_  : ⟪ Nat⊥ →ᶜ Nat →ˢ Bool⊥ ⟫   -- strict greater or equal
  _⟶_,_  : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫   -- McCarthy conditional

------------------------------------------------------------------------
-- Sum domains

postulate
  _+_    : Domain → Domain → Domain                 -- separated sum
  inj₁   : ⟪ D →ᶜ D + E ⟫                            -- injection
  inj₂   : ⟪ E →ᶜ D + E ⟫                            -- injection
  [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ (D + E →ᶜ F) ⟫  -- case analysis

------------------------------------------------------------------------
-- Product domains

postulate
  _×_   : Domain → Domain → Domain   -- cartesian product
  _,_   : ⟪ D →ᶜ E →ᶜ D × E ⟫         -- pairing
  _↓²1  : ⟪ D × E →ᶜ D ⟫              -- 1st projection
  _↓²2  : ⟪ D × E →ᶜ E ⟫              -- 2nd projection
  _↓³1  : ⟪ D × E × F →ᶜ D ⟫          -- 1st projection
  _↓³2  : ⟪ D × E × F →ᶜ E ⟫          -- 2nd projection
  _↓³3  : ⟪ D × E × F →ᶜ F ⟫          -- 3rd projection

------------------------------------------------------------------------
-- Tuple domains

_^_ : Domain → Nat → Domain        -- D ^ n  n-tuples
D ^ 0            = ⊤ +⊥ 
D ^ 1            = D
D ^ suc (suc n)  = D × (D ^ suc n)

------------------------------------------------------------------------
-- Finite sequence domains

postulate
  _⋆     : Domain → Domain         -- D ⋆ domain of finite sequences 
  ⟨⟩     : ⟪ D ⋆ ⟫                 -- empty sequence
  ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫  -- ⟨ d₁ , ... , dₙ₊₁ ⟩ non-empty sequence
  #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫         -- # d⋆                sequence length
  _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫   -- d⋆ § d⋆             concatenation
  _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫     -- d⋆ ↓ n              nth component
  _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫   -- d⋆ † n              nth tail

------------------------------------------------------------------------
-- Grouping precedence

infixr 0  _→ᶜ_
infixr 0  _→ˢ_
infixr 1   _+_
infixr 2   _×_
infixr 4   _,_
infix  8   _^_
infix  10   _+⊥
infixr 20  _⟶_,_

-- ⟦_⟧ = id
\end{code}  