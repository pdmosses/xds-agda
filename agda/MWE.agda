module MWE where

open import Data.Bool.Base

variable A B : Set

record Eq (A : Set) : Set where
  field
    _==_ : A → A → Bool

open Eq {{...}} public

-- f [ b / a ] updates f to map a to b

_[_/_] : {{Eq A}} → (A → B) → B → A → (A → B)
f [ b / a ] = λ a′ → if a == a′ then b else f a′

-- Trying to generalise to typed maps (t : Types) → Var t → Val t

data Types : Set where
  t1 t2 : Types

data Var (σ : Types) : Set where
  v1 v2 : Var σ

postulate Val : Types → Set

Env = (t : Types) → Var t → Val t

variable t : Types; v : Var t; ρ : Env

_==ᵀ_ : Types → Types → Bool
_ ==ᵀ _ = false

_==ⱽ_ : {t : Types} → Var t → Var t → Bool
_ ==ⱽ _ = false

instance
  eqT : Eq Types
  _==_ {{eqT}} = _==ᵀ_

instance
  eqV : ∀ {t} → Eq (Var t)
  _==_ {{eqV}} = _==ⱽ_

-- ρ ! t [ x / v ] should update ρ to map t to ρ t [ x / v ]
-- when x : Val t and v : Var t

_!_[_/_] : Env → (t : Types) → Val t → Var t → Env
ρ ! t [ x / v ] = ρ [ ρ t [ x / v ] / t ]

-- Agda v2.8.0
-- Error
-- /Users/pdm/Projects/Agda/xds-agda/agda/MWE.agda:50,19-42: error: [MetaCannotDependOn]
-- Cannot instantiate the metavariable _B_57 to solution
-- Var t₁ → Val t₁ since it contains the variable t₁
-- which is not in scope of the metavariable
-- when checking that the inferred type of an application
--   Types → _B_57
-- matches the expected type
--   (t₁ : Types) → Var t₁ → Val t₁