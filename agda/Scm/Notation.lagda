\begin{code}
module Scm.Notation where

open import Data.Bool.Base    using (Bool; false; true) public
open import Data.Nat.Base     renaming (ℕ to Nat) using (suc) public
open import Data.String.Base  using (String) public
open import Data.Unit.Base    using (⊤)
open import Function          using (id; _∘_) public

Domain = Set -- unsound!

variable
  A B C  : Set
  D E F  : Domain
  n      : Nat

------------------------------------------------------------------------
-- Domains

postulate
  ⊥ : D              -- bottom element
  fix : (D → D) → D  -- fixed point of endofunction

------------------------------------------------------------------------
-- Flat domains

postulate
  _+⊥    : Set → Domain          -- lifted set
  η      : A → A +⊥              -- inclusion
  _♯     : (A → D) → (A +⊥ → D)  -- Kleisli extension

Bool⊥    = Bool +⊥               -- truth value domain
Nat⊥     = Nat +⊥                -- natural number domain
String⊥  = String +⊥             -- meta-string domain

postulate
  _==⊥_  : Nat⊥ → Nat → Bool⊥    -- strict numerical equality
  _>=⊥_  : Nat⊥ → Nat → Bool⊥    -- strict greater or equal
  _⟶_,_  : Bool⊥ → D → D → D     -- McCarthy conditional

------------------------------------------------------------------------
-- Sum domains

postulate
  _+_    : Domain → Domain → Domain         -- separated sum
  inj₁   : D → D + E                        -- injection
  inj₂   : E → D + E                        -- injection
  [_,_]  : (D → F) → (E → F) → (D + E → F)  -- case analysis
\end{code}
\clearpage
\begin{code}
------------------------------------------------------------------------
-- Product domains

postulate
  _×_  : Domain → Domain → Domain  -- cartesian product
  _,_  : D → E → D × E             -- pairing
  _↓²1  : D × E → D                -- 1st projection
  _↓²2  : D × E → E                -- 2nd projection
  _↓³1   : D × E × F → D           -- 1st projection
  _↓³2   : D × E × F → E           -- 2nd projection
  _↓³3   : D × E × F → F           -- 3rd projection
------------------------------------------------------------------------
-- Tuple domains

_^_ : Domain → Nat → Domain   -- D ^ n               n-tuples
D ^ 0            = ⊤
D ^ 1            = D
D ^ suc (suc n)  = D × (D ^ suc n)

------------------------------------------------------------------------
-- Finite sequence domains

postulate
  _⋆     : Domain → Domain    -- D ⋆ domain of finite sequences 
  ⟨⟩     : D ⋆                -- empty sequence
  ⟨_⟩    : (D ^ suc n) → D ⋆  -- ⟨ d₁ , ... , dₙ₊₁ ⟩ non-empty sequence
  #      : D ⋆ → Nat⊥         -- # d⋆                sequence length
  _§_    : D ⋆ → D ⋆ → D ⋆    -- d⋆ § d⋆             concatenation
  _↓_    : D ⋆ → Nat → D      -- d⋆ ↓ n              nth component
  _†_    : D ⋆ → Nat → D ⋆    -- d⋆ † n              nth tail

------------------------------------------------------------------------
-- Grouping precedence

infixr 1   _+_
infixr 2   _×_
infixr 4   _,_
infix  8   _^_
infixr 20  _⟶_,_

⟦_⟧ = id
\end{code}