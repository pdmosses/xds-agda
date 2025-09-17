\begin{code}
module PCF.Domain-Notation where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_) public

variable D E : Set  -- Set should be a sort of domains

-- Domains are pointed
postulate
  ⊥ : {D : Set} → D

-- Fixed points of endofunctions on function domains

postulate
  fix : {D : Set} → (D → D) → D

  -- Properties
  fix-fix : ∀ {D} (f : D → D) → fix f ≡ f (fix f)

-- Lifted domains

postulate
  𝕃   : Set → Set
  η   : {P : Set} → P → 𝕃 P
  _♯  : {P : Set} {D : Set} → (P → D) → (𝕃 P → D)

  -- Properties
  elim-♯-η  : ∀ {P D} (f : P → D) (p : P) →  (f ♯) (η p)  ≡ f p
  elim-♯-⊥  : ∀ {P D} (f : P → D) →          (f ♯) ⊥      ≡ ⊥

-- Flat domains

_+⊥   : Set → Set
S +⊥  = 𝕃 S

-- McCarthy conditional

-- t ⟶ d₁ , d₂ : D  (t : Bool +⊥ ; d₁, d₂ : D)

open import Data.Bool.Base
  using (Bool; true; false; if_then_else_) public

postulate
  _⟶_,_ : {D : Set} → Bool +⊥ → D → D → D

  -- Properties
  true-cond    : ∀ {D} {d₁ d₂ : D} → (η true ⟶ d₁ , d₂)  ≡ d₁
  false-cond   : ∀ {D} {d₁ d₂ : D} → (η false ⟶ d₁ , d₂) ≡ d₂
  bottom-cond  : ∀ {D} {d₁ d₂ : D} → (⊥ ⟶ d₁ , d₂)       ≡ ⊥
\end{code}