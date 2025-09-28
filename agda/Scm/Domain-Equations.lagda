\begin{code}
module Scm.Domain-Equations where

open import Scm.Notation
open import Scm.Abstract-Syntax using (Ide; Int)

-- Domain declarations

postulate  𝐋   :  Domain  -- locations
variable   α   :  𝐋
𝐍              :  Domain  -- natural numbers
𝐓              :  Domain  -- booleans
𝐑              :  Domain  -- numbers
𝐏              :  Domain  -- pairs
𝐌              :  Domain  -- miscellaneous
variable   μ   :  𝐌
𝐅              :  Domain  -- procedure values
variable   φ   :  𝐅
postulate  𝐄   :  Domain  -- expressed values
variable   ϵ   :  𝐄
𝐒              :  Domain  -- stores
variable   σ   :  𝐒
𝐔              :  Domain  -- environments
variable   ρ   :  𝐔
𝐂              :  Domain  -- command continuations
variable   θ   :  𝐂
postulate  𝐀   :  Domain  -- answers

𝐄⋆             =  𝐄 ⋆
variable   ϵ⋆  :  𝐄⋆

-- Domain equations

data Misc : Set where null unallocated undefined unspecified : Misc

𝐍     =  Nat⊥
𝐓     =  Bool⊥
𝐑     =  Int +⊥
𝐏     =  𝐋 × 𝐋
𝐌     =  Misc +⊥
𝐅     =  𝐄⋆ → (𝐄 → 𝐂) → 𝐂
-- 𝐄  =  𝐓 + 𝐑 + 𝐏 + 𝐌 + 𝐅
𝐒     =  𝐋 → 𝐄
𝐔     =  Ide → 𝐋
𝐂     =  𝐒 → 𝐀
\end{code}
\iflatex
\clearpage
\fi
\begin{code}
-- Injections, tests, and projections

postulate
  _𝐓-in-𝐄    : 𝐓   → 𝐄
  _∈-𝐓       : 𝐄   → Bool +⊥
  _|-𝐓       : 𝐄   → 𝐓

  _𝐑-in-𝐄    : 𝐑   → 𝐄
  _∈-𝐑       : 𝐄   → Bool +⊥
  _|-𝐑       : 𝐄   → 𝐑

  _𝐏-in-𝐄    : 𝐏  → 𝐄
  _∈-𝐏       : 𝐄   → Bool +⊥
  _|-𝐏       : 𝐄   → 𝐏

  _𝐌-in-𝐄    : 𝐌   → 𝐄
  _∈-𝐌       : 𝐄   → Bool +⊥
  _|-𝐌       : 𝐄   → 𝐌

  _𝐅-in-𝐄    : 𝐅   → 𝐄
  _∈-𝐅       : 𝐄   → Bool +⊥
  _|-𝐅       : 𝐄   → 𝐅

-- Operations on flat domains

postulate
  _==ᴸ_  : 𝐋 → 𝐋 → 𝐓
  _==ᴹ_  : 𝐌 → 𝐌 → 𝐓
  _==ᴿ_  : 𝐑 → 𝐑 → 𝐓
  _==ᵀ_  : 𝐓 → 𝐓 → 𝐓
  _<ᴿ_   : 𝐑 → 𝐑 → 𝐓
  _+ᴿ_   : 𝐑 → 𝐑 → 𝐑
  _∧ᵀ_   : 𝐓 → 𝐓 → 𝐓
\end{code}