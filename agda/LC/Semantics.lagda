\begin{code}
module Semantics where

open import Variables
open import Terms
open import Domains
open import Environments

⟦_⟧ : Exp → Env → D∞
-- ⟦ e ⟧ ρ is the value of e with ρ giving the values of free variables 

⟦ var  v      ⟧ ρ  = ρ v
⟦ lam  v e    ⟧ ρ  = from ( λ d → ⟦ e ⟧ (ρ [ d / v ]) )
⟦ app  e₁ e₂  ⟧ ρ  = to ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )
\end{code}