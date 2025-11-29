\begin{code}
module LC.Semantics where

open import LC.Variables
open import LC.Terms
open import LC.Domains
open import LC.Environments

⟦_⟧ : Exp → Env → ⟪ D∞ ⟫
-- ⟦ e ⟧ ρ is the value of e with ρ giving the values of free variables 

⟦ var  v      ⟧ ρ  = ρ v
⟦ lam  v e    ⟧ ρ  = from ( λ d → ⟦ e ⟧ (ρ [ d / v ]) )
⟦ app  e₁ e₂  ⟧ ρ  = to ( ⟦ e₁ ⟧ ρ ) ( ⟦ e₂ ⟧ ρ )
\end{code}