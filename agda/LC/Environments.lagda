\begin{code}
module LC.Environments where

open import LC.Variables
open import LC.Domains
open import Data.Bool using (if_then_else_)

Env = Var → ⟪ D∞ ⟫

variable ρ : Env

_[_/_] : Env → ⟪ D∞ ⟫ → Var → Env
ρ [ d / v ] = λ v′ → if v == v′ then d else ρ v′
\end{code}