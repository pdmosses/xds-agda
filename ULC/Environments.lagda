\begin{code}
module ULC.Environments where

open import ULC.Variables
open import ULC.Domains
open import Data.Bool using (if_then_else_)

Env = Var → D∞
-- the initial environment for a closed term is λ v → ⊥

variable ρ : Env

_[_/_] : Env → D∞ → Var → Env
ρ [ d / v ] = λ v′ → if v == v′ then d else ρ v′
\end{code}