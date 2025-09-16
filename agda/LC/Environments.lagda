\begin{code}
module Environments where

open import Variables
open import Domains
open import Data.Bool using (if_then_else_)

Env = Var → D∞

variable ρ : Env

_[_/_] : Env → D∞ → Var → Env
ρ [ d / v ] = λ v′ → if v == v′ then d else ρ v′
\end{code}