\begin{code}
module Terms where

open import Variables

data Exp : Set where
  var_  : Var → Exp         -- variable value
  lam   : Var → Exp → Exp   -- lambda abstraction
  app   : Exp → Exp → Exp   -- application

variable e : Exp
\end{code}