\begin{code}
module LC.Domains where

postulate
  Domain  : Set₁          -- type of all domains
  ⟪_⟫     : Domain → Set  -- carrier of a domain

open import Function    using (Inverse; _↔_)  public
open Inverse {{ ... }}  using (to; from)      public

postulate
  D∞  : Domain

postulate instance
  bi  : ⟪ D∞ ⟫ ↔ (⟪ D∞ ⟫ → ⟪ D∞ ⟫)

variable d : ⟪ D∞ ⟫
\end{code}