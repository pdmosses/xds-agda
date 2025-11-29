\begin{code}
module LC.Domains where

open import Function
  using (Inverse; _↔_) public
open Inverse {{ ... }}
  using (to; from) public

postulate
  Domain : Set₁
  ⟪_⟫ : Domain → Set
  D∞ : Domain
postulate
  instance iso : ⟪ D∞ ⟫ ↔ (⟪ D∞ ⟫ → ⟪ D∞ ⟫)

variable d : ⟪ D∞ ⟫
\end{code}

The PCF example illustrates declaration of a domain of functions.