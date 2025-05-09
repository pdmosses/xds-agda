\begin{code}
module ULC.Domains where

open import Function
  using (Inverse; _↔_) public
open Inverse {{ ... }}
  using (to; from) public

postulate
  D∞ : Set
postulate
  instance iso : D∞ ↔ (D∞ → D∞)

variable d : D∞
\end{code} 