\begin{code}
module ULC.Domains where

open import Function
  using (Inverse; _↔_) public
open Inverse {{ ... }}
  using (to; from) public

postulate   -- unsound!
  D∞ : Set
  instance  iso : D∞ ↔ (D∞ → D∞)

variable d : D∞
\end{code} 