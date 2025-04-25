\begin{code}
module ULC.Domains where

open import Relation.Binary.PropositionalEquality.Core using (_≡_) public

variable D : Set   -- Set should be a sort of domains

postulate ⊥        : {D : Set} → D

postulate fix      : {D : Set} → (D → D) → D

postulate fix-fix  : ∀ {D} → (f : D → D) → fix f ≡ f (fix f)

open import Function using (Inverse; _↔_) public

postulate D∞ : Set
postulate instance iso : D∞ ↔ (D∞ → D∞)
open Inverse {{ ... }} using (to; from) public

variable d : D∞
\end{code} 