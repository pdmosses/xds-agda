\begin{code}
module ULC.Domains where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl) public

Domain = Set

postulate ⊥        : {D : Domain} → D

postulate fix      : {D : Domain} → (D → D) → D

postulate fix-fix  : ∀ {D} → (f : D → D) → fix f ≡ f (fix f)

postulate fix-app  : ∀ {P D} → (f : (P → D) → (P → D)) (p : P) → fix f p ≡ f (fix f) p

open import Function using (Inverse; _↔_) public

postulate D∞ : Domain
postulate instance iso : D∞ ↔ (D∞ → D∞)
open Inverse {{ ... }} using (to; from) public

variable d : D∞
\end{code}