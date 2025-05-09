\begin{code}
{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module ULC.Checks where

open import ULC.Domains
open import ULC.Variables
open import ULC.Terms
open import ULC.Semantics

open import Relation.Binary.PropositionalEquality using (refl)
open Inverse using (inverseˡ; inverseʳ)

to-from-elim : ∀ {f}  →  to (from f)  ≡ f
to-from-elim  = inverseˡ iso refl

from-to-elim : ∀ {d}  →  from (to d)  ≡ d
from-to-elim  = inverseʳ iso refl

{-# REWRITE to-from-elim #-}

-- The following proofs are potentially unsound,
-- due to rewriting using the postulated iso

-- (λx1.x1)x42 = x42
check-id :
  ⟦ app (lam (x 1) (var x 1))
        (var x 42) ⟧ ≡ ⟦ var x 42 ⟧
check-id = refl

-- (λx1.x42)x0 = x42
check-const :
  ⟦ app (lam (x 1) (var x 42))
        (var x 0) ⟧ ≡ ⟦ var x 42 ⟧
check-const = refl 

-- (λx0.x0 x0)(λx0.x0 x0) = ...
-- check-divergence :
--   ⟦ app (lam (x 0) (app (var x 0) (var x 0))) 
--         (lam (x 0) (app (var x 0) (var x 0))) ⟧
--   ≡ ⟦ var x 42 ⟧
-- check-divergence = refl 

-- (λx1.x42)((λx0.x0 x0)(λx0.x0 x0)) = x42
check-convergence :
  ⟦ app (lam (x 1) (var x 42))
        (app (lam (x 0) (app (var x 0) (var x 0))) 
             (lam (x 0) (app (var x 0) (var x 0)))) ⟧
  ≡ ⟦ var x 42 ⟧
check-convergence = refl 

-- (λx1.x1)(λx1.x42) = λx2.x42
check-abs :
  ⟦ app (lam (x 1) (var x 1))
        (lam (x 1) (var x 42)) ⟧
     ≡ ⟦ lam (x 2) (var x 42) ⟧
check-abs = refl

-- (λx1.(λx42.x1)x2)x42 = x42
check-free :
  ⟦ app (lam (x 1) 
          (app (lam (x 42) (var x 1))
               (var x 2)))
        (var x 42) ⟧ ≡ ⟦ var x 42 ⟧
check-free = refl
\end{code} 