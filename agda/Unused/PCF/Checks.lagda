\begin{code}
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module PCF.Checks where

open import Data.Bool.Base 
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong-app)

open import PCF.Domain-Notation
open import PCF.Types
open import PCF.Constants
open import PCF.Variables
open import PCF.Environments
open import PCF.Terms

{-# REWRITE fix-fix elim-♯-η elim-♯-⊥ true-cond false-cond #-} 

-- Constants
pattern 𝑁 n    = 𝐿 (k n)
pattern succ   = 𝐿 +1′
pattern pred⊥  = 𝐿 -1′
pattern if     = 𝐿 ⊃ᵢ
pattern 𝑌      = 𝐿 Y
pattern 𝑍     = 𝐿 Z

-- Variables
f  = var 0 ι
g  = var 1 (ι ⇒ ι)
h  = var 2 (ι ⇒ ι ⇒ ι)
a  = var 3 ι
b  = var 4 ι

-- Arithmetic
check-41+1 : 𝒜′⟦ succ ␣ 𝑁 41 ⟧ ρ⊥ ≡ η 42
check-41+1 = refl

check-43-1 : 𝒜′⟦ pred⊥ ␣ 𝑁 43 ⟧ ρ⊥ ≡ η 42
check-43-1 = refl

-- Binding
check-id : 𝒜′⟦ (ƛ a ␣ 𝑉 a) ␣ 𝑁 42 ⟧ ρ⊥ ≡ η 42
check-id = refl

check-k : 𝒜′⟦ (ƛ a ␣ ƛ b ␣ 𝑉 a) ␣ 𝑁 42 ␣ 𝑁 41 ⟧ ρ⊥ ≡ η 42
check-k = refl

check-ki : 𝒜′⟦ (ƛ a ␣ ƛ b ␣ 𝑉 b) ␣ 𝑁 41 ␣ 𝑁 42 ⟧ ρ⊥ ≡ η 42
check-ki = refl

\end{code}
\clearpage
\begin{code}
check-suc-41 : 𝒜′⟦ (ƛ a ␣ (succ ␣ 𝑉 a )) ␣ 𝑁 41 ⟧ ρ⊥ ≡ η 42
check-suc-41 = refl

check-pred-42 : 𝒜′⟦ (ƛ a ␣ (pred⊥ ␣ 𝑉 a)) ␣ 𝑁 43 ⟧ ρ⊥ ≡ η 42
check-pred-42 = refl

check-if-zero : 𝒜′⟦ if ␣ (𝑍 ␣ 𝑁 0) ␣ 𝑁 42 ␣ 𝑁 0 ⟧ ρ⊥ ≡ η 42
check-if-zero = refl

check-if-nonzero : 𝒜′⟦ if ␣ (𝑍 ␣ 𝑁 42) ␣ 𝑁 0 ␣ 𝑁 42 ⟧ ρ⊥ ≡ η 42
check-if-nonzero = refl

-- fix (λf. 42) ≡ 42
check-fix-const :
  𝒜′⟦ 𝑌 ␣ (ƛ f ␣ 𝑁 42) ⟧ ρ⊥ 
  ≡ η 42
check-fix-const = fix-fix (λ x → η 42)

-- fix (λg. λa. 42) 2 ≡ 42
check-fix-lambda :
  𝒜′⟦ 𝑌 ␣ (ƛ g ␣ ƛ a ␣ 𝑁 42) ␣ 𝑁 2 ⟧ ρ⊥ 
  ≡ η 42
check-fix-lambda = refl

-- fix (λg. λa. ifz a then 42 else g (pred a)) 5 ≡ 42
check-countdown :
  𝒜′⟦ 𝑌 ␣ (ƛ g ␣ ƛ a ␣
              (if ␣ (𝑍 ␣ 𝑉 a) ␣ 𝑁 42 ␣ (𝑉 g ␣ (pred⊥ ␣ 𝑉 a))))
      ␣ 𝑁 5
    ⟧ ρ⊥ 
  ≡ η 42
check-countdown = refl

-- fix (λh. λa. λb. ifz a then b else h (pred a) (succ b)) 2 40 ≡ 42
check-sum-42 :
  𝒜′⟦ (𝑌 ␣ (ƛ h ␣ ƛ a ␣ ƛ b ␣
              (if ␣ (𝑍 ␣ 𝑉 a) ␣ 𝑉 b ␣ (𝑉 h ␣ (pred⊥ ␣ 𝑉 a) ␣ (succ ␣ 𝑉 b)))))
      ␣ 𝑁 2 ␣ 𝑁 40
    ⟧ ρ⊥
  ≡ η 42
check-sum-42 = refl
-- Exponential in first arg?
\end{code}