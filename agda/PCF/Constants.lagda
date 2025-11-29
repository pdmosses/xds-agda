\begin{code}
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module PCF.Constants where

open import Data.Bool.Base 
  using (Bool; true; false; if_then_else_)
open import Agda.Builtin.Nat
  using (Nat; _+_; _-_; _==_)

open import PCF.Domain-Notation
  using (⟪_⟫; η; _♯; fix; ⊥; _⟶_,_)
open import PCF.Types
  using (Types; o; ι; _⇒_; σ; 𝒟)

-- Syntax

data ℒ : Types → Set where
  tt   : ℒ o
  ff   : ℒ o
  ⊃ᵢ   : ℒ (o ⇒ ι ⇒ ι ⇒ ι)
  ⊃ₒ   : ℒ (o ⇒ o ⇒ o ⇒ o)
  Y    : {σ : Types} → ℒ ((σ ⇒ σ) ⇒ σ)
  k    : (n : Nat) → ℒ ι
  +1′  : ℒ (ι ⇒ ι)
  -1′  : ℒ (ι ⇒ ι)
  Z    : ℒ (ι ⇒ o)

variable c : ℒ σ

-- Semantics

𝒜⟦_⟧ : ℒ σ → ⟪ 𝒟 σ ⟫

𝒜⟦ tt   ⟧ =  η true
𝒜⟦ ff   ⟧ =  η false
𝒜⟦ ⊃ᵢ   ⟧ =  _⟶_,_
𝒜⟦ ⊃ₒ   ⟧ =  _⟶_,_
𝒜⟦ Y    ⟧ =  fix
𝒜⟦ k n  ⟧ =  η n
𝒜⟦ +1′  ⟧ =  (λ n → η (n + 1)) ♯
𝒜⟦ -1′  ⟧ =  (λ n → if n == 0 then ⊥ else η (n - 1)) ♯
𝒜⟦ Z    ⟧ =  (λ n → η (n == 0)) ♯
\end{code}