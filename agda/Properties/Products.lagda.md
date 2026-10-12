# Product Domains

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Properties.Products where

  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Products using (_×_; _,_; _↓₁; _↓₂) public

  variable δ : ⟪ D ⟫; ε : ⟪ E ⟫
  postulate
    elim-↓₁   :  ( δ , ε ) ↓₁     ≡  δ
    elim-↓₂   :  ( δ , ε ) ↓₂     ≡  ε
    elim-⊥-⊥  :  ( ⊥{D} , ⊥{E} )  ≡  ⊥{D × E}
  {-# REWRITE elim-↓₁ elim-↓₂ #-} 
```
