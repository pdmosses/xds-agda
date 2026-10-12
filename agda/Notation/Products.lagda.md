# Product Domains

The carrier of the binary product `D × E` of two domains consists of all
pairs `(d , e)` of elements of `D` and `E`
with the pair `(⊥{D} , ⊥{E})` as the bottom element `⊥{D × E}`.
The following operations can be used directly for binary products,
and iterated for products of more than two domains.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Notation.Products where
--"hide"

  open import Notation.Domains
  open import Notation.Functions
  
--"/hide"
  postulate
    _×_  : Domain → Domain → Domain  -- D × E is the categorical product
    _,_  : ⟪ D →ᶜ E →ᶜ (D × E) ⟫     -- (δ , ε) is a pair of elements
    _↓₁  : ⟪ (D × E) →ᶜ D ⟫          -- (δ , ε)↓₁ is δ
    _↓₂  : ⟪ (D × E) →ᶜ E ⟫          -- (δ , ε)↓₂ is ε
--"hide"
  infixr 2 _×_
  infixr 4 _,_
--"/hide"
```
Neither the product nor pairing is associative in the embedding –
they are associative up to isomorphism, but the Agda type-checker does not take account of that.
