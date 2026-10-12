# Sequence Domains

The domain `D ⋆` of finite sequences of elements of a domain `D` is
conventionally written $D^*$.

The following notation for the various operations on sequences was introduced
in the early 1970s, and is used in the *Scheme* semantics [(Scheme)].
(The single angle-brackets `⟨...⟩` used to form sequences are unrelated to the
double angle-brackets `⟪ D ⟫` used for the carrier of domain `D`.)
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Notation.Products.Sequences where
--"hide"

  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Flat.Naturals
  open import Notation.Products.Tuples
--"/hide"
  variable n : Nat

  postulate
    _⋆     : Domain → Domain         -- D ⋆ is the finite sequence domain
    ⟨⟩     : ⟪ D ⋆ ⟫                 -- ⟨⟩ is the empty sequence
    ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫  -- ⟨ δ₁ , ... ⟩ is a non-empty sequence
    #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫         -- # δ⋆ is the length of sequence δ⋆
    _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫   -- δ⋆₁ § δ⋆₂ is sequence concatenation
    _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫     -- δ⋆ ↓ n is the nth element
    _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫   -- δ⋆ † n is the nth tail
```

[(Scheme)]: https://scheme.org
