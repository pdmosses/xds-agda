# Auxiliary Functions

The $\lambda$-notation in the Agda definitions of auxiliary functions for *Scm*
corresponds closely to that in its published denotational semantics [(Mosses2025CSE)].
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Examples.Scm.Auxiliary-Functions where
--"hide"

  open import Examples.Scm.Abstract-Syntax
  open import Examples.Scm.Domain-Equations
  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Flat
  open import Notation.Flat.Booleans
  open import Notation.Flat.Naturals
  open import Notation.Sums
  open import Notation.Products
  open import Notation.Products.Sequences
  open import Notation.Updates
  open import Agda.Builtin.Nat using (Nat)
  open import Data.String.Properties renaming (_==_ to _==ˢ_) using ()

  postulate
    _<ᴿ_  : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐓 ⟫
    _+ᴿ_  : ⟪ 𝐑 →ᶜ 𝐑 →ᶜ 𝐑 ⟫
    _∧ᵀ_  : ⟪ 𝐓 →ᶜ 𝐓 →ᶜ 𝐓 ⟫

  instance
    eqIde : Eq Ide
    _==_ {{eqIde}} = _==ˢ_

  postulate unknown : Loc

  postulate initial-env : ⟪ 𝐔 ⟫
--"/hide"

  assign : ⟪ 𝐋 →ᶜ 𝐄 →ᶜ 𝐂 →ᶜ 𝐂 ⟫      -- assign α ϵ stores ϵ at location α
  assign α ϵ θ σ = θ (σ [ ϵ / α ]⊥)

  hold : ⟪ 𝐋 →ᶜ (𝐄 →ᶜ 𝐂) →ᶜ 𝐂 ⟫      -- hold α gives the value stored at α
  hold α κ σ = κ (σ α) σ
```
In the continuation-passing style used to define auxilary functions for *Scm*,
giving explicit continuity proofs would be particulary tedious.
For example, the function `hold` is simply a combination of
$\lambda$-abstraction and application, which is well-known to ensure continuity.
```agda
  postulate new : ⟪ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫  -- new gives an unallocated location

  alloc : ⟪ 𝐄 →ᶜ (𝐋 →ᶜ 𝐂) →ᶜ 𝐂 ⟫     -- alloc ϵ allocates a location for ϵ
  alloc ϵ κ = new (λ α → assign α ϵ (κ α))

  postulate initial-store : ⟪ 𝐒 ⟫    -- may have initialised locations

--"hide"
  postulate finished : ⟪ 𝐒 →ᶜ 𝐀 ⟫    -- obtain answer from the final store
--"/hide"
```
Conventional denotational definitions usually leave the injection function `↑` from
sets into [flat domains] implicit, in contrast to the following embedding of the definition of `truish`:

```agda
  truish : ⟪ 𝐄 →ᶜ 𝐓 ⟫                -- truish ε is true for all ε except false
  truish ϵ =  (ϵ ∈⊥ 𝐓) ⟶ (((ϵ |⊥ 𝐓) ==⊥ ↑ false) ⟶ ↑ false , ↑ true) ,
              ↑ true
```
The remaining auxiliary function definitions shown here involve the operations for (finite) sequences `ϵ⋆`
declared in the module for [sequence domains].
```agda
  cons : ⟪ 𝐅 ⟫                       -- cons ⟨ ϵ₁ , ϵ₂ ⟩ allocates and initialises a pair
  cons ϵ⋆ κ =  (# ϵ⋆ ==⊥ ↑ 2) ⟶
                  alloc (ϵ⋆ ↓ 1) (λ α₁ →
                    alloc (ϵ⋆ ↓ 2) (λ α₂ → κ ((α₁ , α₂) in⊥ 𝐄))) ,
                ⊥
```
In [(Mosses2025CSE)] the auxiliary function $\textit{list}$ is defined by recursion on `ϵ⋆`.
Agda accepts recursive definitions only when it can mechanically prove that the recursion terminates,
which is not the case for arguments in postulated types.
The following definition uses the postulated operation `fix` to avoid recursion.
```agda
  list : ⟪ 𝐅 ⟫                       -- list ϵ⋆ allocates and initialises a list
  list =   fix λ (list′ : ⟪ 𝐅 ⟫) → λ ϵ⋆ κ →
            (# ϵ⋆ ==⊥ ↑ 0) ⟶ κ (↑ null in⊥ 𝐄) ,
            list′ (ϵ⋆ † 1) (λ ϵ → cons ⟨ (ϵ⋆ ↓ 1) , ϵ ⟩ κ)
--"hide"

  car : ⟪ 𝐅 ⟫                        -- car ⟨ ϵ ⟩ gives the head of the list ϵ
  car ϵ⋆ κ = (# ϵ⋆ ==⊥ ↑ 1) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₁) κ , ⊥

  cdr : ⟪ 𝐅 ⟫                        -- cdr ⟨ ϵ ⟩ gives the tail of the list ϵ
  cdr ϵ⋆ κ = (# ϵ⋆ ==⊥ ↑ 1) ⟶ hold (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₂) κ , ⊥

  setcar : ⟪ 𝐅 ⟫                     -- setcar ⟨ ϵ₁ , ϵ₂ ⟩ stores ϵ₂ in the head of list ϵ₁
  setcar ϵ⋆ κ =
    (# ϵ⋆ ==⊥ ↑ 2) ⟶
      assign (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₁) (ϵ⋆ ↓ 2) (κ (↑ unspecified in⊥ 𝐄)) ,
    ⊥

  setcdr : ⟪ 𝐅 ⟫                     -- setcdr ⟨ ϵ₁ , ϵ₂ ⟩ stores ϵ₂ in the tail of list ϵ₁
  setcdr ϵ⋆ κ =
    (# ϵ⋆ ==⊥ ↑ 2) ⟶
      assign (((ϵ⋆ ↓ 1) |⊥ 𝐏) ↓₂) (ϵ⋆ ↓ 2) (κ (↑ unspecified in⊥ 𝐄)) ,
    ⊥
--"/hide"
```

[(MFPS2026-Agda)]: https://pdmosses.github.io/mfps2026-agda/
[(Mosses2025CSE)]: https://doi.org/10.1145/3759427.3760369
[Sequence Domains]: ../../Notation/Products/Sequences.md#sequence-domains
[flat domains]: ../../Notation/Flat/index.md#flat-domains
