# Updates

When a type `A` has an equality operation `_==_ : A → A → Bool`,
environments `ρ : ⟪ A →ˢ D ⟫` can be 'updated' (i.e., extended or overridden) using the
conventional notation `ρ [ δ / a ]`, defined as follows.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

--"/hide"
module Notation.Updates where
--"hide"

  open import Notation.Domains
  open import Notation.Functions
  open import Notation.Flat
  open import Notation.Flat.Booleans

--"/hide"
  _[_/_] : {{Eq A}} → ⟪ (A →ˢ D) →ᶜ D →ᶜ A →ˢ (A →ˢ D) ⟫
--"hide"
  -- ρ [ δ / a ] maps a to δ, and other arguments a′ to ρ a′
--"/hide"
  ρ [ δ / a ] = λ a′ → if a == a′ then δ else ρ a′
```
Similarly for stores `σ : ⟪ (A +⊥) →ᶜ D ⟫` (appending $\bot$ to the conventional notation):
```agda
  _[_/_]⊥ : {{Eq A}} → ⟪ ((A +⊥) →ᶜ D) →ᶜ D →ᶜ (A +⊥) →ᶜ ((A +⊥) →ᶜ D) ⟫
--"hide"
  -- σ [ δ / α ]⊥ maps α to δ, and other arguments α′ to σ α′
--"/hide"
  σ [ δ / α ]⊥ = λ α′ → (α ==⊥ α′) ⟶ δ , σ α′
```
Defining an operation `m [ x ← y ]`
for updating a *dependent* map `m` to map `x` to `y`
is somewhat less straightforward,
as it involves an equality test that may return an *equivalence proof*.
```agda
  open import Data.Maybe.Base public using (Maybe; just; nothing)
  open import Relation.Binary.PropositionalEquality.Core public using (_≡_; refl)

  record MaybeEq (A : Set) : Set where field _==?_ : (a a′ : A) → Maybe (a ≡ a′)
  open MaybeEq {{...}} public

  variable X : Set; Y : X → Set

  _[_←_] :  {{MaybeEq X}} → (∀ x′ → Y x′) → (x : X) → Y x → (∀ x′ → Y x′)
  _[_←_] {X} {Y} m x y = λ x′ → h x′ (x ==? x′) 
    where
      h : (x′ : X) → Maybe (x ≡ x′) → Y x′
      h x′ (just refl) = y
      h x′ nothing = m x′
```

Note that the order of the arguments differs from that in the notation
for non-dependent updates, as the type of `y` may depend on the value of `x`.
