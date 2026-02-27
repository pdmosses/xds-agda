
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Notation where

variable A B C : Set

module Domains where
  postulate
    Domain : Set
    ⟪_⟫ : Domain → Set
    ⊥ : {D : Domain} → ⟪ D ⟫
    𝟙 : Domain
  variable D E F : Domain

open Domains public

module Functions where
  open import Agda.Builtin.Equality using (_≡_) public
  open import Agda.Builtin.Equality.Rewrite using ()
  postulate
    _→ᶜ_ : Domain → Domain → Domain
  infixr 0 _→ᶜ_

  postulate
    fix : ⟪ (D →ᶜ D) →ᶜ D ⟫

  postulate
    dom-cts : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  {-# REWRITE dom-cts #-}

  postulate
    _→ˢ_ : Set → Domain → Domain
  infixr 0 _→ˢ_

  postulate
    set-cts : ⟪ A →ˢ D ⟫ ≡ (A → ⟪ D ⟫)
  {-# REWRITE set-cts #-}

open Functions public

module Recursion where
  postulate
    _≅_ : Domain → Domain → Set
    unfold :  {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold :    {{D ≅ E}} → ⟪ E →ᶜ D ⟫

  module D-infinity where
    postulate
      D∞ : Domain
      instance _ : D∞ ≅ (D∞ →ᶜ D∞)

module Flat where
  postulate
    _+⊥  : Set → Domain
    ↑    : ⟪ A →ˢ (A +⊥) ⟫
    _♯   : ⟪ (A →ˢ D) →ᶜ (A +⊥) →ᶜ D ⟫

  module Booleans where
    open import Data.Bool.Base using (Bool; false; true; if_then_else_) public
    record Eq (A : Set) : Set where field _==_ : A → A → Bool
    open Eq {{...}} public
    Bool⊥ = Bool +⊥
    postulate
      _⟶_,_ : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫
    infixr 20 _⟶_,_

    postulate
      Eq⊥ : Domain → Set
      _==⊥_ : {{Eq A}} → ⟪ (A +⊥) →ᶜ (A +⊥) →ᶜ Bool⊥ ⟫
      instance eqBool : Eq Bool

  module Naturals where
    open import Data.Nat.Base renaming (ℕ to Nat) using (suc; _+_; _∸_; _≡ᵇ_) public
    Nat⊥ = Nat +⊥
    open Booleans
    postulate
      instance eqNat : Eq Nat

  module Strings where
    open import Data.String.Base using (String) public
    String⊥ = String +⊥
    open Booleans
    postulate
      instance _ : Eq String

module Sums where
  postulate
    _+_    : Domain → Domain → Domain
    inj₁   : ⟪ D →ᶜ (D + E) ⟫
    inj₂   : ⟪ E →ᶜ (D + E) ⟫
    [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ ((D + E) →ᶜ F) ⟫

  open import Data.Nat.Base renaming (ℕ to Nat)
  open Flat.Booleans
  variable n : Nat
  postulate
    _≳_↦_  : Domain → Nat → Domain → Set
    _in⊥_  : ⟪ D ⟫ → (E : Domain) → {{E ≳ n ↦ D}} → ⟪ E ⟫
    _|⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ D ⟫
    _∈⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ Bool⊥ ⟫

module Products where
  postulate
    _×_  : Domain → Domain → Domain
    _,_  : ⟪ D →ᶜ E →ᶜ (D × E) ⟫
    _↓₁  : ⟪ (D × E) →ᶜ D ⟫
    _↓₂  : ⟪ (D × E) →ᶜ E ⟫
  infixr 2 _×_
  infixr 4 _,_

  module Tuples where
    open import Data.Nat.Base renaming (ℕ to Nat) using (suc) public
    _^_ : Domain → Nat → Domain
    D ^ 0            = 𝟙 
    D ^ 1            = D
    D ^ suc (suc n)  = D × (D ^ suc n)

  module Sequences where
    open Flat.Naturals
    open Tuples
    variable n : Nat
    postulate
      _⋆     : Domain → Domain
      ⟨⟩     : ⟪ D ⋆ ⟫
      ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫
      #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫
      _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫
      _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫
      _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫

module Updates where
  open Flat
  open Flat.Booleans
  _[_/_] : {{Eq A}} → ⟪ (A →ˢ D) →ᶜ D →ᶜ A →ˢ (A →ˢ D) ⟫
  ρ [ δ / a ] = λ a′ → if a == a′ then δ else ρ a′

  open Flat
  _[_/_]⊥ : {{Eq A}} → ⟪ ((A +⊥) →ᶜ D) →ᶜ D →ᶜ (A +⊥) →ᶜ ((A +⊥) →ᶜ D) ⟫
  σ [ δ / α ]⊥ = λ α′ → (α ==⊥ α′) ⟶ δ , σ α′

  open import Data.Maybe.Base using (Maybe; just; nothing) public
  open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl) public
  record EqMaybe (A : Set) : Set where field _==?_ : (a a′ : A) → Maybe (a ≡ a′)
  open EqMaybe {{...}} public
  _[_←_] :  {X : Set} → {Y : X → Set} → {{EqMaybe X}} → 
            (∀ (x′) → Y x′) → (x : X) → Y x → (∀ (x′) → Y x′)
  _[_←_] {X} {Y} m x y = λ x′ → h x′ (x ==? x′) where
    h : (x′ : X) → Maybe (x ≡ x′) → Y x′
    h x′ (just refl) = y
    h x′ nothing = m x′
