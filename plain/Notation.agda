
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Notation where

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite using ()
open import Agda.Builtin.Nat public using (Nat) renaming (_==_ to _==ᴺ_) 

variable A B C : Set

module Domains where

  postulate
    Domain : Set              -- Domain is the type of all domains
    ⟪_⟫ : Domain → Set        -- ⟪ D ⟫ is the type of elements of D
    ⊥ : {D : Domain} → ⟪ D ⟫  -- ⊥{D} is the bottom element of D
    𝟙 : Domain                -- 𝟙 is a unit domain

  variable D E F : Domain

open Domains public

module Functions where

  postulate
    _→ᶜ_ : Domain → Domain → Domain
    -- D →ᶜ E is the domain of continuous functions from D to E
  infixr 0 _→ᶜ_

  postulate
    dom-cts : ⟪ D →ᶜ E ⟫ ≡ (⟪ D ⟫ → ⟪ E ⟫)
  {-# REWRITE dom-cts #-}

  postulate
    _→ˢ_ : Set → Domain → Domain
  -- A →ˢ D is the domain of all functions from A to D
  infixr 0 _→ˢ_

  postulate
    set-cts : ⟪ A →ˢ D ⟫ ≡ (A → ⟪ D ⟫)
  {-# REWRITE set-cts #-}

  postulate
    fix : ⟪ (D →ᶜ D) →ᶜ D ⟫
    -- fix φ is the least fixed point of the continuous function φ
    apply-fix : {φ : ⟪ D →ᶜ D ⟫} → fix φ ≡ φ (fix φ)
    -- apply-fix{φ} unfolds fix φ once
  {-# REWRITE apply-fix #-}

open Functions public

module Recursion where

  postulate
    _≅_ : Domain → Domain → Set
    -- an instance of D ≅ E declares that the structure of D is the same as E
    unfold :  {{D ≅ E}} → ⟪ D →ᶜ E ⟫
    fold :    {{D ≅ E}} → ⟪ E →ᶜ D ⟫
    elim-unfold-fold : {{_ : D ≅ E}} → {e : ⟪ E ⟫} → unfold (fold e) ≡ e
  {-# REWRITE elim-unfold-fold #-}

  module D-infinity where
    postulate
      D∞ : Domain
      instance _ : D∞ ≅ (D∞ →ᶜ D∞)

module Flat where

  postulate
    _+⊥  : Set → Domain                 -- A +⊥ constructs a flat domain
    ↑    : ⟪ A →ˢ (A +⊥) ⟫              -- (↑ a) injects a into A +⊥
    _♯   : ⟪ (A →ˢ D) →ᶜ (A +⊥) →ᶜ D ⟫  -- f ♯ extends f to map ⊥ to ⊥
  variable f : A → ⟪ D ⟫; a′ : A
  postulate
    elim-♯-↑  : (f ♯) (↑ a′)  ≡ f a′
    elim-♯-⊥  : (f ♯) ⊥      ≡ ⊥
  {-# REWRITE elim-♯-↑ elim-♯-⊥ #-} 

  module Booleans where

    open import Data.Bool.Base public using (Bool; false; true; if_then_else_)
    Bool⊥ = Bool +⊥
    _⟶_,_ : ⟪ Bool⊥ →ᶜ D →ᶜ D →ᶜ D ⟫    -- β ⟶ δ₁ , δ₂ is conditional choice
    _⟶_,_ = (λ b δ₁ δ₂ → if b then δ₁ else δ₂)♯  
    infixr 20 _⟶_,_

    record Eq (A : Set) : Set where field _==_ : A → A → Bool
    open Eq {{...}} public
    postulate
      _==⊥_ : {{Eq A}} → ⟪ (A +⊥) →ᶜ (A +⊥) →ᶜ Bool⊥ ⟫
      -- δ₁ ==⊥ δ₂ is ⊥ when either operand is ⊥
      instance eqBool : Eq Bool

  module Naturals where

    open import Agda.Builtin.Nat public
      using (Nat; suc; _+_; _-_) renaming (_==_ to _==ᴺ_)
    Nat⊥ = Nat +⊥
    open Booleans
    postulate 
      instance eqNat : Eq Nat
    variable n₁ n₂ : Nat
    postulate
      elim-==⊥ : (↑ n₁ ==⊥ ↑ n₂) ≡ ↑ (n₁ ==ᴺ n₂)
    {-# REWRITE elim-==⊥ #-} 

module Sums where

  postulate
    _+_    : Domain → Domain → Domain   -- D + E is separated sum
    inj₁   : ⟪ D →ᶜ (D + E) ⟫           -- inj₁ δ is injection from D
    inj₂   : ⟪ E →ᶜ (D + E) ⟫           -- inj₂ ε is injection from E
    [_,_]  : ⟪ (D →ᶜ F) →ᶜ (E →ᶜ F) →ᶜ ((D + E) →ᶜ F) ⟫
    -- [ φ , ψ ] applies φ to arguments in D, and ψ to arguments in E

  variable φ : ⟪ D →ᶜ F ⟫; ψ : ⟪ E →ᶜ F ⟫; δ : ⟪ D ⟫; ε : ⟪ E ⟫
  postulate
    elim-inj₁  :  [ φ , ψ ] (inj₁ δ)  ≡  φ δ
    elim-inj₂  :  [ φ , ψ ] (inj₂ ε)  ≡  ψ ε
    elim-[]-⊥  :  [ φ , ψ ] ⊥         ≡  ⊥
  {-# REWRITE elim-inj₁ elim-inj₂ #-} 

  open import Agda.Builtin.Nat using (Nat)
  open Flat
  open Flat.Booleans
  open Flat.Naturals
  variable n : Nat
  postulate
    _≳_↦_  : Domain → Nat → Domain → Set
    _in⊥_  : ⟪ D ⟫ → (E : Domain) → {{E ≳ n ↦ D}} → ⟪ E ⟫      -- δ in⊥ E is injection from D
    _|⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ D ⟫      -- ε |⊥ D is projection to D
    _∈⊥_   : ⟪ E ⟫ → (D : Domain) → {{E ≳ n ↦ D}} → ⟪ Bool⊥ ⟫  -- ε ∈⊥ D tests an injection

  open import Relation.Binary.PropositionalEquality.Core using (_≢_)
  variable D′ : Domain; n′ : Nat
  postulate
    elim-∈⊥    :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  (δ in⊥ E) ∈⊥ D′ ≡ ↑ (n ==ᴺ n′)
    elim-|⊥    :  {{_ : E ≳ n ↦ D}} → (δ : ⟪ D ⟫) → (δ in⊥ E) |⊥ D ≡ δ
    elim-∈⊥-⊥  :  {{_ : E ≳ n ↦ D}} → {{_ : E ≳ n′ ↦ D′}} → (δ : ⟪ D ⟫) →
                  {n ≢ n′} → (δ in⊥ E) |⊥ D′ ≡ ⊥
  {-# REWRITE elim-∈⊥ elim-|⊥ #-} 

module Products where

  postulate
    _×_  : Domain → Domain → Domain  -- D × E is cartesian product
    _,_  : ⟪ D →ᶜ E →ᶜ (D × E) ⟫     -- (δ , ε) is a pair of elements
    _↓₁  : ⟪ (D × E) →ᶜ D ⟫          -- (δ , ε)↓₁ is δ
    _↓₂  : ⟪ (D × E) →ᶜ E ⟫          -- (δ , ε)↓₂ is ε

  infixr 2 _×_
  infixr 4 _,_

  variable δ : ⟪ D ⟫; ε : ⟪ E ⟫
  postulate
    elim-↓₁  :  ( δ , ε ) ↓₁  ≡  δ
    elim-↓₂  :  ( δ , ε ) ↓₂  ≡  ε
  {-# REWRITE elim-↓₁ elim-↓₂ #-} 

  module Tuples where

    open import Agda.Builtin.Nat public using (Nat; suc)
    _^_ : Domain → Nat → Domain         -- D ^ n is the domain of n-tuples (n ≥ 0)
    D ^ 0            = 𝟙 
    D ^ 1            = D
    D ^ suc (suc n)  = D × (D ^ suc n)

  module Sequences where

    open Flat.Naturals
    open Tuples
    variable n : Nat
    postulate
      _⋆     : Domain → Domain          -- D ⋆ is the finite sequence domain
      ⟨⟩     : ⟪ D ⋆ ⟫                  -- ⟨⟩ is the empty sequence
      ⟨_⟩    : ⟪ (D ^ suc n) →ᶜ D ⋆ ⟫   -- ⟨ δ₁ , ... ⟩ is a non-empty sequence
      #      : ⟪ D ⋆ →ᶜ Nat⊥ ⟫          -- # δ⋆ is the length of sequence δ⋆
      _§_    : ⟪ D ⋆ →ᶜ D ⋆ →ᶜ D ⋆ ⟫    -- δ⋆₁ § δ⋆₂ is sequence concatenation
      _↓_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⟫      -- δ⋆ ↓ n is the nth element
      _†_    : ⟪ D ⋆ →ᶜ Nat →ˢ D ⋆ ⟫    -- δ⋆ † n is the nth tail

module Updates where

  open Flat
  open Flat.Booleans
  _[_/_] : {{Eq A}} → ⟪ (A →ˢ D) →ᶜ D →ᶜ A →ˢ (A →ˢ D) ⟫
  -- ρ [ δ / a ] maps a to δ, and other arguments a′ to ρ a′
  ρ [ δ / a ] = λ a′ → if a == a′ then δ else ρ a′

  open Flat
  _[_/_]⊥ : {{Eq A}} → ⟪ ((A +⊥) →ᶜ D) →ᶜ D →ᶜ (A +⊥) →ᶜ ((A +⊥) →ᶜ D) ⟫
  -- σ [ δ / α ]⊥ maps α to δ, and other arguments α′ to σ α′
  σ [ δ / α ]⊥ = λ α′ → (α ==⊥ α′) ⟶ δ , σ α′

  open import Data.Maybe.Base public using (Maybe; just; nothing)
  open import Relation.Binary.PropositionalEquality.Core public using (_≡_; refl)
  record MaybeEq (A : Set) : Set where field _==?_ : (a a′ : A) → Maybe (a ≡ a′)
  open MaybeEq {{...}} public
  variable X : Set; Y : X → Set
  _[_←_] :  {{MaybeEq X}} → (∀ x′ → Y x′) → (x : X) → Y x → (∀ x′ → Y x′)
  _[_←_] {X} {Y} m x y = λ x′ → h x′ (x ==? x′) where
    h : (x′ : X) → Maybe (x ≡ x′) → Y x′
    h x′ (just refl) = y
    h x′ nothing = m x′
