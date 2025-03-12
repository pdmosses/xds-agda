\begin{code}
module Scheme.Domain-Notation where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl) public

------------------------------------------------------------------------
-- Agda requires Predomain and Domain to be sorts

Predomain  = Set
Domain     = Set
variable
  P    : Predomain
  D E  : Domain

-- Domains are pointed
postulate
  ⊥         : {D : Domain} → D
  strict    : {D E : Domain} → (D → E) → (D → E)

  -- Properties
  strict-⊥  : ∀ {D E} → (f : D → E) →
                strict f ⊥ ≡ ⊥

------------------------------------------------------------------------
-- Fixed points of endofunctions on function domains

postulate
  fix       : {D : Domain} → (D → D) → D

  -- Properties
  fix-fix   : ∀ {D} (f : D → D) →
               fix f ≡ f (fix f)
  fix-app   : ∀ {P D} (f : (P → D) → (P → D)) (p : P) →
               fix f p ≡ f (fix f) p

------------------------------------------------------------------------
-- Lifted domains

postulate
  𝕃         : Predomain → Domain
  η         : {P : Predomain} → P → 𝕃 P
  _♯        : {P : Predomain} {D : Domain} → (P → D) → (𝕃 P → D)

  -- Properties
  elim-♯-η  : ∀ {P D} (f : P → D) (p : P)  →
                (f ♯) (η p) ≡ f p
  elim-♯-⊥  : ∀ {P D} (f : P → D) →
                (f ♯) ⊥ ≡ ⊥
\end{code}
\clearpage
\begin{code}
------------------------------------------------------------------------
-- Flat domains

_+⊥   : Set → Domain
S +⊥  = 𝕃 S

-- Lifted operations on ℕ

open import Agda.Builtin.Nat
  using (_==_; _<_) public
open import Data.Nat.Base as Nat
  using (ℕ; suc; pred) public
open import Data.Bool.Base
  using (Bool) public

-- ν ==⊥ n : Bool +⊥

_==⊥_ : ℕ +⊥ → ℕ → Bool +⊥
ν ==⊥ n = ((λ m → η (m == n)) ♯) ν

-- ν >=⊥ n : Bool +⊥

_>=⊥_ : ℕ +⊥ → ℕ → Bool +⊥
ν >=⊥ n = ((λ m → η (n < m)) ♯) ν

------------------------------------------------------------------------
-- Products

-- Products of (pre)domains are Cartesian

open import Data.Product.Base
  using (_×_; _,_) renaming (proj₁ to _↓1; proj₂ to _↓2) public

-- (p₁ , ... , pₙ) : P₁ × ... × Pₙ  (n ≥ 2)
-- _↓1 : P₁ × P₂ → P₁
-- _↓2 : P₁ × P₂ → P₂

------------------------------------------------------------------------
-- Sum domains

-- Disjoint unions of (pre)domains are unpointed predomains
-- Lifted disjoint unions of domains are separated sum domains

open import Data.Sum.Base
  using (inj₁; inj₂) renaming (_⊎_ to _+_; [_,_]′ to [_,_]) public

-- inj₁ : P₁ → P₁ + P₂
-- inj₂ : P₂ → P₁ + P₂
-- [ f₁ , f₂ ] : (P₁ → P) → (P₂ → P) → (P₁ + P₂) → P
\end{code}
\clearpage
\begin{code}
------------------------------------------------------------------------
-- Finite sequences

open import Data.Vec.Recursive
  using (_^_; []; append) public
open import Agda.Builtin.Sigma
  using (Σ)

-- Sequence predomains
-- P ^ n  = P × ... × P  (n ≥ 0)
-- P *    = (P ^ 0) + ... + (P ^ n) + ...
-- (n, p₁ , ... , pₙ) : P *

_*   : Set → Set
P *  = Σ ℕ (P ^_)

-- #′ S * : ℕ

#′ : {S : Set} → S * → ℕ
#′ (n , _) = n

_::′_ : ∀ {P : Set} → P → P * → P *
p ::′ (0      , ps) = (1 , p)
p ::′ (suc n  , ps) = (suc (suc n) , p , ps)

_↓′_ : ∀ {P : Set} → P * → ℕ → 𝕃 P
(1            , p)       ↓′ 1            = η p
(suc (suc n)  , p , ps)  ↓′ 1            = η p
(suc (suc n)  , p , ps)  ↓′ suc (suc i)  = (suc n , ps) ↓′ suc i
(_            , _)       ↓′ _            = ⊥

_†′_ : ∀ {P : Set} → P * → ℕ → 𝕃 (P *)
(1            , p)       †′ 1            = η (0 , [])
(suc (suc n)  , p , ps)  †′ 1            = η (suc n , ps)
(suc (suc n)  , p , ps)  †′ suc (suc i)  = (suc n , ps) †′ suc i
(_            , _)       †′ _            = ⊥

_§′_ : ∀ {P : Set} → P * → P * → P *
(m , pm) §′ (n , pn) = ((m Nat.+ n) , append m n pm pn)

-- Sequence domains
-- D ⋆ = 𝕃 ((D ^ 0) + ... + (D ^ n) + ...)

_⋆   : Domain → Domain
D ⋆  = 𝕃 (Σ ℕ (D ^_))

-- ⟨⟩ : D ⋆

⟨⟩ : ∀ {D} → D ⋆
⟨⟩ = η (0 , [])

-- ⟨ d₁ , ... , dₙ ⟩ : D ⋆

⟨_⟩ : ∀ {n D} → D ^ suc n → D ⋆
⟨_⟩ {n = n} ds = η (suc n , ds)
\end{code}
\clearpage
\begin{code}
-- # D ⋆ : ℕ +⊥

# : ∀ {D} → D ⋆ → ℕ +⊥
# d⋆ = ((λ p* → η (#′ p*)) ♯) d⋆

-- d⋆₁ § d⋆₂ : D ⋆

_§_ : ∀ {D} → D ⋆ → D ⋆ → D ⋆
d⋆₁ § d⋆₂ = ((λ p*₁ → ((λ p*₂ → η (p*₁ §′ p*₂)) ♯) d⋆₂) ♯) d⋆₁

open import Function
  using (id; _∘_) public

-- d⋆ ↓ k : 𝕃 D  (k ≥ 1; k < # d⋆)

_↓_ : ∀ {D} → D ⋆ → ℕ → D
d⋆ ↓ n = (id ♯) (((λ p* → p* ↓′ n) ♯) d⋆)

-- d⋆ † k : D ⋆  (k ≥ 1)

_†_ : ∀ {D} → D ⋆ → ℕ → D ⋆
d⋆ † n = (id ♯) (((λ p* → η (p* †′ n)) ♯) d⋆)

------------------------------------------------------------------------
-- McCarthy conditional

-- t ⟶ d₁ , d₂ : D  (t : Bool +⊥ ; d₁, d₂ : D)

open import Data.Bool.Base
  using (Bool; true; false; if_then_else_) public

postulate
  _⟶_,_ : {D : Domain} → Bool +⊥ → D → D → D

  -- Properties
  true-cond    : ∀ {D} {d₁ d₂ : D} → (η true ⟶ d₁ , d₂)  ≡ d₁
  false-cond   : ∀ {D} {d₁ d₂ : D} → (η false ⟶ d₁ , d₂) ≡ d₂
  bottom-cond  : ∀ {D} {d₁ d₂ : D} → (⊥ ⟶ d₁ , d₂)       ≡ ⊥

------------------------------------------------------------------------
-- Meta-Strings

open import Data.String.Base
  using (String) public

\end{code}  