# Scheme R5 Denotational Semantics

[R5RS]: https://standards.scheme.org/official/r5rs.pdf

Conversion from plain text copy of PDF preview to Agda:

-[x] Replace `→` by `⟶⊥` in conditionals
-[x] Replace ` . ` by ` → ` in λ s
-[x] Replace `.` by `·` in abstract syntax
-[x] Replace `(...)` by `⦅...⦆` and separate args by `␣` in abstract syntax
-[x] Replace `“...”` by `"..."`
-[x] Insert spaces between name parts
-[x] Use different fonts for domain names and meta-variables
-[x] Use Agda notation for inline comments

When copying text to Literate Agda modules:

-[ ] Import required modules
-[ ] Replace abstract syntax grammar by data type definitions
-[ ] Replace domain equations by postulated declarations and isomorphisms
-[ ] Eliminate non-compositional semantic equations
-[ ] Check alignment in formatted PDF


## 7.2. Formal semantics

This section provides a formal denotational semantics for
the primitive expressions of Scheme and selected built-in
procedures. The concepts and notation used here are de-
scribed in [29]; the notation is summarized below:

[29] Joseph E. Stoy. Denotational Semantics: The Scott-Strachey Approach
     to Programming Language Theory. MIT Press, Cambridge, 1977.

⟨...⟩   sequence formation
s↓k     kth member of the sequence s (1-based)
#s      length of sequence s
s§t     concatenation of sequences s and t
s†k     drop the first k members of sequence s
t⟶⊥a,b   McCarthy conditional "if t then a else b"
ρ[x/i]  substitution "ρ with x for i"
x in D  injection of x into domain D
x|D     projection of x to domain D

The reason that expression continuations take sequences
of values instead of single values is to simplify the formal
treatment of procedure calls and multiple return values.

The boolean flag associated with pairs, vectors, and strings
will be true for mutable objects and false for immutable
objects.

The order of evaluation within a call is unspecified. We
mimic that here by applying arbitrary permutations per-
mute and unpermute, which must be inverses, to the argu-
ments in a call before and after they are evaluated. This is
not quite right since it suggests, incorrectly, that the order
of evaluation is constant throughout a program (for any
given number of arguments), but it is a closer approxima-
tion to the intended semantics than a left-to-right evalua-
tion would be.

The storage allocator new is implementation-dependent,
but it must obey the following axiom: if new σ ∈ 𝐋, then
σ(new σ | 𝐋) ↓ 2 = false.

The definition of K is omitted because an accurate defini-
tion of K would complicate the semantics without being
very interesting.

If P is a program in which all variables are defined before
being referenced or assigned, then the meaning of P is

  ℰ⟦ ⦅ ⦅lambda␣⦅ I⋆ ⦆ P′ ⦆ ␣ ⟨undefined⟩ ␣ ... ⦆ ⟧

where I⋆ is the sequence of variables defined in P, P′ is the
sequence of expressions obtained by replacing every defini-
tion in P by an assignment, ⟨undefined⟩ is an expression
that evaluates to undefined, and E is the semantic function
that assigns meaning to expressions.

### 7.2.1. Abstract syntax

K ∈ Con       constants, including quotations
I ∈ Ide       identifiers (variables)
E ∈ Exp       expressions
Γ ∈ Com = Exp commands

Exp ⟶  K | I | ⦅ E₀ ␣ E⋆ ⦆ 
    |  ⦅lambda␣⦅ I⋆ ⦆ Γ⋆ ␣ E₀ ⦆
    |  ⦅lambda␣⦅ I⋆ · I ⦆ Γ⋆ ␣ E₀ ⦆
    |  ⦅lambda I ␣ Γ⋆ ␣ E₀ ⦆
    |  ⦅if E₀ ␣ E₁ ␣ E₂ ⦆ | ⦅ if E₀ ␣ E₁ ⦆
    |  ⦅set! I ␣ E ⦆

### 7.2.2. Domain equations

α ∈ 𝐋                     locations
ν ∈ 𝐍                     natural numbers
    𝐓 = {false, true}     booleans
    𝐐                     symbols
    𝐇                     characters
    𝐑                     numbers
    𝐄𝐩 = 𝐋 × 𝐋 × 𝐓        pairs
    𝐄𝐯 = 𝐋⋆ × 𝐓           vectors
    𝐄𝐬 = 𝐋⋆ × 𝐓           strings
    𝐌 = {false, true, null, undefined, unspecified}
                          miscellaneous
φ ∈ 𝐅 = 𝐋 × (𝐄⋆ → 𝐊 → 𝐂)  procedure values
ϵ ∈ 𝐄 = 𝐐 + 𝐇 + 𝐑 + 𝐄𝐩 + 𝐄𝐯 + 𝐄𝐬 + 𝐌 + 𝐅
                          expressed values
σ ∈ 𝐒 = 𝐋 → (𝐄 × 𝐓)       stores
ρ ∈ 𝐔 = Ide → 𝐋           environments
θ ∈ 𝐂 = 𝐒 → 𝐀             command continuations
κ ∈ 𝐊 = 𝐄⋆ → 𝐂            expression continuations
    𝐀                     answers
    𝐗                     errors

7.2.3. Semantic functions

𝒦  : Con → 𝐄
ℰ  : Exp → 𝐔 → 𝐊 → 𝐂
ℰ⋆ : Exp⋆ → 𝐔 → 𝐊 → 𝐂
𝒞  : Com⋆ → 𝐔 → 𝐂 → 𝐂

-- Definition of 𝒦 deliberately omitted.

ℰ⟦ K ⟧ = λ ρ κ → send (𝒦⟦ K ⟧) κ

ℰ⟦ I ⟧ = λ ρ κ → hold (lookup ρ I)
                      (single (λ ϵ → ϵ = undefined ⟶⊥
                                         wrong "undefined variable" ,
                                       send ϵ κ))

ℰ⟦ ⦅ E₀ ␣ E⋆ ⦆ ⟧ =
  λ ρ κ → ℰ⋆⟦ permute (⟨ E₀ ⟩ § E⋆ ) ⟧
          ρ
          (λ ϵ⋆ → ((λ ϵ⋆ → applicate (ϵ⋆ ↓ 1) (ϵ⋆ † 1) κ)
                   (unpermute ϵ⋆)))

ℰ⟦ ⦅lambda␣⦅ I⋆ ⦆ Γ⋆ ␣ E₀ ⦆ ⟧ =
  λ ρ κ → λ σ → 
    new σ ∈ 𝐋 ⟶⊥
        send (⟨ new σ | 𝐋 ,
                λ ϵ⋆ κ′ → # ϵ⋆ = # I⋆ ⟶⊥
                              tievals (λ α⋆ → (λ ρ′ → 𝒞⟦ Γ⋆ ⟧ ρ′ (ℰ⟦ E₀ ⟧ ρ′ κ′))
                                              (extends ρ I⋆ α⋆))
                                      ϵ⋆ ,
                            wrong "wrong number of arguments" ⟩
                in 𝐄)
             κ
             (update (new σ | 𝐋) unspecified σ) ,
      wrong "out of memory" σ

ℰ⟦ ⦅lambda␣⦅ I⋆ · I ⦆ Γ⋆ ␣ E₀ ⦆ ⟧ =
  λ ρ κ → λ σ → 
    new σ ∈ 𝐋 ⟶⊥
        send (⟨ new σ | 𝐋 ,
                λ ϵ⋆ κ′ → # ϵ⋆ ≥ # I⋆ ⟶⊥
                              tievalsrest
                                (λ α⋆ → (λ ρ′ → 𝒞⟦ Γ⋆ ⟧ ρ′ (ℰ⟦ E₀ ⟧ ρ′ κ′))
                                        (extends ρ (I⋆ § ⟨ I ⟩) α⋆))
                                ϵ⋆
                                (# I⋆) ,
                            wrong "too few arguments" ⟩ in 𝐄)
             κ
             (update (new σ | 𝐋) unspecified σ) ,
      wrong "out of memory" σ

ℰ⟦ ⦅lambda I ␣ Γ⋆ ␣ E₀ ⦆ ⟧ = ℰ⟦ ⦅lambda ⦅ · I ⦆ Γ⋆ ␣ E₀ ⦆ ⟧

ℰ⟦ ⦅if E₀ ␣ E₁ ␣ E₂ ⦆ ⟧ =
  λ ρ κ → ℰ⟦ E₀ ⟧ ρ (single (λ ϵ → truish ϵ ⟶⊥ ℰ⟦ E₁ ⟧ ρ κ ,
                                     ℰ⟦ E₂ ⟧ ρ κ))

ℰ⟦ ⦅if E₀ ␣ E₁ ⦆ ⟧ =
  λ ρ κ → ℰ⟦ E₀ ⟧ ρ (single (λ ϵ → truish ϵ ⟶⊥ ℰ⟦ E₁ ⟧ ρ κ ,
                                     send unspecified κ))

-- Here and elsewhere, any expressed value other than `undefined`
-- may be used in place of `unspecified`.

ℰ⟦ ⦅set! I ␣ E ⦆ ⟧ =
  λ ρ κ → ℰ⟦ E ⟧ ρ (single (λ ϵ → assign (lookup ρ I)
                                         ϵ
                                         (send unspecified κ)))

ℰ⋆⟦  ⟧ = λ ρ κ → κ ⟨⟩

ℰ⋆⟦ E₀ ␣ E⋆ ⟧ = λ ρ κ → ℰ⟦ E₀ ⟧ ρ (single (λ ϵ₀ → ℰ⋆⟦ E⋆ ⟧ ρ (λ ϵ⋆ → κ(⟨ ϵ₀ ⟩ § ϵ⋆))))

𝒞⟦  ⟧ = λ ρ θ → θ

𝒞⟦ Γ₀ ␣ Γ⋆ ⟧ = λ ρ θ → ℰ⟦ Γ₀ ⟧ ρ (λ ϵ⋆ → 𝒞⟦ Γ⋆ ⟧ ρ θ)

### 7.2.4.  Auxiliary functions

lookup : 𝐔 → Ide → 𝐋
lookup = λ ρ I → ρ I

extends : 𝐔 → Ide⋆ → 𝐋⋆ → 𝐔
extends =
  λ ρ I⋆ α⋆ → # I⋆ = 0 ⟶⊥ ρ ,
                extends (ρ [ (α⋆ ↓ 1) / (I⋆ ↓ 1) ]) (I⋆ † 1) (α⋆ † 1)

wrong : 𝐗 → 𝐂  -- implementation-dependent

send : 𝐄 → 𝐊 → 𝐂
send = λ ϵ κ → κ ⟨ ϵ ⟩

single : (𝐄 → 𝐂) → 𝐊
single =
λ ψ ϵ⋆ →  # ϵ⋆ = 1 ⟶⊥ ψ (ϵ⋆ ↓ 1) ,
            wrong "wrong number of return values"

new : 𝐒 → (𝐋 + {error})  -- implementation-dependent

hold : 𝐋 → 𝐊 → 𝐂
hold = λ α κ σ → send (σ α ↓ 1) κ σ

assign : 𝐋 → 𝐄 → 𝐂 → 𝐂
assign = λ α ϵ θ σ → θ (update α ϵ σ)

update : 𝐋 → 𝐄 → 𝐒 → 𝐒
update = λ α ϵ σ → σ [ ⟨ ϵ , true ⟩ / α ]

tievals : (𝐋⋆ → 𝐂) → 𝐄⋆ → 𝐂
tievals =
  λ ψ ϵ⋆ σ → # ϵ⋆ = 0 ⟶⊥ ψ ⟨⟩ σ ,
                new σ ∈ 𝐋 ⟶⊥ tievals (λ α⋆ → ψ (⟨ new σ | 𝐋 ⟩ § α⋆))
                                    (ϵ⋆ † 1)
                                    (update (new σ | 𝐋) (ϵ⋆ ↓ 1) σ) ,
              wrong "out of memory" σ

tievalsrest : (𝐋⋆ → 𝐂) → 𝐄⋆ → 𝐍 → 𝐂
tievalsrest =
  λ ψ ϵ⋆ ν → list (dropfirst ϵ⋆ ν)
                  (single (λ ϵ → tievals ψ ((takefirst ϵ⋆ ν) § ⟨ ϵ ⟩)))

dropfirst = λ l n → n = 0 ⟶⊥ l , dropfirst (l † 1) (n − 1)

takefirst = λ l n → n = 0 ⟶⊥ ⟨⟩ , ⟨l ↓ 1⟩ § (takefirst (l † 1) (n − 1))

truish : 𝐄 → 𝐓
truish = λ ϵ → ϵ = false ⟶⊥ false , true

permute : Exp⋆ → Exp⋆  -- implementation-dependent

unpermute : 𝐄⋆ → 𝐄⋆  -- inverse of permute

applicate : 𝐄 → 𝐄⋆ → 𝐊 → 𝐂
applicate =
  λ ϵ ϵ⋆ κ → ϵ ∈ 𝐅 ⟶⊥ (ϵ | 𝐅 ↓ 2) ϵ⋆ κ , wrong "bad procedure"

onearg : (𝐄 → 𝐊 → 𝐂) → (𝐄⋆ → 𝐊 → 𝐂)
onearg =
  λ ζ ϵ⋆ κ → # ϵ⋆ = 1 ⟶⊥ ζ (ϵ⋆ ↓ 1) κ ,
               wrong "wrong number of arguments"

twoarg : (𝐄 → 𝐄 → 𝐊 → 𝐂) → (𝐄⋆ → 𝐊 → 𝐂)
twoarg =
  λ ζ ϵ⋆ κ → # ϵ⋆ = 2 ⟶⊥ ζ (ϵ⋆ ↓ 1) (ϵ⋆ ↓ 2) κ ,
               wrong "wrong number of arguments"

list : 𝐄⋆ → 𝐊 → 𝐂
list =
  λ ϵ⋆ κ → # ϵ⋆ = 0 ⟶⊥ send null κ ,
             list (ϵ⋆ † 1) (single (λ ϵ → cons ⟨ ϵ⋆ ↓ 1 , ϵ ⟩ κ))

cons : 𝐄⋆ → 𝐊 → 𝐂
cons =
  twoarg (λ ϵ₁ ϵ₂ κ σ → new σ ∈ 𝐋 ⟶⊥
                            (λ σ′ → new σ′ ∈ 𝐋 ⟶⊥
                                        send (⟨ new σ | 𝐋 , new σ′ | 𝐋 , true ⟩
                                              in 𝐄)
                                            κ
                                            (update (new σ′ | 𝐋) ϵ₂ σ′) ,
                                      wrong "out of memory" σ′)
                            (update (new σ | 𝐋) ϵ₁ σ) ,
                      wrong "out of memory" σ)

-- [...]