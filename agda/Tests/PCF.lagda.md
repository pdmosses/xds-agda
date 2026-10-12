# PCF Tests

The following tests check that the denotations of some expressions
in the abstract syntax of the PCF language compute the expected values
when applied to an arbitrary environment `ρ`.

All the `refl` proofs of the tests below implicitly use the rewrite rule postulated as
a [property of the fixed-point operator], 
together with the rule for [eliminating injections] in arguments of
extensions of functions to flat domains.

```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Tests.PCF where
--"hide"
  open import Notation.Domains

  open import Examples.PCF.Abstract-Syntax
  open import Examples.PCF.Domain-Equations
  open import Examples.PCF.Semantic-Functions

  open import Properties.Functions
  open import Properties.Flat
--"/hide"
```

The following trivial abbreviations improve the readbility of AST terms in the tests:
```agda
  a  = α 0 ι
  b  = α 1 ι
  e  = α 2 ι
  
  g  = α 0 (ι ⇒ ι)
  h  = α 0 (ι ⇒ ι ⇒ ι)
```

Checking applications of successor and predecessor:
```agda
  check-41+1 :
    𝒜′⟦ ⦅ 𝐿 ⦅+1⦆ ␣ 𝐿 k 41 ⦆ ⟧ ρ ≡ ↑ 42
  check-41+1 = refl

  check-43-1 :
    𝒜′⟦ ⦅ 𝐿 ⦅−1⦆ ␣ 𝐿 k 43 ⦆ ⟧ ρ ≡ ↑ 42
  check-43-1 = refl
```

Checking that an environment binds a variable:
```agda
  lookup-var :
    𝒜′⟦ 𝑉 a ⟧ (ρ [ ↑ 42 / a ]′) ≡ ↑ 42
  lookup-var = refl
```

Checking applications of some combinators ($I$, $K$, $K\,I$):
```agda
  check-id :
    𝒜′⟦ ⦅ ⦅λ a ␣ 𝑉 a ⦆ ␣ 𝐿 k 42 ⦆ ⟧ ρ ≡ ↑ 42
  check-id = refl

  check-k :
    𝒜′⟦ ⦅ ⦅ ⦅λ a ␣ ⦅λ b ␣ 𝑉 a ⦆ ⦆ ␣ 𝐿 k 42 ⦆ ␣ 𝐿 k 41 ⦆ ⟧ ρ ≡ ↑ 42
  check-k = refl

  check-ki :
    𝒜′⟦ ⦅ ⦅ ⦅λ a ␣ ⦅λ b ␣ 𝑉 b ⦆ ⦆ ␣ 𝐿 k 41 ⦆ ␣ 𝐿 k 42 ⦆ ⟧ ρ ≡ ↑ 42
  check-ki = refl
```

Checking applications of conditional choice:
```agda
  check-if-zero :
    𝒜′⟦ ⦅ ⦅ ⦅ 𝐿 ⊃ ␣ ⦅ 𝐿 Z  ␣ 𝐿 k 0 ⦆ ⦆ ␣ 𝐿 k 42 ⦆ ␣ 𝐿 k 0 ⦆ ⟧ ρ ≡ ↑ 42
  check-if-zero = refl

  check-if-nonzero :
    𝒜′⟦ ⦅ ⦅ ⦅ 𝐿 ⊃ ␣ ⦅ 𝐿 Z  ␣ 𝐿 k 42 ⦆ ⦆ ␣ 𝐿 k 0 ⦆ ␣ 𝐿 k 42 ⦆ ⟧ ρ ≡ ↑ 42
  check-if-nonzero = refl
```

Checking applications of the fixed-point operator:
```agda
  check-fix-const : -- Y (λe. 42) ≡ 42
    𝒜′⟦ ⦅ 𝐿 Y ␣ ⦅λ e ␣ 𝐿 k 42 ⦆ ⦆ ⟧ ρ ≡ ↑ 42
  check-fix-const = refl

  check-fix-lambda : -- Y (λg. λa. 42) 2 ≡ 42
    𝒜′⟦ ⦅ ⦅ 𝐿 Y ␣ ⦅λ g ␣ ⦅λ a ␣ 𝐿 k 42 ⦆ ⦆ ⦆ ␣ 𝐿 k 2 ⦆ ⟧ ρ ≡ ↑ 42
  check-fix-lambda = refl
```

Checking counting down from 5 to zero:
```agda
  check-countdown : -- Y (λg. λa. ifz a then 42 else g (pred a)) 5 ≡ 42
    𝒜′⟦ ⦅ ⦅ 𝐿 Y ␣ ⦅λ g ␣ ⦅λ a ␣
                ⦅ ⦅ ⦅ 𝐿 ⊃ ␣ ⦅ 𝐿 Z  ␣ 𝑉 a ⦆ ⦆ ␣ 𝐿 k 42 ⦆ ␣
                      ⦅ 𝑉 g ␣ ⦅ 𝐿 ⦅−1⦆ ␣ 𝑉 a ⦆ ⦆ ⦆ ⦆ ⦆ ⦆ ␣ 𝐿 k 5 ⦆ ⟧ ρ ≡ ↑ 42
  check-countdown = refl
```

Checking addition of 4 to 38:
```agda
  check-sum-42 : -- Y (λh.λa.λb. ifz a then b else h(pred a)(𝐿 ⦅+1⦆ b)) 4 38 ≡ 42
    𝒜′⟦ ⦅ ⦅ ⦅ 𝐿 Y ␣ ⦅λ h ␣ ⦅λ a ␣ ⦅λ b ␣
                    ⦅ ⦅ ⦅ 𝐿 ⊃ ␣ ⦅ 𝐿 Z  ␣ 𝑉 a ⦆ ⦆ ␣ 𝑉 b ⦆ ␣ 
                      ⦅ ⦅ 𝑉 h ␣ ⦅ 𝐿 ⦅−1⦆ ␣ 𝑉 a ⦆ ⦆ ␣ ⦅ 𝐿 ⦅+1⦆ ␣ 𝑉 b ⦆ ⦆ ⦆ ⦆ ⦆ ⦆ ⦆
        ␣ 𝐿 k 4 ⦆ ␣ 𝐿 k 38 ⦆ ⟧ ρ ≡ ↑ 42
  check-sum-42 = refl
```

[property of the fixed-point operator]: ../Properties/Functions.md#function-domains
[eliminating injections]: ../Properties/Flat/index.md#flat-domains
