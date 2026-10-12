# Naturals

Agda allows decimal notation for natural numbers, as well as unary notation
using `zero` and `suc`.
```agda
--"hide"
{-# OPTIONS --rewriting --confluence-check #-}

--"/hide"
module Notation.Flat.Naturals where
--"hide"
  
  open import Notation.Flat
  open import Notation.Flat.Booleans
--"/hide"
  open import Agda.Builtin.Nat public  using (Nat; suc; _+_; _-_)
                                       renaming (_==_ to _==ᴺ_)
  Nat⊥ = Nat +⊥
  instance 
    eqNat : Eq Nat
    _==_ {{eqNat}} = _==ᴺ_
```
