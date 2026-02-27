
{-# OPTIONS --rewriting --confluence-check --lossy-unification #-}

module Scm.Abstract-Syntax where


  open import Data.String.Base using (String) public
  Ide = String
  variable I : Ide


  open import Data.Integer.Base renaming (ℤ to Int) using () public
  data Con  : Set where
    int     : Int → Con
    #t #f   : Con
  variable K : Con


  mutual
    data Exp       : Set where
      con          : Con → Exp
      ide          : Ide → Exp
      ⦅_␣_⦆        : Exp → Exp⋆ → Exp
      ⦅lambda_␣_⦆  : Ide → Exp → Exp
      ⦅if_␣_␣_⦆    : Exp → Exp → Exp → Exp
      ⦅set!_␣_⦆    : Ide → Exp → Exp
    data Exp⋆      : Set where
      ␣␣␣          : Exp⋆
      _␣␣_         : Exp → Exp⋆ → Exp⋆
  variable E : Exp; E⋆ : Exp⋆


  mutual
    data Body      : Set where
      ␣␣_          : Exp → Body
      ⦅define_␣_⦆  : Ide → Exp → Body
      ⦅begin_⦆     : Body⁺ → Body
    data Body⁺     : Set where
      ␣␣_          : Body → Body⁺
      _␣␣_         : Body → Body⁺ → Body⁺
  data Prog        : Set where
    ␣␣␣            : Prog
    ␣␣_            : Body⁺ → Prog
  variable B : Body; B⁺ : Body⁺; Π : Prog
