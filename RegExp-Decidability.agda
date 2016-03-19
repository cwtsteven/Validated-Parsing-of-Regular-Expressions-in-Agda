{-
  This module contains the following proofs:
    ∀e∈RegExp. L(e) is decidable

  Steven Cheung
  Version 04-12-2015
-}
open import Util
module RegExp-Decidability (Σ : Set)(dec : DecEq Σ) where

open import Subset
open import RegularExpression Σ dec
open import DFA Σ dec
open import Translation Σ dec
open import Correctness Σ dec

{- proving L(Regex) is decidable -}
Dec-Lᴿ : ∀ e → Decidable (Lᴿ e)
Dec-Lᴿ e = Decidable-lem₁ (≈-sym (Lᴿ≈Lᴰ e)) (Dec-Lᴰ dfa)
  where
    dfa : DFA
    dfa = regexToDFA e
