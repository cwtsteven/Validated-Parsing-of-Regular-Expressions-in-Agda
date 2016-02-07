{-
  This module contains the following proofs:
    ∀e∈RegExp. L(e) is decidable

  Steven Cheung 2015.
  Version 04-12-2015
-}
open import Util
module RegExp-Decidability (Σ : Set)(dec : DecEq Σ) where

open import Subset
open import RegularExpression Σ dec
open import Automata Σ dec
open import Translation Σ dec
open import Correctness Σ dec

{- proving L(Regex) is decidable -}
Dec-Lᴿ : ∀ e → Decidable (Lᴿ e)
Dec-Lᴿ e = Decidable-lem₁
             (≈-sym (≈-trans (Lᴿ≈Lᵉᴺ e) (≈-trans (Lᵉᴺ≈Lᴺ ε-nfa) (Lᴺ≈Lᴰ nfa))))
             (Dec-Lᴰ dfa)
         where
           ε-nfa : ε-NFA
           ε-nfa = regexToε-NFA e
           nfa : NFA
           nfa = regexToNFA e
           dfa : DFA
           dfa = regexToDFA e
