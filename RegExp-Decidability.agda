{-
  This module contains the following proofs:
    ∀e∈RegExp. L(e) is decidable

  Steven Cheung 2015.
  Version 4-12-2015
-}
module RegExp-Decidability (Σ : Set) where

open import Subset
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ
open import Correctness Σ

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
