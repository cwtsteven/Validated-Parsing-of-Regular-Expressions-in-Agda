{-
  This module contains the following proofs:
    ∀e∈RegExp.  L(e)   = L(regexToε-NFA e)
    ∀nfa∈ε-NFA. L(nfa) = L(remove-ε-step nfa)
    ∀nfa∈NFA.   L(nfa) = L(powerset-construction dfa)
    ∀dfa∈DFA.   L(dfa) = L(minimise dfa)

    ∀e∈RegExp.  L(e)   = L(regexToMDFA e)

  Steven Cheung
  Version 15-03-2016
-}
open import Util
module Correctness (Σ : Set)(dec : DecEq Σ) where

open import Function
open import Data.Product hiding (Σ)

open import Subset
open import RegularExpression Σ dec
open import eNFA Σ dec
open import NFA Σ dec
open import DFA Σ dec
open import MDFA Σ dec
open import Translation Σ dec

{- ∀e∈RegExp. L(e) = L(regexToε-NFA e) -}
Lᴿ≈Lᵉᴺ : ∀ e → Lᴿ e ≈ Lᵉᴺ (regexToε-NFA e)
Lᴿ≈Lᵉᴺ = Lᴿ≈Lᵉᴺ'
  where
    open import Correctness.RegExp-eNFA Σ dec renaming (Lᴿ≈Lᵉᴺ to Lᴿ≈Lᵉᴺ')


{- ∀nfa∈ε-NFA. L(nfa) = L(remove-ε-step nfa) -}
Lᵉᴺ≈Lᴺ : ∀ nfa → Lᵉᴺ nfa ≈ Lᴺ (remove-ε-step nfa)
Lᵉᴺ≈Lᴺ = Lᵉᴺ≈Lᴺ'
  where
    open import Correctness.eNFA-NFA Σ dec renaming (Lᵉᴺ≈Lᴺ to Lᵉᴺ≈Lᴺ')


{- ∀nfa∈NFA. L(nfa) = L(powerset-construction dfa) -}
Lᴺ≈Lᴰ : ∀ nfa → Lᴺ nfa ≈ Lᴰ (powerset-construction nfa)
Lᴺ≈Lᴰ = Lᴺ≈Lᴰ'
  where
    open import Correctness.NFA-DFA Σ dec renaming (Lᴺ≈Lᴰ to Lᴺ≈Lᴰ')


{- ∀dfa∈DFA.   L(dfa) = L(minimise dfa) -}
Lᴰ≈Lᴹ : ∀ dfa → Lᴰ dfa ≈ Lᴰ (minimise dfa)
Lᴰ≈Lᴹ = Minimise.Lᴰ≈Lᴹ
  where
    open import Correctness.DFA-MDFA Σ dec


{- ∀e∈RegExp. L(e) = L(regexToDFA e) -}
Lᴿ≈Lᴰ : ∀ e → Lᴿ e ≈ Lᴰ (regexToDFA e)
Lᴿ≈Lᴰ e = ≈-trans (Lᴿ≈Lᵉᴺ e) (≈-trans (Lᵉᴺ≈Lᴺ ε-nfa) (Lᴺ≈Lᴰ nfa))
  where
    ε-nfa : ε-NFA
    ε-nfa = regexToε-NFA e
    nfa : NFA
    nfa = regexToNFA e
    dfa : DFA
    dfa = regexToDFA e


{- ∀e∈RegExp. L(e) = L(regexToMDFA e) -}
Lᴿ≈Lᴹ : ∀ e → Lᴿ e ≈ Lᴰ (regexToMDFA e)
Lᴿ≈Lᴹ e = ≈-trans (Lᴿ≈Lᵉᴺ e) (≈-trans (Lᵉᴺ≈Lᴺ ε-nfa) (≈-trans (Lᴺ≈Lᴰ nfa) (Lᴰ≈Lᴹ dfa)))
  where
    ε-nfa : ε-NFA
    ε-nfa = regexToε-NFA e
    nfa : NFA
    nfa = regexToNFA e
    dfa : DFA
    dfa = regexToDFA e
    mdfa : DFA
    mdfa = regexToMDFA e


{- ∀dfa∈DFA. minimise(dfa) is Minimal -}
IsMinimal : ∀ dfa → Minimal (minimise dfa)
IsMinimal = IsMinimal'
  where
    open import Correctness.DFA-MDFA Σ dec renaming (IsMinimal to IsMinimal')
