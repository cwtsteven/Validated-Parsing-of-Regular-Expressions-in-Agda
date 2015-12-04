{-
  This module contains the following proofs:
    ∀e∈RegExp.  L(e)   = L(regexToε-NFA e)
    ∀nfa∈ε-NFA. L(nfa) = L(remove-ε-step nfa)
    ∀nfa∈NFA.   L(nfa) = L(powerset-construction dfa)

  Steven Cheung 2015.
  Version 4-12-2015
-}

module Correctness (Σ : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Util
open import Subset renaming (Ø to ø)
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ
open import State

{- ∀e∈RegExp. L(e) = L(regexToε-NFA e) -}
Lᴿ≈Lᵉᴺ : ∀ e → Lᴿ e ≈ Lᵉᴺ (regexToε-NFA e)
Lᴿ≈Lᵉᴺ e = Lᴿ⊆Lᵉᴺ e , Lᴿ⊇Lᵉᴺ e
 where
  open import Correctness.RegExpToe-NFA Σ


{- ∀nfa∈ε-NFA. L(nfa) = L(remove-ε-step nfa) -}
Lᵉᴺ≈Lᴺ : ∀ nfa → Lᵉᴺ nfa ≈ Lᴺ (remove-ε-step nfa)
Lᵉᴺ≈Lᴺ nfa = Lᵉᴺ⊆Lᴺ nfa , Lᵉᴺ⊇Lᴺ nfa
 where
  open import Correctness.e-NFAToNFA Σ


{- ∀nfa∈NFA. L(nfa) = L(powerset-construction dfa) -}
Lᴺ≈Lᴰ : ∀ nfa → Lᴺ nfa ≈ Lᴰ (powerset-construction nfa)
Lᴺ≈Lᴰ nfa = Lᴺ⊆Lᴰ nfa , Lᴺ⊇Lᴰ nfa
 where
  open import Correctness.NFAToDFA Σ
