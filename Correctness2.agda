{-
  This module contains the following proofs:
    ∀e∈RegExp.  L(e)   = L(regexToε-NFA e)
    ∀nfa∈ε-NFA. L(nfa) = L(remove-ε-step nfa)
    ∀nfa∈NFA.   L(nfa) = L(powerset-construction dfa)

  Steven Cheung 2015.
  Version 9-12-2015
-}
open import Util
module Correctness2 (Σ : Set)(dec : DecEq Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Subset renaming (Ø to ø)
open import Language Σ
open import RegularExpression Σ
open import Automata2 Σ
open import Translation2 Σ dec
open import State

{- ∀e∈RegExp. L(e) = L(regexToε-NFA e) -}
Lᴿ≈Lᵉᴺ : ∀ e → Lᴿ e ≈ Lᵉᴺ (regexToε-NFA e)
Lᴿ≈Lᵉᴺ e = Lᴿ⊆Lᵉᴺ e , Lᴿ⊇Lᵉᴺ e
 where
  open import Correctness2.RegExpToe-NFA Σ dec

{-

{- ∀nfa∈ε-NFA. L(nfa) = L(remove-ε-step nfa) -}
Lᵉᴺ≈Lᴺ : ∀ nfa → Lᵉᴺ nfa ≈ Lᴺ (remove-ε-step nfa)
Lᵉᴺ≈Lᴺ nfa = Lᵉᴺ⊆Lᴺ nfa , Lᵉᴺ⊇Lᴺ nfa
 where
  open import Correctness2.e-NFAToNFA Σ


{- ∀nfa∈NFA. L(nfa) = L(powerset-construction dfa) -}
Lᴺ≈Lᴰ : ∀ nfa → Lᴺ nfa ≈ Lᴰ (powerset-construction nfa)
Lᴺ≈Lᴰ nfa = Lᴺ⊆Lᴰ nfa , Lᴺ⊇Lᴰ nfa
 where
  open import Correctness2.NFAToDFA Σ
-}
