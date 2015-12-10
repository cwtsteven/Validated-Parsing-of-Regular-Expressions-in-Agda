{-
  This module contains the following proofs:
    ∀nfa∈ε-NFA. L(nfa) ⊆ L(remove-ε-step nfa)
    ∀nfa∈ε-NFA. L(nfa) ⊇ L(remove-ε-step nfa)

  Steven Cheung 2015.
  Version 10-12-2015
-}
open import Util
module Correctness.e-NFAToNFA (Σ : Set)(dec : DecEq Σ) where

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
open import Automata Σ
open import Translation Σ dec
open import State

Lᵉᴺ⊆Lᴺ : ∀ nfa → Lᵉᴺ nfa ⊆ Lᴺ (remove-ε-step nfa)
Lᵉᴺ⊆Lᴺ nfa w (q , q∈F , n , q₀w⊢ᵏq[]) = undefined
 where
  open ε-NFA nfa
  open ε-NFA-Operations nfa

Lᵉᴺ⊇Lᴺ : ∀ nfa → Lᵉᴺ nfa ⊇ Lᴺ (remove-ε-step nfa)
Lᵉᴺ⊇Lᴺ = undefined
