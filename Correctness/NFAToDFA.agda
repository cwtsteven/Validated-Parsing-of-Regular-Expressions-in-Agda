{-
  This module contains the following proofs:
    ∀nfa∈NFA. L(nfa) ⊆ L(powerset-construction dfa)
    ∀nfa∈NFA. L(nfa) ⊇ L(powerset-construction dfa)

  Steven Cheung 2015.
  Version 10-12-2015
-}
open import Util
module Correctness.NFAToDFA (Σ : Set)(dec : DecEq Σ) where

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

Lᴺ⊆Lᴰ : ∀ nfa → Lᴺ nfa ⊆ Lᴰ (powerset-construction nfa)
Lᴺ⊆Lᴰ = undefined

Lᴺ⊇Lᴰ : ∀ nfa → Lᴺ nfa ⊇ Lᴰ (powerset-construction nfa)
Lᴺ⊇Lᴰ = undefined
