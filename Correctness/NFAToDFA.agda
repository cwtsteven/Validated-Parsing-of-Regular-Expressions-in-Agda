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
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Subset renaming (Ø to ø)
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ)
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ dec
open import State

module Lᴺ⊆Lᴰ (nfa : NFA) where
 dfa : DFA
 dfa = powerset-construction nfa

 open NFA nfa renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; It to It₁) 
 open NFA-Operations nfa
 open DFA dfa
 open DFA-Operations dfa

 lem₁ : ∀ w
        → w ∈ Lᴺ nfa
        → w ∈ Lᴰ dfa
 lem₁ w (q , q∈F , prf) = undefined



Lᴺ⊆Lᴰ : ∀ nfa → Lᴺ nfa ⊆ Lᴰ (powerset-construction nfa)
Lᴺ⊆Lᴰ nfa w prf = lem₁ w prf
 where open Lᴺ⊆Lᴰ nfa






Lᴺ⊇Lᴰ : ∀ nfa → Lᴺ nfa ⊇ Lᴰ (powerset-construction nfa)
Lᴺ⊇Lᴰ = undefined
