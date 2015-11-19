module Minimisation (Σ : Set) where

open import Automata
open import DecidableSubset
open import Util

DFA2MDFA : DFA Σ → DFA Σ
DFA2MDFA dfa = record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' }
 where
  Q' : Set
  Q' = DecSubset (DFA.Q dfa)
  δ' : Q' → Σ → Q'
  δ' = undefined
  q₀' : Q'
  q₀' = undefined
  F' : DecSubset Q'
  F' = undefined
