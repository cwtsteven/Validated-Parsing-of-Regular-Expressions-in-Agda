open import Util
module Determinisation (Σ : Set)(dec : DecEq Σ) where


open import Subset.DecidableSubset
open import Automata Σ dec


NFA2DFA : NFA → DFA
NFA2DFA nfa = record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' }
 where
  open NFA nfa
  open NFA-Operations nfa using (δ*)
  Q' : Set
  Q' = Dec-ℙ Q
  δ' : Q' → Σ → Q'
  δ' (sub qs) a = sub (δ* qs a)
  q₀' : Q'
  q₀' = sub (singleton {Q} {Q?} q₀)
  F' : DecSubset Q'
  F' (sub qs) = ¬empty (qs ⋂ F) It
