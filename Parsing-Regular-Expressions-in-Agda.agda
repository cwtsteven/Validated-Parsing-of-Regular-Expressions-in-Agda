{-
  Parsing Regular Expressions in Agda - index file

  Steven Cheung
  Version 15-03-2016
-}
module Parsing-Regular-Expressions-in-Agda where

-- Subsets
open import Subset
open import Subset.DecidableSubset
open import Subset.VectorRep

-- Formal Languages
open import Language

-- Regular Expressions
open import RegularExpression

-- ε-NFA
open import eNFA

-- NFA
open import NFA

-- DFA
open import DFA

-- State construction for ε-NFA
open import State

-- State construction for quotient set
open import Quotient

-- Translation from regular expression to DFA
open import Translation
open import Translation.RegExp-eNFA
open import Translation.eNFA-NFA
open import Translation.NFA-DFA
open import Translation.DFA-MDFA

-- Correctness Proof of Translation
open import Correctness
open import Correctness.RegExp-eNFA
open import Correctness.RegExp-eNFA.Epsilon-lemmas
open import Correctness.RegExp-eNFA.Singleton-lemmas
open import Correctness.RegExp-eNFA.Union-lemmas
open import Correctness.RegExp-eNFA.Concatenation-lemmas
open import Correctness.RegExp-eNFA.KleenStar-lemmas
open import Correctness.eNFA-NFA
open import Correctness.NFA-DFA
open import Correctness.DFA-MDFA

-- Decidability of regular expressions
open import RegExp-Decidability

-- Utilities
open import Util

-- Examples
open import Example
