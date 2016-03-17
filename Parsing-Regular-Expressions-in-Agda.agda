{-
  Parsing Regular Expressions in Agda - index file

  Steven Cheung
  Version 15-03-2016
-}
module Parsing-Regular-Expressions-in-Agda where

-- Utilities
open import Util

-- General Subset
open import Subset

-- Decidable Subset
open import Subset.DecidableSubset

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

-- Translation from regular expression to DFA
open import Translation

-- Correctness Proof of Translation
open import Correctness

-- Decidability of regular expressions
open import RegExp-Decidability

-- Myhill-Nerode Theorem
open import Myhill-Nerode-Theorem
