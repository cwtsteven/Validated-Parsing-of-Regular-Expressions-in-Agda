{-
  Here the translation of a regular expression to a DFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung
  Version 15-03-2016
-}
open import Util
module Translation (Σ : Set)(dec : DecEq Σ) where

open import Function

open import RegularExpression Σ dec 
open import eNFA Σ dec
open import NFA Σ dec
open import DFA Σ dec


-- translate a Regular expression to a NFA with ε-step
regexToε-NFA : RegExp → ε-NFA
regexToε-NFA = regexToε-NFA'
  where
    open import Translation.RegExp-eNFA Σ dec renaming (regexToε-NFA to regexToε-NFA')


-- remove ε-steps
remove-ε-step : ε-NFA → NFA
remove-ε-step = remove-ε-step'
  where
    open import Translation.eNFA-NFA Σ dec renaming (remove-ε-step to remove-ε-step')


-- determinise the NFA by powerset construction
powerset-construction : NFA → DFA
powerset-construction = powerset-construction'
  where
    open import Translation.NFA-DFA Σ dec renaming (powerset-construction to powerset-construction')
    
-- minimise the DFA by removing inaccessible states and quotient construction
minimise : DFA → DFA
minimise = minimise'
  where
    open import Translation.DFA-MDFA Σ dec renaming (minimise to minimise')


-- translating a regular expression to a NFA
regexToNFA : RegExp → NFA
regexToNFA = remove-ε-step ∘ regexToε-NFA


-- translating a regular expression to a DFA
regexToDFA : RegExp → DFA
regexToDFA = powerset-construction ∘ remove-ε-step ∘ regexToε-NFA


-- translating a regular expression to a MDFA
regexToMDFA : (r : RegExp) → DFA
regexToMDFA r = minimise (regexToDFA r)
