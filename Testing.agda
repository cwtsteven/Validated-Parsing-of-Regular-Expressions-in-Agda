module Testing where

open import Data.List
open import Data.Unit
open import Data.Empty

open import Util
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data Σ : Set where
 a : Σ
 b : Σ

dec : DecEq Σ
dec a a = yes refl
dec a b = no (λ ())
dec b a = no (λ ())
dec b b = yes refl

open import RegularExpression Σ dec
open import Automata Σ dec
open import Parsing Σ dec
open import Util
open import Subset

regex : RegExp
regex = (σ a)

nfa : NFA
nfa = Regex2NFA regex

--dfa : DFA
--dfa = NFA2DFA nfa
        
open NFA nfa
