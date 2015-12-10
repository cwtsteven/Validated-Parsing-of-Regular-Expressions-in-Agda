open import Util
module Correctness.RegExpToe-NFA.Singleton-lemmas (Σ : Set)(dec : DecEq Σ)(a : Σ) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_)
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ dec
open import State

e : RegExp
e = σ a

nfa : ε-NFA
nfa = regexToε-NFA e

open ε-NFA nfa
open ε-NFA-Operations nfa

lem₁ : Lᴿ e ⊆ Lᵉᴺ (regexToε-NFA e)
lem₁ []           ()
lem₁ (x ∷ y ∷ xs) ()
lem₁ (.a ∷ [])    refl with accept ∈ᵈ δ init (α a) | inspect (δ init (α a)) accept
lem₁ (.a ∷ [])    refl | true  | [ eq ] = accept , refl , 1 , accept , α a , [] , inj₁ (refl , λ ()) , (refl , eq) , (refl , refl)
lem₁ (.a ∷ [])    refl | false | [ eq ] with dec a a
lem₁ (.a ∷ [])    refl | false | [ () ] | yes refl
lem₁ (.a ∷ [])    refl | false | [ eq ] | no  a≢a   = ⊥-elim (a≢a refl)
