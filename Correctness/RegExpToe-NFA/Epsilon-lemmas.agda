open import Util
module Correctness.RegExpToe-NFA.Epsilon-lemmas (Σ : Set)(dec : DecEq Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ dec
open import State

nfa : ε-NFA
nfa = regexToε-NFA ε

open ε-NFA nfa
open ε-NFA-Operations nfa

module Lᴿ⊆Lᴺ where
 lem₁ : Lᴿ ε ⊆ Lᵉᴺ nfa
 lem₁ []       refl = [] , refl , init , refl , zero , refl , refl
 lem₁ (x ∷ xs) ()

module Lᴿ⊇Lᴺ where
 lem₁ : Lᴿ ε ⊇ Lᵉᴺ nfa
 lem₁ []       _ = refl
 lem₁ (x ∷ xs) (.[] , ()   , init , refl , zero  , refl , refl)
 lem₁ (x ∷ xs) (._  , _    , init , refl , suc n , init , α _ , _  , refl , (refl , ()) ,   _)
 lem₁ (x ∷ xs) (._  , w≡wᵉ , init , refl , suc n , init , E   , uᵉ , refl , (refl , ()) , prf)
   --= lem₁ (x ∷ xs) (uᵉ , w≡wᵉ , init , refl , n , prf)
