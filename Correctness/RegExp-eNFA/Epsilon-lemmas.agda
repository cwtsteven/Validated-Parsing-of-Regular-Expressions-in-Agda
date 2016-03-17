{-
  This module contains the following proofs:
    L(ε) ⊆ L(regexToε-NFA ε)
    L(ε) ⊇ L(regexToε-NFA ε)

  Steven Cheung
  Version 07-01-2016
-}

open import Util
module Correctness.RegExp-eNFA.Epsilon-lemmas (Σ : Set)(dec : DecEq Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Language Σ dec
open import RegularExpression Σ dec
open import eNFA Σ dec
open import Translation.RegExp-eNFA Σ dec
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
  lem₁ (x ∷ xs) (._  , w≡wᵉ , init , refl , suc n , init , E   , uᵉ , refl , (refl ,  _) , prf)
    = lem₁ (x ∷ xs) (uᵉ , w≡wᵉ , init , refl , n , prf)
