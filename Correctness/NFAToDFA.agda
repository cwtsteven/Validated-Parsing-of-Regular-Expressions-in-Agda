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
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ)
open import Subset.VectorRep
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ dec
open import State

module Lᴺ⊆Lᴰ (nfa : NFA) where
 dfa : DFA
 dfa = powerset-construction nfa

 open NFA nfa renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; It to It₁) 
 open NFA-Operations nfa renaming (_⊢_ to _⊢₁_ ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_)
 open DFA dfa
 open DFA-Operations dfa

 lem₁ : ∀ w
        → w ∈ Lᴺ nfa
        → w ∈ Lᴰ dfa
 lem₁ w (q , q∈F , prf) = undefined



Lᴺ⊆Lᴰ : ∀ nfa → Lᴺ nfa ⊆ Lᴰ (powerset-construction nfa)
Lᴺ⊆Lᴰ nfa w prf = lem₁ w prf
 where open Lᴺ⊆Lᴰ nfa


module Lᴺ⊇Lᴰ (nfa : NFA) where
 dfa : DFA
 dfa = powerset-construction nfa

 open NFA nfa renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; It to It₁) 
 open NFA-Operations nfa renaming (_⊢_ to _⊢₁_ ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_)
 open DFA dfa
 open DFA-Operations dfa

 


 lem₂ : ∀ qs q w n qs' w'
        → q ∈ᵈ qs
        → (qs , w) ⊢ᵏ n ─ (qs' , w')
        → Σ[ q' ∈ Q₁ ] ( q' ∈ᵈ qs' × (q , w) ⊢ᵏ₁ n ─ (q' , w') )
 lem₂ qs q w  zero    .qs .w  q∈qs (refl , refl) = q , q∈qs , (refl , refl)
 lem₂ qs q ._ (suc n)  qs' w' q∈qs (ps , a , u , refl , (refl , prf₁) , prf₂) = undefined
 

 lem₁ : ∀ w
        → w ∈ Lᴰ dfa
        → w ∈ Lᴺ nfa
 lem₁ w (qs , qs∈F , n , prf) with Dec-∈F qs
 lem₁ w (qs , qs∈F , n , prf) | yes prf₁ with lem₂ (⟦ q₀₁ ⟧ᵈ {{Q₁?}}) q₀₁ w n qs [] (⟦a⟧-lem₁ Q₁? q₀₁) prf
 lem₁ w (qs , qs∈F , n , prf) | yes prf₁ | q' , q'∈qs' , prf₂ = q' , prf₁ q' q'∈qs' , n , prf₂
 lem₁ w (qs ,   () , n , prf) | no  prf₁




Lᴺ⊇Lᴰ : ∀ nfa → Lᴺ nfa ⊇ Lᴰ (powerset-construction nfa)
Lᴺ⊇Lᴰ = Lᴺ⊇Lᴰ.lem₁
