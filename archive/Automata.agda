open import Util
module Automata (Σ : Set)(dec : DecEq Σ) where
open import Data.List
open import Data.Bool
open import Relation.Nullary
open import Data.Product hiding (Σ)
open import Data.Nat

open import Relation.Binary.PropositionalEquality

open import Subset.DecidableSubset

Σ* : Set
Σ* = List Σ

infix 0 _,_,_,_,_,_
record NFA : Set₁ where
 constructor _,_,_,_,_,_
 field
  Q  : Set
  Q? : DecEq Q
  It : List Q
  δ  : Q → Σ → DecSubset Q
  q₀ : Q
  F  : DecSubset Q

module NFA-Operations (N : NFA) where
 open NFA N

 δ' : List Q → Σ → DecSubset Q
 δ' [] a =  Ø
 δ' (x ∷ xs) a = δ x a ⋃ δ' xs a

 δ* : DecSubset Q → Σ → DecSubset Q
 δ* qs = λ a → δ' (toList qs It) a

 δ^ : DecSubset Q → Σ* → DecSubset Q
 δ^ qs [] = qs
 δ^ qs (x ∷ xs) = δ^ (δ* qs x) xs

 δ¹ : Q → Σ* → DecSubset Q
 δ¹ q w = δ^ (singleton {dec = Q?} q) w

 δ₀ : Σ* → DecSubset Q
 δ₀ w = δ¹ q₀ w

 mutual
  infix 7 _⊢_
  _⊢_ : (Q × Σ*) → (Q × Σ*) → Bool
  (q , [])      ⊢ (q' , [])     = true
  (q , [])      ⊢ (q' , x ∷ xs) = false
  (q , x ∷ xs)  ⊢ (q' , w') with DecEq-List dec xs w' | inspect (DecEq-List dec xs) w'
  (q , x ∷ .w') ⊢ (q' , w') | yes refl | [ eq ] = q' ∈ δ q x
  (q , x ∷ xs)  ⊢ (q' , w') | no  _    | [ eq ] = false

  infix 7 _⊢ᵏ_[_]
  _⊢ᵏ_[_] : (Q × Σ*) → ℕ → (Q × Σ*) → Bool
  (q , w) ⊢ᵏ n [ q' , w' ] = ∃p It (q , w) n (q' , w')
  
  ∃p : List Q → (Q × Σ*) → ℕ → (Q × Σ*) → Bool
  ∃p []       _            _       _         = false
  ∃p _        (q , w)      zero    (q' , w') with Q? q q' | DecEq-List dec w w'
  ∃p _        (q , w)      zero    (.q , .w) | yes refl | yes refl = true
  ∃p _        (q , w)      zero    (q' , w') | _        | no  _    = false
  ∃p _        (q , w)      zero    (q' , w') | no _     | _        = false
  ∃p _        (q , [])     _       (q' , w') = (q , []) ⊢ (q' , w')
  ∃p (p ∷ ps) (q , x ∷ xs) (suc n) (q' , w') = (q , x ∷ xs) ⊢ (p , xs) ∧ (p , xs) ⊢ᵏ n [ q' , w' ] ∨ ∃p ps (q , x ∷ xs) (suc n) (q' , w')

  infix 7 _⊢*_
  _⊢*_ : (Q × Σ*) → (Q × Σ*) → Bool
  (q , w) ⊢* (q' , w') = ∃n (Data.List.length w) (q , w) (q' , w')
 
  ∃n : ℕ → (Q × Σ*) → (Q × Σ*) → Bool
  ∃n zero    (q , w) (q' , w') = (q , w) ⊢ᵏ zero [ q' , w' ]
  ∃n (suc n) (q , w) (q' , w') = (q , w) ⊢ᵏ (suc n) [ q' , w' ] ∨ (q , w) ⊢ᵏ n [ q' , w' ]

  ∃q : List Q → Σ* → Bool
  ∃q []       _  = false
  ∃q (q ∷ qs) w = ((q₀ , w) ⊢* (q , []) ∧ q ∈ F) ∨ ∃q qs w 

Lᴺ : NFA → DecSubset Σ*
Lᴺ nfa = ∃q It --λ w → ¬empty (δ₀ w ⋂ F) It --
 where
  open NFA nfa
  open NFA-Operations nfa


infix 0 _,_,_,_
record DFA : Set₁ where
 constructor _,_,_,_
 field
  Q  : Set
  δ  : Q → Σ → Q
  q₀ : Q
  F  : DecSubset Q

module DFA-Operations (M : DFA) where
 open DFA M
  
 δ^ : Q → Σ* → Q
 δ^ q [] = q
 δ^ q (x ∷ xs) = δ^ (δ q x) xs
  
 δ₀ : Σ* → Q
 δ₀ w = δ^ q₀ w

Lᴰ : DFA → DecSubset Σ*
Lᴰ dfa w = δ₀ w ∈ F
 where
  open DFA dfa
  open DFA-Operations dfa
