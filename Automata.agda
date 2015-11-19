open import Util
module Automata (Σ : Set)(dec : DecEq Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Subset

Σ* : Set
Σ* = List Σ

data Σᵉ : Set where
 E : Σᵉ
 α : Σ → Σᵉ

DecEq-Σᵉ : DecEq Σᵉ
DecEq-Σᵉ E     E      = yes refl
DecEq-Σᵉ E     (α  _) = no (λ ())
DecEq-Σᵉ (α a) E      = no (λ ())
DecEq-Σᵉ (α a) (α  b) with dec a b
DecEq-Σᵉ (α a) (α .a) | yes refl = yes refl
DecEq-Σᵉ (α a) (α  b) | no ¬a≡b  = no  (λ p → ¬σa≡σb ¬a≡b p)
 where
  lem : {a b : Σ} → α a ≡ α b → a ≡ b
  lem refl = refl
  ¬σa≡σb : ¬ (a ≡ b) → ¬ (α a ≡ α b)
  ¬σa≡σb ¬a≡b σa≡σb = ¬a≡b (lem σa≡σb)

Σᵉ* : Set
Σᵉ* = List Σᵉ


record NFA : Set₁ where
 field
  Q  : Set
  Q? : DecEq Q
  --It : List Q
  δ  : Q → Σᵉ → Subset Q
  q₀ : Q
  F  : Subset Q

module NFA-Operations (N : NFA) where
 open NFA N

 infix 7 _⊢_
 _⊢_ : (Q × Σᵉ × Σᵉ*) → (Q × Σᵉ*) → Set
 (q , x , xs) ⊢ (q' , w') = xs ≡ w' × q' ∈ δ q x
 

 infix 7 _⊢ᵏ_─_
 _⊢ᵏ_─_ : (Q × Σᵉ*) → ℕ → (Q × Σᵉ*) → Set
 (q , w) ⊢ᵏ zero    ─ (q' ,  w') = q ≡ q' × w ≡ w'
 (q , w) ⊢ᵏ (suc n) ─ (q' ,  w') = Σ[ p ∈ Q ] Σ[ a ∈ Σᵉ ] Σ[ w₁ ∈ Σᵉ* ] ( ((w ≡ a ∷ w₁ × a ≢ E) ⊎ (w ≡ w₁ × a ≡ E)) × (q , a , w₁) ⊢ (p , w₁) × (p , w₁) ⊢ᵏ n ─ (q' , w') )

 
 infix 7 _⊢*_
 _⊢*_ : (Q × Σᵉ*) → (Q × Σᵉ*) → Set
 (q , w) ⊢* (q' , w') = Σ[ n ∈ ℕ ] ((q , w) ⊢ᵏ n ─ (q' , w'))


Lᴺ : NFA → Subset Σ*
Lᴺ nfa = λ w → Σ[ q ∈ Q ] (q ∈ F × (q₀ , (Data.List.map α w)) ⊢* (q , []))
 where
  open NFA nfa
  open NFA-Operations nfa



record DFA : Set₁ where
 field
  Q  : Set
  δ  : Q → Σ → Q
  q₀ : Q
  F  : Subset Q

module DFA-Operations (M : DFA) where
 open DFA M
  
 δ* : Q → Σ* → Q
 δ* q [] = q
 δ* q (a ∷ w) = δ* (δ q a) w
  
 δ₀ : Σ* → Q
 δ₀ w = δ* q₀ w

Lᴰ : DFA → Subset Σ*
Lᴰ dfa w = δ₀ w ∈ F
 where
  open DFA dfa
  open DFA-Operations dfa
