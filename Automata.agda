{-
  Here the Automata and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 2.2: Regular sets, their generators, and their recognizers
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 26-11-2015
-}

module Automata (Σ : Set) where

open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Nat

open import Util
open import Subset
open import Language Σ

-- Nondeterministic finite automata with ε-step
-- section 2.2.3: Finite Automata
record ε-NFA : Set₁ where
 field
  Q  : Set
  δ  : Q → Σᵉ → Subset Q {lzero}
  q₀ : Q
  F  : Subset Q {lzero}
  F? : Decidable F

-- section 2.2.3: Finite Automata
module ε-NFA-Operations (N : ε-NFA) where
 open ε-NFA N

 -- a move from (q , aw) to (q' , w)
 infix 7 _⊢_
 _⊢_ : (Q × Σᵉ × Σᵉ*) → (Q × Σᵉ*) → Set
 (q , a , w) ⊢ (q' , w') = w ≡ w' × q' ∈ δ q a

 -- k moves from (q , w) to (q' , w')
 infix 7 _⊢ᵏ_─_
 _⊢ᵏ_─_ : (Q × Σᵉ*) → ℕ → (Q × Σᵉ*) → Set
 (q , w) ⊢ᵏ zero    ─ (q' , w') = q ≡ q' × w ≡ w'
 (q , w) ⊢ᵏ (suc n) ─ (q' , w')
   = Σ[ p ∈ Q ] Σ[ a ∈ Σᵉ ] Σ[ u ∈ Σᵉ* ]
     (((w ≡ a ∷ u × a ≢ E) ⊎ (w ≡ u × a ≡ E)) × (q , a , u) ⊢ (p , u) × (p , u) ⊢ᵏ n ─ (q' , w'))
                                  
 -- transitive closure of ⊢
 infix 7 _⊢*_
 _⊢*_ : (Q × Σᵉ*) → (Q × Σᵉ*) → Set
 (q , w) ⊢* (q' , w') = Σ[ n ∈ ℕ ] ((q , w) ⊢ᵏ n ─ (q' , w'))

 -- alternative definition of ⊢*, we will later prove that ⊢*₂ is equivalent to ⊢*
 infix 7 _⊢*₂_
 _⊢*₂_ : (Q × Σᵉ*) → (Q × Σᵉ*) → Set
 (q , w) ⊢*₂ (q' , w') = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] Σ[ p ∈ Q ] Σ[ u ∈ Σᵉ* ]
                         ((q , w) ⊢ᵏ n ─ (p , u) × (p , u) ⊢ᵏ m ─ (q' , w'))
                         

 ⊢ᵏ-lem₃ : ∀ q w n q' w' p u
           → p ≡ q' → u ≡ w'
           → (q , w) ⊢ᵏ n ─ (p , u)
           → (q , w) ⊢ᵏ n ─ (q' , w')
 ⊢ᵏ-lem₃ q w zero    q' w' p u p≡q' u≡w' (q≡p , w≡u)
   = trans q≡p p≡q' , trans w≡u u≡w'
 ⊢ᵏ-lem₃ q w (suc n) q' w' p u p≡q' u≡w' (r , a , v , prf₁ , prf₂ , rv⊢ᵏpu)
   = r , a , v , prf₁ , prf₂ , ⊢ᵏ-lem₃ r v n q' w' p u p≡q' u≡w' rv⊢ᵏpu


 ⊢ᵏ-lem₂ : ∀ q w n q' w'
           → (q , w) ⊢ᵏ n ─ (q' , w')
           → (q , w) ⊢ᵏ (n + zero) ─ (q' , w')
 ⊢ᵏ-lem₂ q w zero    q' w' (q≡q' , w≡w')
   = (q≡q' , w≡w')
 ⊢ᵏ-lem₂ q w (suc n) q' w' (p , a , u , prf₁ , prf₂ , prf₃)
   = p , a , u , prf₁ , prf₂ , ⊢ᵏ-lem₂ p u n q' w' prf₃


 ⊢ᵏ-lem₁ : ∀ q w n q' w' p u m
           → (q , w) ⊢ᵏ n ─ (p , u)
           → (p , u) ⊢ᵏ m ─ (q' , w')
           → (q , w) ⊢ᵏ (n + m) ─ (q' , w')
 ⊢ᵏ-lem₁ q w zero    q' w' p u zero       (q≡p , w≡u) (p≡q' , u≡w')
   = trans q≡p p≡q' , trans w≡u u≡w'
 ⊢ᵏ-lem₁ q w zero    q' w' p u (suc m) (q≡p , w≡u) (r , a , v , inj₁ (u≡av , a≢E) , (refl , r∈δpa) , rv⊢ᵏq'w')
   = r , a , v , inj₁ (trans w≡u u≡av , a≢E)  , (refl , subst (λ p → r ∈ δ p a) (sym q≡p) r∈δpa) , rv⊢ᵏq'w'
 ⊢ᵏ-lem₁ q w zero    q' w' p u (suc m) (q≡p , w≡u) (r , a , v , inj₂ (u≡v  , a≡E) , (refl , r∈δpE) , rv⊢ᵏq'w')
   = r , a , v , inj₂ (trans w≡u u≡v  , a≡E)  , (refl , subst (λ p → r ∈ δ p a) (sym q≡p) r∈δpE) , rv⊢ᵏq'w'
 ⊢ᵏ-lem₁ q w (suc n) q' w' p u zero    (r , a , v , prf₁ , prf₂ , rv⊢ᵏpu) (p≡q' , u≡w')
   = r , a , v ,  prf₁ , prf₂ , ⊢ᵏ-lem₃ r v (n + zero) q' w' p u p≡q' u≡w' (⊢ᵏ-lem₂ r v n p u rv⊢ᵏpu)
 ⊢ᵏ-lem₁ q w (suc n) q' w' p u (suc m) (r , a , v , prf₁ , prf₂ , rv⊢ᵏpu) pu⊢ᵏq'w'
   = r , a , v , prf₁ , prf₂ , ⊢ᵏ-lem₁ r v n q' w' p u (suc m) rv⊢ᵏpu pu⊢ᵏq'w'


 ⊢*-lem₁ : ∀ {q w q' w'}
           → (q , w) ⊢*₂ (q' , w')
           → (q , w) ⊢* (q' , w')
 ⊢*-lem₁ {q} {w} {q'} {w'} (n  , m  , p , u , prf₁ , prf₂)
   = n + m , ⊢ᵏ-lem₁ q w n q' w' p u m prf₁ prf₂ 

-- Language denoted by a ε-NFA
-- section 2.2.3: Finite Automata
Lᵉᴺ : ε-NFA → Language
Lᵉᴺ nfa = λ w → Σ[ q ∈ Q ] (q ∈ F × (q₀ , toΣᵉ* w) ⊢* (q , []))
 where
  open ε-NFA nfa
  open ε-NFA-Operations nfa
  

-- Nondeterministic finite automata w/o ε-step
-- section 2.2.3: Finite Automata
record NFA : Set₁ where
 field
  Q  : Set
  δ  : Q → Σ → Subset Q {lzero}
  q₀ : Q
  F  : Subset Q {lzero}
  F? : Decidable F

module NFA-Operations (N : NFA) where
 open NFA N

  -- a move from (q , aw) to (q' , w)
 infix 7 _⊢_
 _⊢_ : (Q × Σ × Σ*) → (Q × Σ*) → Set
 (q , a , w) ⊢ (q' , w') = w ≡ w' × q' ∈ δ q a

 -- k moves from (q , w) to (q' , w')
 infix 7 _⊢ᵏ_─_
 _⊢ᵏ_─_ : (Q × Σ*) → ℕ → (Q × Σ*) → Set
 (q , w) ⊢ᵏ zero    ─ (q' , w') = q ≡ q' × w ≡ w'
 (q , w) ⊢ᵏ (suc n) ─ (q' , w')
   = Σ[ p ∈ Q ] Σ[ a ∈ Σ ] Σ[ u ∈ Σ* ]
     (w ≡ a ∷ u × (q , a , u) ⊢ (p , u) × (p , u) ⊢ᵏ n ─ (q' , w'))
                                  
 -- transitive closure of ⊢
 infix 7 _⊢*_
 _⊢*_ : (Q × Σ*) → (Q × Σ*) → Set
 (q , w) ⊢* (q' , w') = Σ[ n ∈ ℕ ] ((q , w) ⊢ᵏ n ─ (q' , w'))

-- Language denoted by a NFA
-- section 2.2.3: Finite Automata
Lᴺ : NFA → Language
Lᴺ nfa = λ w → Σ[ q ∈ Q ] (q ∈ F × (q₀ , w) ⊢* (q , []))
 where
  open NFA nfa
  open NFA-Operations nfa


-- Deterministic finite automata
-- section 2.2.3: Finite Automata
record DFA : Set₂ where
 field
  Q  : Set₁
  δ  : Q → Σ → Q
  q₀ : Q
  F  : Subset Q {lzero}
  F? : Decidable F

module DFA-Operations (D : DFA) where
 open DFA D

 δ* : Q → Σ* → Q
 δ* q []      = q
 δ* q (a ∷ w) = δ* (δ q a) w
  
 δ₀ : Σ* → Q
 δ₀ w = δ* q₀ w

-- Language denoted by a DFA
Lᴰ : DFA → Language
Lᴰ dfa = λ w → δ₀ w ∈ F
 where
  open DFA dfa
  open DFA-Operations dfa
