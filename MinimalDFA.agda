{-
  This module contains the definition of minimal DFA. 

  Steven Cheung
  Version 06-04-2016
-}
open import Util
module MinimalDFA (Σ : Set)(dec : DecEq Σ) where

open import Data.List hiding (any ; all) 
open import Data.Bool
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset
  renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; Ø to Øᵈ ; _⋃_ to _⋃ᵈ_ ; _⋂_ to _⋂ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ
                 ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ≈-refl to ≈ᵈ-refl ; ≈-trans to ≈ᵈ-trans ; ≈-sym to ≈ᵈ-sym)
open import Data.Vec hiding (_++_) renaming (_∈_ to _∈ⱽ_ ; tail to tailⱽ)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import Language Σ dec
open import DFA Σ dec


module Remove-Unreachable-States (dfa : DFA) where
  open DFA dfa
  open DFA-Operations dfa
  open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)
  
  -- Reachable from q₀
  Reachable : Q → Set
  Reachable q = Σ[ w ∈ Σ* ] (q₀ , w) ⊢* (q , [])

  data Qᴿ : Set where
    reach : ∀ q → Reachable q → Qᴿ
  
  q₀-reach : Reachable q₀
  q₀-reach = [] , (zero , ≋-refl , refl)

  reach-lem : ∀ {q w a n q'}
              → (q , w) ⊢ᵏ n ─ (q' , [])
              → (q , w ++ a ∷ []) ⊢ᵏ suc n ─ (δ q' a , [])
  reach-lem {q} {.[]} {a} {n = zero}  {q'} (q≋q' , refl)
    = δ q a , a , [] , refl , (refl , ≋-refl) , (δ-lem a q≋q' , refl)
  reach-lem {q} {._}  {a} {n = suc n} {q'} (p , b , u , refl , (refl , prf₁) , prf₂)
    = p , b , u ++ a ∷ [] , refl , (refl , prf₁) , reach-lem {p} {u} {a} {n} {q'} prf₂

  ⊢ᵏ-lem : ∀ {s q q'} → q ≋ q'
           → ∀ w n
           → (s , w) ⊢ᵏ n ─ (q , [])
           → (s , w) ⊢ᵏ n ─ (q' , [])
  ⊢ᵏ-lem q≋q' .[] zero    (s≋q , refl)
    = ≋-trans s≋q q≋q' , refl
  ⊢ᵏ-lem q≋q' ._  (suc n) (p , a , u , refl , (refl , prf₁) , prf₂)
    = p , a , u , refl , (refl , prf₁) , ⊢ᵏ-lem q≋q' u n prf₂
  

  -- easy
  reach-lem₁ : ∀ {q a} → Reachable q → Reachable (δ q a)
  reach-lem₁ {q} {a} (w , n , prf) = w ++ a ∷ [] , suc n , reach-lem {q₀} {w} {a} {n} {q} prf

  reach-lem₂ : ∀ {q q'} → q ≋ q' → Reachable q → Reachable q'
  reach-lem₂ q≋q' (w , n , prf) = w , n , ⊢ᵏ-lem q≋q' w n prf

  reach-lem₃ : ∀ {q a p} → p ≋ δ q a → Reachable q → Reachable p
  reach-lem₃ p≋δqa prf = reach-lem₂ (≋-sym p≋δqa) (reach-lem₁ prf)

All-Reachable-States : DFA → Set
All-Reachable-States dfa = ∀ q → Reachable q
  where
    open DFA dfa
    open DFA-Properties dfa
    open Remove-Unreachable-States dfa


module Irreducibility (D : DFA) where
  open DFA D
  open DFA-Operations D

  -- Distinquishable states
  infix 0 _≠_
  _≠_ : Q → Q → Set
  p ≠ q = Σ[ w ∈ Σ* ] (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F)
  

  -- there are several algorithms
  -- 1) Table-filling algorithm
  -- 2) Myhill-Nerode Theorem (Partition refinement)
  postulate Dec-≠ : ∀ p q → Dec (p ≠ q)
  --Dec-≠ p q with Dec-D-States p q
  --... | yes prf = yes (proj₂ (D-States-lem p q) prf)
  --... | no  prf = no  (D-States-lem₂ p q prf)
  

Irreducible : DFA → Set
Irreducible dfa = ∀ p q → ¬ p ≋ q → p ≠ q
  where
    open DFA dfa
    open DFA-Properties dfa
    open Irreducibility dfa


Minimal : DFA → Set
Minimal dfa = All-Reachable-States dfa × Irreducible dfa

