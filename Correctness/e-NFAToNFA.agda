{-
  This module contains the following proofs:
    ∀nfa∈ε-NFA. L(nfa) ⊆ L(remove-ε-step nfa)
    ∀nfa∈ε-NFA. L(nfa) ⊇ L(remove-ε-step nfa)

  Steven Cheung 2015.
  Version 10-12-2015
-}
open import Util
module Correctness.e-NFAToNFA (Σ : Set)(dec : DecEq Σ) where

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
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ)
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ dec
open import State



module Lᵉᴺ⊆Lᴺ (ε-nfa : ε-NFA) where
  open ε-NFA ε-nfa
  open ε-NFA-Operations ε-nfa

  lem₁ : Lᵉᴺ ε-nfa ⊆ Lᴺ (remove-ε-step ε-nfa)
  lem₁ = undefined



Lᵉᴺ⊆Lᴺ : ∀ ε-nfa → Lᵉᴺ ε-nfa ⊆ Lᴺ (remove-ε-step ε-nfa)
Lᵉᴺ⊆Lᴺ = Lᵉᴺ⊆Lᴺ.lem₁ 



module Lᵉᴺ⊇Lᴺ (ε-nfa : ε-NFA) where
  nfa : NFA
  nfa = remove-ε-step ε-nfa

  open NFA nfa
  open NFA-Operations nfa
  open ε-NFA ε-nfa renaming (Q to Qₑ ; Q? to Qₑ? ; δ to δₑ ; q₀ to q₀ₑ ; F to Fₑ ; It to Itₑ) 
  open ε-NFA-Operations ε-nfa
    renaming (_⊢_ to _⊢ₑ_ ; _⊢*_ to _⊢*ₑ_ ; _⊢*₂_ to _⊢*₂ₑ_ ; _⊢ᵏ_─_ to _⊢ᵏₑ_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ ; ⊢*-lem₂ to ⊢*-lem₂ₑ ; ⊢*-lem₃ to ⊢*-lem₃ₑ ; ε-closure₃ to ε-closure₃ₑ)
   

  lem₂ : ∀ q w n q' w'
         → (q , w) ⊢ᵏ n ─ (q' , w')
         → (q , toΣᵉ* w) ⊢ᵏₑ n ─ (q' , toΣᵉ* w')
  lem₂ q w  zero    .q  .w  (refl , refl) = refl , refl
  lem₂ q ._ (suc n)  q'  w' (p , a , u , refl , (refl , prf₁) , prf₂) with p ∈ᵈ δₑ q (α a) | inspect (δₑ q (α a)) p
  lem₂ q ._ (suc n)  q'  w' (p , a , u , refl , (refl , prf₁) , prf₂) | true  | [ eq ] = p , α a , toΣᵉ* u , refl , (refl , eq) , lem₂ p u n q' w' prf₂
  lem₂ q ._ (suc n)  q'  w' (p , a , u , refl , (refl , prf₁) , prf₂) | false | [ eq ] = p , α a , toΣᵉ* u , refl , (refl , undefined) , undefined
  
  lem₃ : ∀ q
         → any (λ p → p ∈ᵈ Fₑ ∧ p ∈ᵈ ε-closure₃ₑ (length Itₑ) (⟦ q ⟧ᵈ {{Qₑ?}})) Itₑ ≡ true
         → Σ[ n ∈ ℕ ] Σ[ p ∈ Qₑ ] Σ[ uᵉ ∈ Σᵉ* ] ( toΣ* uᵉ ≡ [] × p ∈ᵍ Fₑ × (q , uᵉ) ⊢ᵏₑ n ─ (p , []))
  lem₃ = undefined
  
  lem₁ : Lᵉᴺ ε-nfa ⊇ Lᴺ nfa
  lem₁ w (q , q∈F , n , prf) with q ∈ᵈ Fₑ | inspect Fₑ q 
  lem₁ w (q , q∈F , n , prf) | true  | [ eq ] = toΣᵉ* w , Σᵉ*-lem₆ w , q , eq , n , lem₂ q₀ w n q [] prf
  lem₁ w (q , q∈F , n , prf) | false | [ eq ] with ∃p? Itₑ | inspect (∃p?) Itₑ
    where
      ∃p? : List Qₑ → Bool
      ∃p? = any (λ p → p ∈ᵈ Fₑ ∧ p ∈ᵈ ε-closure₃ₑ (length Itₑ) (⟦ q ⟧ᵈ {{Qₑ?}}))
  lem₁ w (q , q∈F , n , prf) | false | [ eq ] | true  | [ eq₁ ] with lem₃ q eq₁
  lem₁ w (q , q∈F , n , prf) | false | [ eq ] | true  | [ eq₁ ] | n₁ , p , uᵉ , u≡[] , p∈F , prf₁ = toΣᵉ* w ++ uᵉ , undefined , p , p∈F , n + n₁ , undefined
  lem₁ w (q ,  () , n , prf) | false | [ eq ] | false | [ eq₁ ]

  

Lᵉᴺ⊇Lᴺ : ∀ nfa → Lᵉᴺ nfa ⊇ Lᴺ (remove-ε-step nfa)
Lᵉᴺ⊇Lᴺ = Lᵉᴺ⊇Lᴺ.lem₁
