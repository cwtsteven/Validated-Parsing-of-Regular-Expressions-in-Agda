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
  nfa : NFA
  nfa = remove-ε-step ε-nfa

  open NFA nfa
  open NFA-Operations nfa
  open ε-NFA ε-nfa renaming (Q to Qₑ ; Q? to Qₑ? ; δ to δₑ ; q₀ to q₀ₑ ; F to Fₑ ; It to Itₑ) 
  open ε-NFA-Operations ε-nfa
    renaming (_⊢_ to _⊢ₑ_ ; _⊢*_ to _⊢*ₑ_ ; _⊢*₂_ to _⊢*₂ₑ_ ; _⊢ᵏ_─_ to _⊢ᵏₑ_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ ; ⊢*-lem₂ to ⊢*-lem₂ₑ ; ⊢*-lem₃ to ⊢*-lem₃ₑ)


  lem₁ : Lᵉᴺ ε-nfa ⊆ Lᴺ nfa
  lem₁ w (wᵉ , w≡wᵉ , q , q∈F , prf) = {!!}



Lᵉᴺ⊆Lᴺ : ∀ ε-nfa → Lᵉᴺ ε-nfa ⊆ Lᴺ (remove-ε-step ε-nfa)
Lᵉᴺ⊆Lᴺ = Lᵉᴺ⊆Lᴺ.lem₁ 



module Lᵉᴺ⊇Lᴺ (ε-nfa : ε-NFA) where
  nfa : NFA
  nfa = remove-ε-step ε-nfa

  open NFA nfa
  open NFA-Operations nfa
  open ε-NFA ε-nfa renaming (Q to Qₑ ; Q? to Qₑ? ; δ to δₑ ; q₀ to q₀ₑ ; F to Fₑ ; It to Itₑ) 
  open ε-NFA-Operations ε-nfa
    renaming (_⊢_ to _⊢ₑ_ ; _⊢*_ to _⊢*ₑ_ ; _⊢*₂_ to _⊢*₂ₑ_ ; _⊢ᵏ_─_ to _⊢ᵏₑ_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ ; ⊢*-lem₂ to ⊢*-lem₂ₑ ; ⊢*-lem₃ to ⊢*-lem₃ₑ ; ⊢*-lem₄ to ⊢*-lem₄ₑ)

  -- build a tree and search?
  lem₄ : ∀ q a w q'
         → q ⊢ε a ─ q' ≡ true
         → Σ[ p ∈ Q ] Σ[ n ∈ ℕ ] Σ[ w' ∈ Σᵉ* ] ( toΣ* (α a ∷ w) ≡ toΣ* w' × (q , w') ⊢ᵏₑ n ─ (p , α a ∷ w) × (p , α a , w) ⊢ₑ (q' , w) )
  lem₄ q a w q' q⊢εa─q' = {!!}
  
  lem₃ : ∀ q w
         → q ⊢εF ≡ true
         → Σ[ p ∈ Q ] Σ[ n ∈ ℕ ] Σ[ w' ∈ Σᵉ* ]  ( toΣ* w ≡ toΣ* w' × p ∈ᵍ Fₑ × (q , w) ⊢ᵏₑ n ─ (p , w') )
  lem₃ q w q⊢εF with Itₑ | ⊢εF-decider Itₑ q | inspect (⊢εF-decider Itₑ) q
  lem₃ q w q⊢εF | []       | true  | [ () ]
  lem₃ q w   () | []       | false | [ eq ]
  lem₃ q w q⊢εF | (p ∷ ps) | true  | [ eq ] with p ∈ᵈ ε-closure q | p ∈ᵈ F
  lem₃ q w q⊢εF | (p ∷ ps) | true  | [ eq ] | true  | true  = {!!}
  lem₃ q w q⊢εF | (p ∷ ps) | true  | [ eq ] | false | _     = {!!}
  lem₃ q w q⊢εF | (p ∷ ps) | true  | [ eq ] | _     | false = {!!}
  lem₃ q w   () | (p ∷ ps) | false | [ eq ]

  lem₂ : ∀ q w n q'
         → (q , w) ⊢ᵏ n ─ (q' , [])
         → Σ[ wᵉ ∈ Σᵉ* ] Σ[ n₁ ∈ ℕ ] ( w ≡ toΣ* wᵉ × (q , wᵉ) ⊢ᵏₑ n₁ ─ (q' , []) )
  lem₂ q .[] zero    .q  (refl , refl) = [] , zero , refl , (refl , refl)
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) with p ∈ᵈ δₑ q (α a) | inspect (δₑ q (α a)) p
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | true  | [ eq ] with lem₂ p u n q' prf₂
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | true  | [ eq ] | wᵉ , n₁ , u≡wᵉ , prf₃
    = α a ∷ wᵉ , suc n₁ , cong (λ u → a ∷ u) u≡wᵉ , (p , α a , wᵉ , refl , (refl , eq) , prf₃)
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | false | [ eq ] with q ⊢ε a ─ p | inspect (_⊢ε_─_ q a) p
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | false | [ eq ] | true  | [ q⊢εa─p ] with lem₂ p u n q' prf₂
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | false | [ eq ] | true  | [ q⊢εa─p ] | wᵉ₂ , n₂ , u≡wᵉ₂ , prf₃ with lem₄ q a wᵉ₂ p q⊢εa─p
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | false | [ eq ] | true  | [ q⊢εa─p ] | wᵉ₂ , n₂ , u≡wᵉ₂ , prf₃ | p₁ , n₁ , wᵉ₁ , awᵉ₂≡w₁ , prf₄ , prf₅
    = wᵉ₁ , n₁ + suc n₂ , trans (cong (λ u → a ∷ u) u≡wᵉ₂) awᵉ₂≡w₁ , {!!}
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl ,   ()) , prf₂) | false | [ eq ] | false | [ q⊬εa─p ]


  lem₁ : Lᵉᴺ ε-nfa ⊇ Lᴺ nfa
  lem₁ w (q , q∈F , n , prf) with q ∈ᵈ Fₑ | inspect Fₑ q
  lem₁ w (q , q∈F , n , prf) | true  | [ q∈Fₑ ] with lem₂ q₀ w n q prf
  lem₁ w (q , q∈F , n , prf) | true  | [ q∈Fₑ ] | wᵉ , n₁ , w≡wᵉ , prf₁ = wᵉ , w≡wᵉ , q , q∈Fₑ , n₁ , prf₁
  lem₁ w (q , q∈F , n , prf) | false | [ q∉Fₑ ] with q ⊢εF | inspect _⊢εF q
  lem₁ w (q , q∈F , n , prf) | false | [ q∉Fₑ ] | true  | [ q⊢εF ] with lem₂ q₀ w n q prf | lem₃ q [] q⊢εF
  lem₁ w (q , q∈F , n , prf) | false | [ q∉Fₑ ] | true  | [ q⊢εF ] | wᵉ₁ , n₁ , w≡wᵉ₁ , prf₁ | p , n₂ , wᵉ₂ , []≡wᵉ₂ , p∈Fₑ , prf₂ = wᵉ₁ ++ wᵉ₂ , {!!} , p , p∈Fₑ , n₁ + n₂ , {!!}
  lem₁ w (q ,  () , n , prf) | false | [ q∉Fₑ ] | false | [ q⊬εF ]
 

Lᵉᴺ⊇Lᴺ : ∀ nfa → Lᵉᴺ nfa ⊇ Lᴺ (remove-ε-step nfa)
Lᵉᴺ⊇Lᴺ = Lᵉᴺ⊇Lᴺ.lem₁
