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
  lem₁ w (wᵉ , w≡wᵉ , q , q∈F , prf) = undefined



Lᵉᴺ⊆Lᴺ : ∀ ε-nfa → Lᵉᴺ ε-nfa ⊆ Lᴺ (remove-ε-step ε-nfa)
Lᵉᴺ⊆Lᴺ = Lᵉᴺ⊆Lᴺ.lem₁ 



module Lᵉᴺ⊇Lᴺ (ε-nfa : ε-NFA) where
  nfa : NFA
  nfa = remove-ε-step ε-nfa

  open NFA nfa
  open NFA-Operations nfa
  open ε-NFA ε-nfa renaming (Q to Qₑ ; Q? to Qₑ? ; δ to δₑ ; q₀ to q₀ₑ ; F to Fₑ ; It to Itₑ) 
  open ε-NFA-Operations ε-nfa
    renaming (_⊢_ to _⊢ₑ_ ; _⊢*_ to _⊢*ₑ_ ; _⊢*₂_ to _⊢*₂ₑ_ ; _⊢ᵏ_─_ to _⊢ᵏₑ_─_)

  -- tree?
  lem₁₀ : ∀ q n p w'
          → q →εᵏ n ─ p
          → Σ[ w ∈ Σᵉ* ] ( toΣ* w ≡ toΣ* w' × (q , w) ⊢ᵏₑ n ─ (p , w') )
  lem₁₀ q zero    .q w' refl = w' , refl , (refl , refl)
  lem₁₀ q (suc n)  p w' (p₁ , p₁δqE , p₁→εᵏp) with lem₁₀ p₁ n p w' p₁→εᵏp
  lem₁₀ q (suc n)  p w' (p₁ , p₁δqE , p₁→εᵏp) | w₁ , w₁≡w' , prf
    = E ∷ w₁ , w₁≡w' , (p₁ , E , w₁ , refl , (refl , p₁δqE) , prf)

  lem₉ : ∀ q p w' rs
         → Reachable? {q} p rs ≡ true
         → Σ[ n ∈ ℕ ] Σ[ w ∈ Σᵉ* ] ( toΣ* w ≡ toΣ* w' × (q , w) ⊢ᵏₑ n ─ (p , w') )
  lem₉ q p w' [] ()
  lem₉ q p w' (step  p₁ _ ∷ rs) reach with Qₑ? p p₁
  lem₉ q p w' (step .p  (n , prf) ∷ rs) reach | yes refl = n , lem₁₀ q n p w' prf
  lem₉ q p w' (step  p₁ _ ∷ rs) reach | no  _    = lem₉ q p w' rs reach

  lem₇ : ∀ q p w'
         → p ∈ᵍ ε-closure q
         → Σ[ n ∈ ℕ ] Σ[ w ∈ Σᵉ* ] ( toΣ* w ≡ toΣ* w' × (q , w) ⊢ᵏₑ n ─ (p , w') )
  lem₇ q  p w' p∈εq = lem₉ q p w' (n-step (length It) (step q (zero , refl) ∷ [])) p∈εq


  lem₅ : ∀ q a w q' ps
         → ⊢ε-decider ps q a q' ≡ true
         → Σ[ p ∈ Qₑ ] Σ[ n ∈ ℕ ] Σ[ w' ∈ Σᵉ* ] ( toΣ* (α a ∷ w) ≡ toΣ* w' × (q , w') ⊢ᵏₑ n ─ (p , α a ∷ w) × (p , α a , w) ⊢ₑ (q' , w) )
  lem₅ q a w q' []           ()
  lem₅ q a w q' (p ∷ ps) q⊢εa─q' with p ∈ᵈ ε-closure q | inspect (ε-closure q) p | q' ∈ᵈ δₑ p (α a) | inspect (δₑ p (α a)) q'
  lem₅ q a w q' (p ∷ ps) q⊢εa─q' | true  | [ p∈εq ] | true  | [ q'∈δpa ] with lem₇ q p (α a ∷ w) p∈εq
  lem₅ q a w q' (p ∷ ps) q⊢εa─q' | true  | [ p∈εq ] | true  | [ q'∈δpa ] | n , w' , w'≡aw , prf
    = p , n , w' , sym w'≡aw , prf , (refl , q'∈δpa)
  lem₅ q a w q' (p ∷ ps) q⊢εa─q' | false | [ p∉εq ] | _     | [ q'∈δpa ] = lem₅ q a w q' ps q⊢εa─q'
  lem₅ q a w q' (p ∷ ps) q⊢εa─q' | true  | [ p∈εq ] | false | [ q'∉δpa ] = lem₅ q a w q' ps q⊢εa─q'

  lem₄ : ∀ q a w q'
         → q ⊢ε a ─ q' ≡ true
         → Σ[ p ∈ Qₑ ] Σ[ n ∈ ℕ ] Σ[ w' ∈ Σᵉ* ] ( toΣ* (α a ∷ w) ≡ toΣ* w' × (q , w') ⊢ᵏₑ n ─ (p , α a ∷ w) × (p , α a , w) ⊢ₑ (q' , w) )
  lem₄ q a w q' q⊢εa─q' = lem₅ q a w q' Itₑ q⊢εa─q'


  lem₆ : ∀ q w' ps
         → ⊢εF-decider ps q ≡ true
         → Σ[ p ∈ Qₑ ] Σ[ n ∈ ℕ ] Σ[ w ∈ Σᵉ* ]  ( toΣ* w ≡ toΣ* w' × p ∈ᵍ Fₑ × (q , w) ⊢ᵏₑ n ─ (p , w') )
  lem₆ q w' []       ()
  lem₆ q w' (p ∷ ps) q⊢εF with p ∈ᵈ ε-closure q | inspect (ε-closure q) p | p ∈ᵈ Fₑ | inspect Fₑ p
  lem₆ q w' (p ∷ ps) q⊢εF | true  | [ p∈εq ] | true  | [ p∈Fₑ ] with lem₇ q p w' p∈εq
  lem₆ q w' (p ∷ ps) q⊢εF | true  | [ p∈εq ] | true  | [ p∈Fₑ ] | n , w , w≡w' , prf
    = p , n , w , w≡w' , p∈Fₑ , prf
  lem₆ q w' (p ∷ ps) q⊢εF | false | [ p∉εq ] | _     | [ p∉Fₑ ] = lem₆ q w' ps q⊢εF
  lem₆ q w' (p ∷ ps) q⊢εF | true  | [ p∈εq ] | false | [ p∉Fₑ ] = lem₆ q w' ps q⊢εF

  lem₃ : ∀ q w'
         → q ⊢εF ≡ true
         → Σ[ p ∈ Qₑ ] Σ[ n ∈ ℕ ] Σ[ w ∈ Σᵉ* ]  ( toΣ* w ≡ toΣ* w' × p ∈ᵍ Fₑ × (q , w) ⊢ᵏₑ n ─ (p , w') )
  lem₃ q w' q⊢εF = lem₆ q w' Itₑ q⊢εF

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
    = wᵉ₁ , n₁ + suc n₂ , trans (cong (λ u → a ∷ u) u≡wᵉ₂) awᵉ₂≡w₁ , ⊢*-lem₄ q wᵉ₁ n₁ p₁ (α a ∷ wᵉ₂) (suc n₂) q' [] prf₄ (p , α a , wᵉ₂ , refl , prf₅ , prf₃)
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl ,   ()) , prf₂) | false | [ eq ] | false | [ q⊬εa─p ]

  lem₈ : ∀ q wᵉ₁ n q' wᵉ₂
         → (q , wᵉ₁) ⊢ᵏₑ n ─ (q' , [])
         → (q , wᵉ₁ ++ wᵉ₂) ⊢ᵏₑ n ─ (q' , wᵉ₂)
  lem₈ q .[] zero    .q  wᵉ₂ (refl , refl) = refl , refl
  lem₈ q ._  (suc n)  q' wᵉ₂ (p , a , uᵉ , refl , (refl , prf₁) , prf₂)
    = p , a , uᵉ ++ wᵉ₂ , refl , (refl , prf₁) , lem₈ p uᵉ n q' wᵉ₂ prf₂

  lem₁ : Lᵉᴺ ε-nfa ⊇ Lᴺ nfa
  lem₁ w (q , q∈F , n , prf) with q ∈ᵈ Fₑ | inspect Fₑ q
  lem₁ w (q , q∈F , n , prf) | true  | [ q∈Fₑ ] with lem₂ q₀ w n q prf
  lem₁ w (q , q∈F , n , prf) | true  | [ q∈Fₑ ] | wᵉ , n₁ , w≡wᵉ , prf₁ = wᵉ , w≡wᵉ , q , q∈Fₑ , n₁ , prf₁
  lem₁ w (q , q∈F , n , prf) | false | [ q∉Fₑ ] with q ⊢εF | inspect _⊢εF q
  lem₁ w (q , q∈F , n , prf) | false | [ q∉Fₑ ] | true  | [ q⊢εF ] with lem₂ q₀ w n q prf | lem₃ q [] q⊢εF
  lem₁ w (q , q∈F , n , prf) | false | [ q∉Fₑ ] | true  | [ q⊢εF ] | wᵉ₁ , n₁ , w≡wᵉ₁ , prf₁ | p , n₂ , wᵉ₂ , wᵉ₂≡[] , p∈Fₑ , prf₂
    = wᵉ₁ ++ wᵉ₂ , w≡wᵉ₁wᵉ₂  , p , p∈Fₑ , n₁ + n₂ , ⊢*-lem₄ q₀ (wᵉ₁ ++ wᵉ₂) n₁ q wᵉ₂ n₂ p [] (lem₈ q₀ wᵉ₁ n₁ q wᵉ₂ prf₁) prf₂
    where
      open ≡-Reasoning
      w≡wᵉ₁wᵉ₂ : w ≡ toΣ* (wᵉ₁ ++ wᵉ₂)
      w≡wᵉ₁wᵉ₂ = begin
                 w                    ≡⟨ w≡wᵉ₁ ⟩
                 toΣ* wᵉ₁             ≡⟨ sym (List-lem₂ (toΣ* wᵉ₁)) ⟩
                 toΣ* wᵉ₁ ++ []       ≡⟨ cong (λ w → toΣ* wᵉ₁ ++ w) (sym wᵉ₂≡[]) ⟩
                 toΣ* wᵉ₁ ++ toΣ* wᵉ₂ ≡⟨ Σᵉ*-lem₁ wᵉ₁ wᵉ₂ ⟩
                 toΣ* (wᵉ₁ ++ wᵉ₂)
                 ∎
  lem₁ w (q ,  () , n , prf) | false | [ q∉Fₑ ] | false | [ q⊬εF ]
 

Lᵉᴺ⊇Lᴺ : ∀ nfa → Lᵉᴺ nfa ⊇ Lᴺ (remove-ε-step nfa)
Lᵉᴺ⊇Lᴺ = Lᵉᴺ⊇Lᴺ.lem₁
