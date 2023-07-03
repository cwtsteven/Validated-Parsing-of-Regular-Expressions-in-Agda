{-
  This module contains the following proofs:

  Steven Cheung
  Version 10-01-2016
-}
open import Util
open import RegularExpression
module Correctness.RegExp-eNFA.Union-lemmas (Σ : Set)(dec : DecEq Σ)(e₁ : RegularExpression.RegExp Σ dec)(e₂ : RegularExpression.RegExp Σ dec) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_)
open import Language Σ dec
open import eNFA Σ dec
open import Translation.RegExp-eNFA Σ dec
open import State

nfa : ε-NFA
nfa = regexToε-NFA (e₁ ∣ e₂)

nfa₁ : ε-NFA
nfa₁ = regexToε-NFA e₁

nfa₂ : ε-NFA
nfa₂ = regexToε-NFA e₂

open ε-NFA nfa
open ε-NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
open ε-NFA nfa₂ renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
open ε-NFA-Operations nfa
open ε-NFA-Operations nfa₁ renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_)
open ε-NFA-Operations nfa₂ renaming (_⊢_ to _⊢ₑ₂_ ; _⊢*_ to _⊢*ₑ₂_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₂_─_)

module Lᴿ⊆Lᴺ where
  lem₆ : ∀ q w n q' w'
         → (q , w) ⊢ᵏₑ₂ n ─ (q' , w')
         → (⊍inj₂ q , w) ⊢ᵏ n ─ (⊍inj₂ q' , w')
  lem₆ q w zero   .q .w (refl , refl)
    = refl , refl
  lem₆ q w (suc n) q' w' (p , a , u , prf₁ , prf₂ , prf₃)
    = ⊍inj₂ p , a , u , prf₁ , prf₂ , lem₆ p u n q' w' prf₃


  lem₅ : ∀ q w w'
         → (q₀₂ , w) ⊢*ₑ₂ (q , w')
         → (q₀ , E ∷ w) ⊢* (⊍inj₂ q , w')
  lem₅ q w w' (n , prf) with ⊍inj₂ q₀₂ ∈ᵈ? δ q₀ E | inspect (δ q₀ E) (⊍inj₂ q₀₂)
  lem₅ q w w' (n , prf) | true  | [ eq ]
    = suc n , ⊍inj₂ q₀₂ , E , w , refl , (refl , eq) , lem₆ q₀₂ w n q w' prf
  lem₅ q w w' (n , prf) | false | [ eq ] with Q₂? q₀₂ q₀₂
  lem₅ q w w' (n , prf) | false | [ () ] | yes refl
  lem₅ q w w' (n , prf) | false | [ eq ] | no  q₀₂≢q₀₂ = ⊥-elim (q₀₂≢q₀₂ refl)
  
  
  lem₄ : ∀ {w}
         → w ∈ Lᵉᴺ nfa₂
         → w ∈ Lᵉᴺ nfa
  lem₄ {w} (wᵉ , w≡wᵉ , q , q∈F , prf)
    = E ∷ wᵉ , w≡wᵉ , ⊍inj₂ q , q∈F , lem₅ q wᵉ [] prf
  
  
  lem₃ : ∀ q w n q' w'
         → (q , w) ⊢ᵏₑ₁ n ─ (q' , w')
         → (⊍inj₁ q , w) ⊢ᵏ n ─ (⊍inj₁ q' , w')
  lem₃ q w zero   .q .w (refl , refl)
    = refl , refl
  lem₃ q w (suc n) q' w' (p , a , u , prf₁ , prf₂ , prf₃)
    = ⊍inj₁ p , a , u , prf₁ , prf₂ , lem₃ p u n q' w' prf₃
  
  
  lem₂ : ∀ q w w'
         → (q₀₁ , w) ⊢*ₑ₁ (q , w')
         → (q₀ , E ∷ w) ⊢* (⊍inj₁ q , w')
  lem₂ q w w' (n , prf) with ⊍inj₁ q₀₁ ∈ᵈ? δ q₀ E | inspect (δ q₀ E) (⊍inj₁ q₀₁)
  lem₂ q w w' (n , prf) | true  | [ eq ]
    = suc n , ⊍inj₁ q₀₁ , E , w , refl , (refl , eq) , lem₃ q₀₁ w n q w' prf
  lem₂ q w w' (n , prf) | false | [ eq ] with Q₁? q₀₁ q₀₁
  lem₂ q w w' (n , prf) | false | [ () ] | yes refl    
  lem₂ q w w' (n , prf) | false | [ eq ] | no  q₀₁≢q₀₁ = ⊥-elim (q₀₁≢q₀₁ refl)
  
  
  lem₁ : ∀ {w}
         → w ∈ Lᵉᴺ nfa₁
         → w ∈ Lᵉᴺ nfa
  lem₁ {w} (wᵉ , w≡wᵉ , q , q∈F , prf)
    = E ∷ wᵉ , w≡wᵉ , ⊍inj₁ q , q∈F , lem₂ q wᵉ [] prf
  
module Lᴿ⊇Lᴺ where
  lem₁₁ : ∀ q wᵉ n q' wᵉ'
          → ¬ (⊍inj₁ q , wᵉ) ⊢ᵏ n ─ (⊍inj₂ q' , wᵉ')
  lem₁₁ q wᵉ zero    q' .wᵉ  (() , refl)
  lem₁₁ q wᵉ (suc n) q'  wᵉ' (init    , _ , _  , _ , (_ , ()) ,    _)
  lem₁₁ q wᵉ (suc n) q'  wᵉ' (⊍inj₁ p , _ , uᵉ , _ , _        , prf₃)
    = lem₁₁ p uᵉ n q' wᵉ' prf₃
  lem₁₁ q wᵉ (suc n) q'  wᵉ' (⊍inj₂ _ , _ , _  , _ , (_ , ()) ,    _) 
  
  lem₁₀ : ∀ q wᵉ n q' wᵉ'
          → (⊍inj₂ q , wᵉ) ⊢ᵏ n ─ (⊍inj₂ q' , wᵉ')
          → (q , wᵉ) ⊢ᵏₑ₂ n ─ (q' , wᵉ')
  lem₁₀ q wᵉ zero    .q  .wᵉ  (refl , refl) = refl , refl
  lem₁₀ q wᵉ (suc n)  q'  wᵉ' (init    , _ , _  , _    , (_ , ()) ,    _)
  lem₁₀ q wᵉ (suc n)  q'  wᵉ' (⊍inj₁ p , _ , _  , _    , (_ , ()) ,    _)
  lem₁₀ q wᵉ (suc n)  q'  wᵉ' (⊍inj₂ p , a , uᵉ , prf₁ , prf₂     , prf₃)
    = p , a , uᵉ , prf₁ , prf₂ , lem₁₀ p uᵉ n q' wᵉ' prf₃
  
  lem₉ : ∀ {wᵉ q}
         → (q₀ , wᵉ) ⊢* (⊍inj₂ q , [])
         → Σ[ uᵉ ∈ Σᵉ* ] ( (q₀₂ , uᵉ) ⊢*ₑ₂ (q , []) × toΣ* wᵉ ≡ toΣ* uᵉ )
  lem₉ {.(E ∷  uᵉ)} {q} (suc n , init , E , uᵉ  , refl , (refl , snd₁) , snd) = lem₉ (n , snd)
  lem₉ {.(E ∷  uᵉ)} {q} (suc n , ⊍inj₁ p , E , uᵉ  , refl , (refl , snd₁) , prf) =  ⊥-elim (lem₁₁ p uᵉ n q [] prf)
  lem₉ {.(E ∷ uᵉ)} {q} (suc n , ⊍inj₂ p , E , uᵉ , refl , fst , prf) with Q₂? p q₀₂
  lem₉ {.(E ∷ uᵉ)} {q} (suc n , ⊍inj₂ .(_) , E , uᵉ , refl , fst , prf) | .true because ofʸ refl = uᵉ , ((n , lem₁₀ q₀₂ uᵉ n q [] prf)) , refl
  
  lem₈ : ∀ a wᵉ q
         → ¬ (q₀ , α a ∷ wᵉ) ⊢* (⊍inj₂ q , [])
  lem₈ a wᵉ q (zero  , () , _)
  lem₈ a wᵉ q (suc n , p  , .(α a) , .wᵉ , refl , (refl , ()) , gg)
  
  lem₇ : ∀ q
         → ¬ (q₀ , []) ⊢* (⊍inj₂ q , [])
  lem₇ q (zero  , ()  , _)
  lem₇ q (suc n , p , a , uᵉ , () , _ , prf₂)
  
  lem₆ : ∀ q wᵉ n q' wᵉ'
         → ¬ (⊍inj₂ q , wᵉ) ⊢ᵏ n ─ (⊍inj₁ q' , wᵉ')
  lem₆ q wᵉ zero    q' .wᵉ  (() , refl)
  lem₆ q wᵉ (suc n) q'  wᵉ' (init    , _ , _  , _ , (_ , ()) ,    _)
  lem₆ q wᵉ (suc n) q'  wᵉ' (⊍inj₁ _ , _ , _  , _ , (_ , ()) ,    _) 
  lem₆ q wᵉ (suc n) q'  wᵉ' (⊍inj₂ p , _ , uᵉ , _ , _        , prf₃)
    = lem₆ p uᵉ n q' wᵉ' prf₃
  
  lem₅ : ∀ q wᵉ n q' wᵉ'
         → (⊍inj₁ q , wᵉ) ⊢ᵏ n ─ (⊍inj₁ q' , wᵉ')
         → (q , wᵉ) ⊢ᵏₑ₁ n ─ (q' , wᵉ')
  lem₅ q wᵉ zero    .q  .wᵉ  (refl , refl) = refl , refl
  lem₅ q wᵉ (suc n)  q'  wᵉ' (init    , _ , _  , _    , (_ , ()) ,    _)
  lem₅ q wᵉ (suc n)  q'  wᵉ' (⊍inj₁ p , a , uᵉ , prf₁ , prf₂     , prf₃)
    = p , a , uᵉ , prf₁ , prf₂ , lem₅ p uᵉ n q' wᵉ' prf₃
  lem₅ q wᵉ (suc n)  q'  wᵉ' (⊍inj₂ p , _ , _  , _    , (_ , ()) ,    _)
  
  lem₄ : ∀ {wᵉ q}
         → (q₀ , wᵉ) ⊢* (⊍inj₁ q , [])
         → Σ[ uᵉ ∈ Σᵉ* ] ( (q₀₁ , uᵉ) ⊢*ₑ₁ (q , []) × toΣ* wᵉ ≡ toΣ* uᵉ )
  lem₄ {.(E ∷ uᵉ)} {q} (suc n , init , E ,  uᵉ , refl , (refl , snd₁) , prf₂) =  lem₄ {uᵉ} {q} (n , prf₂)
  lem₄ {.(E ∷ uᵉ)} {q} (suc n , ⊍inj₁ p , E ,  uᵉ , refl , (refl , snd₁) , prf) with Q₁? p q₀₁
  lem₄ {.(E ∷ uᵉ)} {q} (suc n , ⊍inj₁ .(_) , E , uᵉ , refl , (refl , snd₁) , prf) | .true because ofʸ refl = uᵉ , (n , lem₅ q₀₁ uᵉ n q [] prf) , refl
  lem₄ {.(E ∷ uᵉ)} {q} (suc n , ⊍inj₂ p , E , uᵉ   , refl , (refl , snd₁) , prf) =  ⊥-elim (lem₆ p uᵉ n q [] prf)
  
  lem₃ : ∀ a wᵉ q
         → ¬ (q₀ , α a ∷ wᵉ) ⊢* (⊍inj₁ q , [])
  lem₃ a wᵉ q (zero  , () , _)
  lem₃ a wᵉ q (suc n , p  , .(α a) , .wᵉ , refl , (refl , ()) , gg)
  
  lem₂ : ∀ q
         → ¬ (q₀ , []) ⊢* (⊍inj₁ q , [])
  lem₂ q (zero  , ()  , _)
  lem₂ q (suc n , p , a , uᵉ , () , _ , prf₂)
  
  lem₁ : ∀ w
         → w ∈ Lᵉᴺ nfa
         → w ∈ Lᵉᴺ nfa₁ ⊎ w ∈ Lᵉᴺ nfa₂
  lem₁  w  (_  , _    , init    , ()   ,   _)
  lem₁ .[] ([]       , refl , ⊍inj₁ q , q∈F₁ , prf) = ⊥-elim (lem₂ q prf)
  lem₁  w  (α a ∷ wᵉ , w≡wᵉ , ⊍inj₁ q , q∈F₁ , prf) = ⊥-elim (lem₃ a wᵉ q prf)
  lem₁  w  (E   ∷ wᵉ , w≡wᵉ , ⊍inj₁ q , q∈F₁ , prf) with lem₄ {E ∷ wᵉ} {q} prf
  lem₁  w  (E   ∷ wᵉ , w≡wᵉ , ⊍inj₁ q , q∈F₁ , prf) | uᵉ , prf₁ , w≡u = inj₁ (uᵉ , trans w≡wᵉ w≡u , q , q∈F₁ , prf₁)
  lem₁  w  ([]       , w≡wᵉ , ⊍inj₂ q , q∈F₂ , prf) = ⊥-elim (lem₇ q prf)
  lem₁  w  (α a ∷ wᵉ , w≡wᵉ , ⊍inj₂ q , q∈F₂ , prf) = ⊥-elim (lem₈ a wᵉ q prf)
  lem₁  w  (E   ∷ wᵉ , w≡wᵉ , ⊍inj₂ q , q∈F₂ , prf) with lem₉ {E ∷ wᵉ} {q} prf
  lem₁  w  (E   ∷ wᵉ , w≡wᵉ , ⊍inj₂ q , q∈F₂ , prf) | uᵉ , prf₁ , w≡u = inj₂ (uᵉ , trans w≡wᵉ w≡u , q , q∈F₂ , prf₁)
        
