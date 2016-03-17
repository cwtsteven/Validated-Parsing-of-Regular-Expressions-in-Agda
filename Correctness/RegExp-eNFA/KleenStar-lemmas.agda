{-
  This module contains the following proofs:

  Steven Cheung
  Version 10-01-2016
-}
open import Util
open import RegularExpression
module Correctness.RegExp-eNFA.KleenStar-lemmas (Σ : Set)(dec : DecEq Σ)(e : RegularExpression.RegExp Σ dec) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_)
open import Language Σ dec
open import eNFA Σ dec
open import Translation.RegExp-eNFA Σ dec
open import State

nfa : ε-NFA
nfa = regexToε-NFA (e *)

nfa₁ : ε-NFA
nfa₁ = regexToε-NFA e

open ε-NFA nfa
open ε-NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
open ε-NFA-Operations nfa
open ε-NFA-Operations nfa₁
  renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_)

¬lem₂ : ∀ q wᵉ n vᵉ
        → ¬ (inj q , wᵉ) ⊢ᵏ n ─ (init , vᵉ)
¬lem₂ q wᵉ zero    vᵉ (() , _)
¬lem₂ q wᵉ (suc n) vᵉ (init  , α _ , uᵉ , _ , (refl ,   ()) , prf₂)
¬lem₂ q wᵉ (suc n) vᵉ (init  , E   , uᵉ , _ , (refl ,   ()) , prf₂)
¬lem₂ q wᵉ (suc n) vᵉ (inj p , a   , uᵉ , _ , (refl , prf₁) , prf₂)
  = ¬lem₂ p uᵉ n vᵉ prf₂

lem₄₀ : ∀ wᵉ n vᵉ
        → (init , wᵉ) ⊢ᵏ n ─ (init , vᵉ)
        → toΣ* wᵉ ≡ toΣ* vᵉ
lem₄₀ wᵉ zero    .wᵉ (refl , refl) = refl
lem₄₀ ._ (suc n)  vᵉ (init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂)
lem₄₀ ._ (suc n)  vᵉ (init  , E   , uᵉ , refl , (refl , prf₁) , prf₂) = lem₄₀ uᵉ n vᵉ prf₂
lem₄₀ ._ (suc n)  vᵉ (inj p , α _ , uᵉ , refl , (refl ,   ()) , prf₂)
lem₄₀ ._ (suc n)  vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) = ⊥-elim (¬lem₂ p uᵉ n vᵉ prf₂)


¬lem₁ : ∀ wᵉ n vᵉ
        → toΣ* wᵉ ≢ toΣ* vᵉ
        → ¬ (init , wᵉ) ⊢ᵏ n ─ (init , vᵉ)
¬lem₁ ._ zero     vᵉ w≢v (refl , refl) = ⊥-elim (w≢v refl)
¬lem₁ ._ (suc n)  vᵉ w≢v ( init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂)
¬lem₁ ._ (suc n)  vᵉ w≢v ( init  , E   , uᵉ , refl , (refl , prf₁) , prf₂)
  = ¬lem₁ uᵉ n vᵉ w≢v prf₂
¬lem₁ ._ (suc n)  vᵉ w≢v ( inj p , a   , uᵉ , refl , (refl , prf₁) , prf₂)
  = ¬lem₂ p uᵉ n vᵉ prf₂


module Lᴿ⊆Lᴺ where
  lem₄ : ∀ wᵉ n q₁
         → (q₀ , wᵉ)  ⊢ᵏ suc n ─ (inj q₁ , [])
         → Σ[ n₁ ∈ ℕ ] Σ[ uᵉ ∈ Σᵉ* ] (toΣ* wᵉ ≡ toΣ* uᵉ × (inj q₀₁ , uᵉ) ⊢ᵏ n₁ ─ (inj q₁ , []))
  lem₄ ._ zero    q₁  (inj .q₁  , α _ , .[] , refl , (refl ,   ()) , (refl , refl))
  lem₄ ._ zero    q₁  (inj .q₁  , E   , .[] , refl , (refl , prf₁) , (refl , refl)) with Q₁? q₁ q₀₁
  lem₄ ._ zero   .q₀₁ (inj .q₀₁ , E   , .[] , refl , (refl , prf₁) , (refl , refl)) | yes refl  = zero , [] , (refl , (refl , refl))
  lem₄ ._ zero    q₁  (inj .q₁  , E   , .[] , refl , (refl ,   ()) , (refl , refl)) | no  p≢q₀₁
  lem₄ ._ (suc n) q₁  (init     , α _ ,  uᵉ , refl , (refl ,   ()) , prf₂)
  lem₄ ._ (suc n) q₁  (init     , E   ,  uᵉ , refl , (refl , prf₁) , prf₂) = lem₄ uᵉ n q₁ prf₂
  lem₄ ._ (suc n) q₁  (inj  p   , α _ ,  uᵉ , refl , (refl ,   ()) , prf₂)
  lem₄ ._ (suc n) q₁  (inj  p   , E   ,  uᵉ , refl , (refl , prf₁) , prf₂) with Q₁? p q₀₁
  lem₄ ._ (suc n) q₁  (inj .q₀₁ , E   ,  uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  = suc n , uᵉ , refl , prf₂
  lem₄ ._ (suc n) q₁  (inj  p   , E   ,  uᵉ , refl , (refl ,   ()) , prf₂) | no  p≢q₀₁


  lem₃ : ∀ q wᵉ uᵉ n q' vᵉ
         → wᵉ ≡ uᵉ ++ vᵉ
         → (q , uᵉ) ⊢ᵏₑ₁ n ─ (q' , [])
         → (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , vᵉ)
  lem₃ q wᵉ .[] zero    .q  vᵉ w≡uv (refl , refl) = refl , w≡uv
  lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , α a , u₁ , refl , (refl , prf₁) , prf₂)
    = inj p , α a , u₁ ++ vᵉ , w≡uv , (refl , prf₁) , lem₃ p (u₁ ++ vᵉ) u₁ n q' vᵉ refl prf₂
  lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) with inj p ∈ᵈ? δ (inj q) E | inspect (δ (inj q) E) (inj p)
  lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | true  | [ eq ]
    = inj p , E , u₁ ++ vᵉ , w≡uv , (refl , eq) , lem₃ p (u₁ ++ vᵉ) u₁ n q' vᵉ refl prf₂
  lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | false | [ eq ] with p ∈ᵈ? δ₁ q E | inspect (δ₁ q E) p
  lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | false | [ () ] | true  | [ eq₁ ]
  lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl ,   ()) , prf₂) | false | [ eq ] | false | [ eq₁ ]
  
  
  lem₂ : ∀ wᵉ uᵉ n q vᵉ
         → wᵉ ≡ uᵉ ++ vᵉ
         → (q₀₁ , uᵉ) ⊢ᵏₑ₁ n ─ (q , [])
         → (init , E ∷ wᵉ) ⊢ᵏ suc n ─ (inj q , vᵉ)
  lem₂ wᵉ uᵉ n q vᵉ w≡uv prf with inj q₀₁ ∈ᵈ? δ q₀ E | inspect (δ q₀ E) (inj q₀₁)
  lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | true  | [ eq ] = inj q₀₁ , E , wᵉ , refl , (refl , eq) , lem₃ q₀₁ wᵉ uᵉ n q vᵉ w≡uv prf
  lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | false | [ eq ] with Q₁? q₀₁ q₀₁
  lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | false | [ () ] | yes refl
  lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | false | [ eq ] | no  q₀₁≢q₀₁ = ⊥-elim (q₀₁≢q₀₁ refl)
  
  
module Lᴿ⊇Lᴺ where
  find-uᵉ : ∀ q wᵉ n q' vᵉ
            → (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , vᵉ)
            → Σᵉ*
  find-uᵉ q  wᵉ zero    .q  .wᵉ (refl , refl) = []
  find-uᵉ q ._  (suc n)  q'  vᵉ (init  , α _ , uᵉ , refl , (refl , ()) , prf₂)
  find-uᵉ q ._  (suc n)  q'  vᵉ (init  , E   , uᵉ , refl , (refl , ()) , prf₂)
  find-uᵉ q ._  (suc n)  q'  vᵉ (inj p , a   , uᵉ , refl , (refl ,  _) , prf₂)
    = a ∷ find-uᵉ p uᵉ n q' vᵉ prf₂
  
  
  NoLoop : ∀ q wᵉ n q' wᵉ'
           → (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , wᵉ')
           → Set
  NoLoop q ._ zero    .q  wᵉ' (refl , refl) = ⊤
  NoLoop q ._ (suc n)  q' wᵉ' (init     , α _ , _  , refl , (refl ,   ()) , prf₂)
  NoLoop q ._ (suc n)  q' wᵉ' (init     , E   , _  , refl , (refl ,   ()) , prf₂)
  NoLoop q ._ (suc n)  q' wᵉ' (inj  p   , α _ , uᵉ , refl , (refl , prf₁) , prf₂)
    = NoLoop p uᵉ n q' wᵉ' prf₂
  NoLoop q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂)
    = (p ≢ q₀₁ ⊎ q ∉ᵈ F₁) × NoLoop p uᵉ n q' wᵉ' prf₂
  
  
  HasLoop : ∀ q wᵉ n q' wᵉ'
            → (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , wᵉ')
            → Set
  HasLoop q wᵉ n q' wᵉ' prf
    = Σ[ n₁ ∈ ℕ ] Σ[ m₁ ∈ ℕ ] Σ[ p ∈ Q₁ ] Σ[ vᵉ ∈ Σᵉ* ] Σ[ prf₁ ∈ (inj q , wᵉ) ⊢ᵏ n₁ ─ (inj p , E ∷ vᵉ) ]
      ( NoLoop q wᵉ n₁ p (E ∷ vᵉ) prf₁
        × p ∈ᵈ F₁
        × (inj q₀₁ , vᵉ) ⊢ᵏ m₁ ─ (inj q' , wᵉ')
        × wᵉ ≡ find-uᵉ q wᵉ n₁ p (E ∷ vᵉ) prf₁ ++ (E ∷ vᵉ) × m₁ <′ n )
  

  find-uᵉ-lem₁ : ∀ q wᵉ n q'
                 → (prf : (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , []))
                 → NoLoop q wᵉ n q' [] prf
                 → wᵉ ≡ find-uᵉ q wᵉ n q' [] prf
  find-uᵉ-lem₁ q .[] zero    .q  (refl  , refl) tt = refl
  find-uᵉ-lem₁ q ._  (suc n)  q' (init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂) prf₃
  find-uᵉ-lem₁ q ._  (suc n)  q' (init  , E   , uᵉ , refl , (refl ,   ()) , prf₂) prf₃
  find-uᵉ-lem₁ q ._  (suc n)  q' (inj p , α a , uᵉ , refl , (refl , prf₁) , prf₂) prf₃
    = cong (λ uᵉ → α a ∷ uᵉ) (find-uᵉ-lem₁ p uᵉ n q' prf₂ prf₃)
  find-uᵉ-lem₁ q ._  (suc n)  q' (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (_ , prf₃)
    = cong (λ uᵉ → E   ∷ uᵉ) (find-uᵉ-lem₁ p uᵉ n q' prf₂ prf₃)
    
  
  lem₆ : ∀ q wᵉ n q' vᵉ
         → (prf : (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , vᵉ))
         → NoLoop q wᵉ n q' vᵉ prf
         → (q , find-uᵉ q wᵉ n q' vᵉ prf) ⊢ᵏₑ₁ n ─ (q' , [])
  lem₆ q .vᵉ zero    .q  vᵉ (refl  , refl) tt = refl , refl
  lem₆ q ._  (suc n)  q' vᵉ (init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂) prf₃
  lem₆ q ._  (suc n)  q' vᵉ (init  , E   , uᵉ , refl , (refl ,   ()) , prf₂) prf₃
  lem₆ q ._  (suc n)  q' vᵉ (inj p , α a , uᵉ , refl , (refl , prf₁) , prf₂) prf₃
    = p , α a , find-uᵉ p uᵉ n q' vᵉ prf₂ , refl , (refl , prf₁) , lem₆ p uᵉ n q' vᵉ prf₂ prf₃
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₁ p≢q₀₁ , prf₃) with Q₁? p q₀₁ | q ∈ᵈ? F₁ | inspect F₁ q | p ∈ᵈ? δ₁ q E | inspect (δ₁ q E) p
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₁ p≢q₀₁ , prf₃) | yes p≡q₀₁ | _     | _      | _     | _
    = ⊥-elim (p≢q₀₁ p≡q₀₁)
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₁ p≢q₀₁ , prf₃) | no  _     | q∈?F₁ | [ eq ] | true  | [ eq₁ ]
    = p , E , find-uᵉ p uᵉ n q' vᵉ prf₂ , refl , (refl , eq₁) , lem₆ p uᵉ n q' vᵉ prf₂ prf₃
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₁ p≢q₀₁ , prf₃) | no  _     | q∈?F₁ | [ eq ] | false | [ eq₁ ]
    = ⊥-elim (Bool-lem₈ {q∈?F₁} prf₁)
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₂ q∉F   , prf₃) with Q₁? p q₀₁ | q ∈ᵈ? F₁ | inspect F₁ q | p ∈ᵈ? δ₁ q E | inspect (δ₁ q E) p
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₂ q∉F   , prf₃) | _         | true  | [ eq ] | _     | _
    = ⊥-elim (q∉F refl)
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₂ q∉F   , prf₃) | _         | false | [ eq ] | true  | [ eq₁ ]
    = p , E , find-uᵉ p uᵉ n q' vᵉ prf₂ , refl , (refl , eq₁) , lem₆ p uᵉ n q' vᵉ prf₂ prf₃
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl ,   ()) , prf₂) (inj₂ q∉F   , prf₃) | _         | false | [ eq ] | false | [ eq₁ ]
    
  
  lem₅ : ∀ q wᵉ n q' wᵉ'
         → (prf : (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , wᵉ'))
         → (NoLoop q wᵉ n q' wᵉ' prf) ⊎ (HasLoop q wᵉ n q' wᵉ' prf)
  lem₅ q ._ zero    .q  wᵉ' (refl  , refl) = inj₁ tt
  lem₅ q ._ (suc n)  q' wᵉ' (init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂)
  lem₅ q ._ (suc n)  q' wᵉ' (init  , E   , uᵉ , refl , (refl ,   ()) , prf₂)
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , α a , uᵉ , refl , (refl , prf₁) , prf₂) with lem₅ p uᵉ n q' wᵉ' prf₂
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , α a , uᵉ , refl , (refl , prf₁) , prf₂) | inj₁ prf₃ = inj₁ prf₃
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , α a , uᵉ , refl , (refl , prf₁) , prf₂) | inj₂ (n₁ , m₁ , p₁ , u₁ , prf₃ , NoLoop-prf₃ , p₁∈F , prf₅ , w≡uv , m₁<n)
    = inj₂ (suc n₁ , m₁ , p₁ , u₁ , (inj p , α a , uᵉ , refl , (refl , prf₁) , prf₃) , NoLoop-prf₃ , p₁∈F , prf₅ , cong (λ u → α a ∷ u) w≡uv , ≤′-step m₁<n)
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) with Q₁? p q₀₁ | q ∈ᵈ? F₁ | inspect F₁ q | p ∈ᵈ? δ₁ q E | inspect (δ₁ q E) p
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | true  | [ eq ] | p∈?δqE | [ eq₁ ] with Q₁? q₀₁ q₀₁
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | true  | [ eq ] | p∈?δqE | [ eq₁ ] | yes refl
    = inj₂ (zero , n , q , uᵉ , (refl , refl) , tt , eq , prf₂ , refl , ≤′-refl)
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | true  | [ eq ] | p∈?δqE | [ eq₁ ] | no  p≢p  = ⊥-elim (p≢p refl)
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | false | [ eq ] | true   | [ eq₁ ] with lem₅ q₀₁ uᵉ n q' wᵉ' prf₂
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | false | [ eq ] | true   | [ eq₁ ] | inj₁ prf₃ = inj₁ (inj₂ (λ ()) , prf₃)
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | false | [ eq ] | true   | [ eq₁ ] | inj₂ (n₁ , m₁ , p₁ , u₁ , prf₃ , NoLoop-prf₃ , q₀₁∈F , prf₅ , w≡uv , m₁<n)
    = inj₂ (suc n₁ , m₁ , p₁ , u₁
            , (inj q₀₁ , E , uᵉ , refl , (refl , Bool-lem₆ (q₀₁ ∈ᵈ? δ₁ q E) (q ∈ᵈ? F₁ ∧ decEqToBool Q₁? q₀₁ q₀₁) eq₁) , prf₃)
            , (inj₂ (∈-lem₂ {Q₁} {q} {F₁} eq) , NoLoop-prf₃)
            , q₀₁∈F , prf₅
            , cong (λ u → E ∷ u) w≡uv
            , ≤′-step m₁<n)
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl ,   ()) , prf₂) | yes refl  | false | [ eq ] | false  | [ eq₁ ]
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) | no  p≢q₀₁ | q∈?F₁ | [ eq ] | true   | [ eq₁ ] with lem₅ p uᵉ n q' wᵉ' prf₂
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) | no  p≢q₀₁ | q∈?F₁ | [ eq ] | true   | [ eq₁ ] | inj₁ prf₃ = inj₁ (inj₁ p≢q₀₁ , prf₃)
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) | no  p≢q₀₁ | q∈?F₁ | [ eq ] | true   | [ eq₁ ] | inj₂ (n₁ , m₁ , p₁ , u₁ , prf₃ , NoLoop-prf₃ , p₁∈F , prf₅ , w≡uv , m₁<n)
    = inj₂ (suc n₁ , m₁ , p₁ , u₁
            , (inj p , E , uᵉ , refl , (refl , Bool-lem₆ (p ∈ᵈ? δ₁ q E) (q ∈ᵈ? F₁ ∧ decEqToBool Q₁? p q₀₁) eq₁) , prf₃)
            , (inj₁ p≢q₀₁ , NoLoop-prf₃)
            , p₁∈F , prf₅
            , cong (λ u → E ∷ u) w≡uv
            , ≤′-step m₁<n)
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) | no  p≢q₀₁ | q∈?F₁ | [ eq ] | false  | [ eq₁ ]
    = ⊥-elim (Bool-lem₈ {q∈?F₁} prf₁)
            
