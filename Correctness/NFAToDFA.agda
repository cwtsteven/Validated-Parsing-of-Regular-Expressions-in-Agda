{-
  This module contains the following proofs:
    ∀nfa∈NFA. L(nfa) ⊆ L(powerset-construction dfa)
    ∀nfa∈NFA. L(nfa) ⊇ L(powerset-construction dfa)

  Steven Cheung 2015.
  Version 10-12-2015
-}
open import Util
module Correctness.NFAToDFA (Σ : Set)(dec : DecEq Σ) where

open import Data.List hiding (any)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open Deprecated-inspect-on-steroids renaming (inspect to inspect')
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Vec renaming (_∈_ to _∈ⱽ_)

open import Subset renaming (Ø to ø)
open import Subset.DecidableSubset renaming (Ø to øᵈ ; _∈_ to _∈ᵈ_ ; _∈?_ to _∈ᵈ?_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_)
open import Subset.VectorRep
open import Language Σ dec
open import RegularExpression Σ dec 
open import Automata Σ dec
open import Translation Σ dec
open import State

module base (nfa : NFA) where
  dfa : DFA
  dfa = powerset-construction nfa

  open NFA nfa renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; ∣Q∣-1 to ∣Q₁∣-1 ; It to It₁ ; unique to unique₁) 
  open NFA-Operations nfa renaming (_⊢_ to _⊢₁_ ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_)
  open DFA dfa
  open DFA-Operations dfa
  
  open Vec-Rep {Q₁} {∣Q₁∣-1} Q₁? It₁ ∀q∈It unique₁
  
  mutual
    lem₈ : ∀ q a u m q'
           → Dec (any (λ p → p ∈ᵈ δ₁ q a × (p , u) ⊢ᵏ₁ m ─ (q' , [])) It₁)
    lem₈ q a u m q' = helper {suc ∣Q₁∣-1} It₁
      where
        helper : {n : ℕ}(ps : Vec Q₁ n) → Dec (any (λ p → p ∈ᵈ δ₁ q a × (p , u) ⊢ᵏ₁ m ─ (q' , [])) ps)
        helper []       = no (λ z → z)
        helper (p ∷ ps) with p ∈ᵈ? δ₁ q a | lem₆ p u m q'
        helper (p ∷ ps) | true  | yes prf = yes (inj₁ (refl , prf))
        helper (p ∷ ps) | true  | no  prf with helper ps
        helper (p ∷ ps) | true  | no  prf | yes anyps = yes (inj₂ anyps)
        helper (p ∷ ps) | true  | no  prf | no ¬anyps = no  ¬any
          where
            ¬any : ¬ (true ≡ true × (p , u) ⊢ᵏ₁ m ─ (q' , []) ⊎ any (λ p → p ∈ᵈ δ₁ q a × (p , u) ⊢ᵏ₁ m ─ (q' , [])) ps)
            ¬any (inj₁ (refl , prf₃)) = prf prf₃
            ¬any (inj₂ anyps) = ¬anyps anyps
        helper (p ∷ ps) | false | prf     with helper ps
        helper (p ∷ ps) | false | prf     | yes anyps = yes (inj₂ anyps)
        helper (p ∷ ps) | false | prf     | no ¬anyps = no  ¬any
          where
            ¬any : ¬ (false ≡ true × (p , u) ⊢ᵏ₁ m ─ (q' , []) ⊎ any (λ p → p ∈ᵈ δ₁ q a × (p , u) ⊢ᵏ₁ m ─ (q' , [])) ps)
            ¬any (inj₁ (() , _))
            ¬any (inj₂ anyps) = ¬anyps anyps
  
    lem₇ : ∀ q a u n q'
           → Dec (Σ[ p ∈ Q₁ ] ( p ∈ᵈ δ₁ q a × (p , u) ⊢ᵏ₁ n ─ (q' , []) ))
    lem₇ q a u n q' with lem₈ q a u n q'
    lem₇ q a u n q' | yes prf = yes (Vec-any-lem₂ (λ p → p ∈ᵈ δ₁ q a × (p , u) ⊢ᵏ₁ n ─ (q' , [])) prf)
    lem₇ q a u n q' | no  prf = no  (Vec-any-lem₄ (λ p → p ∈ᵈ δ₁ q a × (p , u) ⊢ᵏ₁ n ─ (q' , [])) prf)
  
    lem₆ : ∀ q w n q'
           → Dec ( (q , w) ⊢ᵏ₁ n ─ (q' , []) )
    lem₆ q w zero q'    with Q₁? q q' | DecEq-Σ* w []
    lem₆ q .[] zero .q  | yes refl | yes refl = yes (refl , refl)
    lem₆ q w zero .q    | yes refl | no  w≢[] = no  prf
      where
        prf : ¬ (q , w) ⊢ᵏ₁ zero ─ (q , [])
        prf (refl , w≡[]) = ⊥-elim (w≢[] w≡[])
    lem₆ q w zero q'    | no  q≢q' | _        = no  prf
      where
        prf : ¬ (q , w) ⊢ᵏ₁ zero ─ (q' , [])
        prf (q≡q' , _) = ⊥-elim (q≢q' q≡q')
    lem₆ q []      (suc n) q' = no prf
      where
        prf : ¬ (q , []) ⊢ᵏ₁ suc n ─ (q' , [])
        prf (p , a , u , () , _ , _)
    lem₆ q (a ∷ u) (suc n) q' with lem₇ q a u n q'
    lem₆ q (a ∷ u) (suc n) q' | yes (p , p∈δqa , prf₁) = yes (p , a , u , refl , (refl , p∈δqa) , prf₁)
    lem₆ q (a ∷ u) (suc n) q' | no  ¬∃p                = no  prf
      where
        prf : ¬ (q , (a ∷ u)) ⊢ᵏ₁ suc n ─ (q' , [])
        prf (p , .a , .u , refl , (refl , p∈δqa) , prf₁) = ¬∃p (p , p∈δqa , prf₁)
  
  
  lem₅ : ∀ qs w m q'
         → Dec (any (λ q → q ∈ᵈ qs × (q , w) ⊢ᵏ₁ m ─ (q' , [])) It₁)
  lem₅ qs w m q' = helper {suc ∣Q₁∣-1} It₁
    where
      helper : {n : ℕ}(ps : Vec Q₁ n) → Dec (any (λ q → q ∈ᵈ qs × (q , w) ⊢ᵏ₁ m ─ (q' , [])) ps)
      helper []       = no (λ z → z)
      helper (p ∷ ps) with p ∈ᵈ? qs | lem₆ p w m q'
      helper (p ∷ ps) | true  | yes prf = yes (inj₁ (refl , prf))
      helper (p ∷ ps) | true  | no  prf with helper ps
      helper (p ∷ ps) | true  | no  prf | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | true  | no  prf | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (true ≡ true × (p , w) ⊢ᵏ₁ m ─ (q' , []) ⊎ any (λ q → q ∈ᵈ qs × (q , w) ⊢ᵏ₁ m ─ (q' , [])) ps)
          ¬any (inj₁ (refl , prf₃)) = prf prf₃
          ¬any (inj₂ anyps) = ¬anyps anyps
      helper (p ∷ ps) | false | prf     with helper ps
      helper (p ∷ ps) | false | prf     | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | false | prf     | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (false ≡ true × (p , w) ⊢ᵏ₁ m ─ (q' , []) ⊎ any (λ q → q ∈ᵈ qs × (q , w) ⊢ᵏ₁ m ─ (q' , [])) ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ anyps) = ¬anyps anyps


  lem₃ : ∀ qs w n q'
         → Dec ( Σ[ q ∈ Q₁ ] ( q ∈ᵈ qs × (q , w) ⊢ᵏ₁ n ─ (q' , []) ))
  lem₃ qs w n q' with lem₅ qs w n q'
  lem₃ qs w n q' | yes prf = yes (Vec-any-lem₂ (λ q → q ∈ᵈ qs × (q , w) ⊢ᵏ₁ n ─ (q' , [])) prf)
  lem₃ qs w n q' | no  prf = no  (Vec-any-lem₄ (λ q → q ∈ᵈ qs × (q , w) ⊢ᵏ₁ n ─ (q' , [])) prf)
  
  
  lem₄ : (qs : Q)(w : Σ*)(n : ℕ)(q' : Q₁)
         → Bool
  lem₄ qs w n q' with lem₃ qs w n q'
  ... | yes _ = true
  ... | no  _ = false
  
  lem₉ : ∀ qs w m q'
         → lem₄ qs w m q' ≡ true
         → Σ[ q ∈ Q₁ ] ( q ∈ᵈ qs × (q , w) ⊢ᵏ₁ m ─ (q' , []) )
  lem₉ qs w m q' prf with lem₃ qs w m q'
  lem₉ qs w m q' prf | yes prf₁ = prf₁
  lem₉ qs w m q'  () | no  _
  
  lem₁₀ : ∀ qs a p
          → p ∈ᵈ δ qs a
          → Σ[ q ∈ Q₁ ] ( q ∈ᵈ qs × p ∈ᵈ δ₁ q a )
  lem₁₀ qs a p p∈δqsa with Dec-⊢ qs a p
  lem₁₀ qs a p p∈δqsa | yes prf = prf
  lem₁₀ qs a p     () | no  _
  
  lem₁₁ : ∀ qs q a p
          → q ∈ᵈ qs
          → p ∈ᵈ δ₁ q a
          → p ∈ᵈ δ qs a
  lem₁₁ qs q a p q∈qs p∈δqa with p ∈ᵈ? δ qs a | inspect (δ qs a) p
  lem₁₁ qs q a p q∈qs p∈δqa | true  | [ eq ] = refl
  lem₁₁ qs q a p q∈qs p∈δqa | false | [ eq ] with Dec-⊢ qs a p
  lem₁₁ qs q a p q∈qs p∈δqa | false | [ () ] | yes _
  lem₁₁ qs q a p q∈qs p∈δqa | false | [ eq ] | no ¬∃q = ⊥-elim (¬∃q (q , q∈qs , p∈δqa))
  
  
  
module Lᴺ⊆Lᴰ (nfa : NFA) where
  open base nfa
 
  open NFA nfa renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; ∣Q∣-1 to ∣Q₁∣-1 ; It to It₁ ; unique to unique₁) 
  open NFA-Operations nfa renaming (_⊢_ to _⊢₁_ ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_)
  open DFA dfa 
  open DFA-Operations dfa 

  lem₂ : ∀ qs q w n q'
         → q ∈ᵈ qs
         → (q , w) ⊢ᵏ₁ n ─ (q' , [])
         → Σ[ qs' ∈ Q ] ( q' ∈ᵈ qs' × (qs , w) ⊢ᵏ n ─ (qs' , []) )
  lem₂ qs q .[] zero   .q  q∈qs (refl , refl) = qs , q∈qs , (≋-refl , refl)
  lem₂ qs q ._  (suc n) q' q∈qs (p , a , u , refl , (refl , p∈δqa) , prf) with lem₂ (δ qs a) p u n q' (lem₁₁ qs q a p q∈qs p∈δqa) prf
  lem₂ qs q ._  (suc n) q' q∈qs (p , a , u , refl , (refl , p∈δqa) , prf) | qs' , q'∈qs' , prf₁
    = qs' , q'∈qs' , ((δ qs a) , a , u , refl , (refl , ≋-refl) , prf₁)
  
  lem₁ : ∀ w
         → w ∈ Lᴺ nfa
         → w ∈ Lᴰ dfa
  lem₁ w (q , q∈F , n , prf) with lem₂ q₀ q₀₁ w n q (⟦a⟧-lem₁ Q₁? q₀₁) prf
  lem₁ w (q , q∈F , n , prf) | qs , q∈qs , prf₁ with qs ∈ᵈ? F | inspect' F qs
  lem₁ w (q , q∈F , n , prf) | qs , q∈qs , prf₁ | true  | [ qs∈F ] = qs , qs∈F , n , prf₁
  lem₁ w (q , q∈F , n , prf) | qs , q∈qs , prf₁ | false | [ qs∉F ] with Dec-qs∈F qs
  lem₁ w (q , q∈F , n , prf) | qs , q∈qs , prf₁ | false | [   () ] | yes _
  lem₁ w (q , q∈F , n , prf) | qs , q∈qs , prf₁ | false | [ qs∉F ] | no  ¬∃q
    = ⊥-elim (¬∃q (q , q∈qs , q∈F))
  
  
  
Lᴺ⊆Lᴰ : ∀ nfa → Lᴺ nfa ⊆ Lᴰ (powerset-construction nfa)
Lᴺ⊆Lᴰ = Lᴺ⊆Lᴰ.lem₁
  
  
  
  
module Lᴺ⊇Lᴰ (nfa : NFA) where
  open base nfa
 
  open NFA nfa renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; ∣Q∣-1 to ∣Q₁∣-1 ; It to It₁) 
  open NFA-Operations nfa renaming (_⊢_ to _⊢₁_ ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_)
  open DFA dfa
  open DFA-Operations dfa
  
  lem₂'' : ∀ qs w n qs'
           → (qs , w) ⊢ᵏ n ─ (qs' , [])
           → qs' ⊇ᵈ (λ q' → lem₄ qs w n q')
  lem₂'' qs .[] zero    qs' (qs≈qs' , refl) q' q'∈lem₄ with lem₃ qs [] zero q'
  lem₂'' qs .[] zero    qs' (qs≈qs' , refl) q' q'∈lem₄ | yes (.q' , q'∈qs , (refl , refl)) = proj₁ qs≈qs' q' q'∈qs
  lem₂'' qs .[] zero    qs' (qs≈qs' , refl) q'      () | no  _
  lem₂'' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈lem₄ with lem₄ ps u n q' | inspect' (lem₄ ps u n) q'
  lem₂'' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈lem₄ | true  | [ eq ] = lem₂'' ps u n qs' prf₁ q' eq
  lem₂'' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈lem₄ | false | [ eq ] with lem₃ ps u n q'
  lem₂'' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈lem₄ | false | [ () ] | yes _
  lem₂'' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈lem₄ | false | [ eq ] | no  ¬∃q with lem₃ qs (a ∷ u) (suc n) q'
  lem₂'' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈lem₄ | false | [ eq ] | no  ¬∃q | yes (q , q∈qs , (p , .a , .u , refl , (refl , p∈δqa) , prf₂))
    = ⊥-elim (¬∃q (p , proj₂ ps≈δqsa p (lem₁₁ qs q a p q∈qs p∈δqa) , prf₂))
  lem₂'' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q'      () | false | [ eq ] | no  ¬∃q | no  _
  
  
  lem₂' : ∀ qs w n qs'
          → (qs , w) ⊢ᵏ n ─ (qs' , [])
          → qs' ⊆ᵈ (λ q' → lem₄ qs w n q')
  lem₂' qs .[] zero    qs' (qs≈qs' , refl) q' q'∈qs' with lem₄ qs [] zero q' | inspect (lem₄ qs [] zero) q'
  lem₂' qs .[] zero    qs' (qs≈qs' , refl) q' q'∈qs' | true  | [ eq ] = refl
  lem₂' qs .[] zero    qs' (qs≈qs' , refl) q' q'∈qs' | false | [ eq ] with lem₃ qs [] zero q'
  lem₂' qs .[] zero    qs' (qs≈qs' , refl) q' q'∈qs' | false | [ () ] | yes _
  lem₂' qs .[] zero    qs' (qs≈qs' , refl) q' q'∈qs' | false | [ eq ] | no  ¬∃q = ⊥-elim (¬∃q (q' , proj₂ qs≈qs' q' q'∈qs' , (refl , refl)))
  lem₂' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈qs' with lem₄ qs (a ∷ u) (suc n) q' | inspect' (lem₄ qs (a ∷ u) (suc n)) q'
  lem₂' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈qs' | true  | [ eq ] = refl
  lem₂' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈qs' | false | [ eq ] with lem₃ qs (a ∷ u) (suc n) q'
  lem₂' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈qs' | false | [ () ] | yes _
  lem₂' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈qs' | false | [ eq ] | no ¬∃q with lem₉ ps u n q' (lem₂' ps u n qs' prf₁ q' (q'∈qs'))
  lem₂' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈qs' | false | [ eq ] | no ¬∃q | p , p∈ps , prf₂ with lem₁₀ qs a p (proj₁ ps≈δqsa p p∈ps)
  lem₂' qs ._  (suc n) qs' (ps , a , u , refl , (refl , ps≈δqsa) , prf₁) q' q'∈qs' | false | [ eq ] | no ¬∃q | p , p∈ps , prf₂ | q , q∈qs , p∈δqa
    = ⊥-elim (¬∃q (q , q∈qs , (p , a , u , refl , (refl , p∈δqa) , prf₂)))
  
  
  lem₂ : ∀ qs w n qs'
         → (qs , w) ⊢ᵏ n ─ (qs' , [])
         → qs' ≈ᵈ (λ q' → lem₄ qs w n q')
  lem₂ qs w n qs' prf = lem₂' qs w n qs' prf , lem₂'' qs w n qs' prf
  
  
  lem₁ : ∀ w
         → w ∈ Lᴰ dfa
         → w ∈ Lᴺ nfa
  lem₁ w (qs , qs∈F , n , prf) with Dec-qs∈F qs
  lem₁ w (qs , qs∈F , n , prf) | yes (q , q∈qs , q∈F) with lem₄ q₀ w n q | inspect' (lem₄ q₀ w n) q
  lem₁ w (qs , qs∈F , n , prf) | yes (q , q∈qs , q∈F) | true  | [ eq ] with lem₃ q₀ w n q
  lem₁ w (qs , qs∈F , n , prf) | yes (q , q∈qs , q∈F) | true  | [ eq ] | yes (p    , p∈q₀ , prf₁) with Q₁? q₀₁ p
  lem₁ w (qs , qs∈F , n , prf) | yes (q , q∈qs , q∈F) | true  | [ eq ] | yes (.q₀₁ , p∈q₀  , prf₁) | yes refl = q , q∈F , n , prf₁
  lem₁ w (qs , qs∈F , n , prf) | yes (q , q∈qs , q∈F) | true  | [ eq ] | yes (p    ,   ()  , prf₁) | no  _
  lem₁ w (qs , qs∈F , n , prf) | yes (q , q∈qs , q∈F) | true  | [ () ] | no  _
  lem₁ w (qs , qs∈F , n , prf) | yes (q , q∈qs , q∈F) | false | [ eq ]
    = let (qs⊆lem₄ , lem₄⊇qs) = lem₂ q₀ w n qs prf in ⊥-elim (Bool-lem₉ eq (qs⊆lem₄ q q∈qs))
  lem₁ w (qs ,   () , n , prf) | no  _
  
  
Lᴺ⊇Lᴰ : ∀ nfa → Lᴺ nfa ⊇ Lᴰ (powerset-construction nfa)
Lᴺ⊇Lᴰ = Lᴺ⊇Lᴰ.lem₁
