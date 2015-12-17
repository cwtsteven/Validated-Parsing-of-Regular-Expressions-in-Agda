open import Util
open import RegularExpression
module Correctness.RegExpToe-NFA.Union-lemmas (Σ : Set)(dec : DecEq Σ)(e₁ : RegularExpression.RegExp Σ)(e₂ : RegularExpression.RegExp Σ) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_)
open import Language Σ
open import Automata Σ
open import Translation Σ dec
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
        → (q₀ , w) ⊢* (⊍inj₂ q , w')
 lem₅ q w w' (n , prf) with ⊍inj₂ q₀₂ ∈ᵈ δ q₀ E | inspect (δ q₀ E) (⊍inj₂ q₀₂)
 lem₅ q w w' (n , prf) | true  | [ eq ]
   = suc n , ⊍inj₂ q₀₂ , E , w , inj₂ (refl , refl) , (refl , eq) , lem₆ q₀₂ w n q w' prf
 lem₅ q w w' (n , prf) | false | [ eq ] with Q₂? q₀₂ q₀₂
 lem₅ q w w' (n , prf) | false | [ () ] | yes refl
 lem₅ q w w' (n , prf) | false | [ eq ] | no  q₀₂≢q₀₂ = ⊥-elim (q₀₂≢q₀₂ refl)


 lem₄ : ∀ {w}
        → w ∈ Lᵉᴺ nfa₂
        → w ∈ Lᵉᴺ nfa
 lem₄ {w} (q , q∈F , q₀₂w⊢*q[])
   = ⊍inj₂ q , q∈F , lem₅ q (toΣᵉ* w) [] q₀₂w⊢*q[]


 lem₃ : ∀ q w n q' w'
        → (q , w) ⊢ᵏₑ₁ n ─ (q' , w')
        → (⊍inj₁ q , w) ⊢ᵏ n ─ (⊍inj₁ q' , w')
 lem₃ q w zero   .q .w (refl , refl)
   = refl , refl
 lem₃ q w (suc n) q' w' (p , a , u , prf₁ , prf₂ , prf₃)
   = ⊍inj₁ p , a , u , prf₁ , prf₂ , lem₃ p u n q' w' prf₃


 lem₂ : ∀ q w w'
        → (q₀₁ , w) ⊢*ₑ₁ (q , w')
        → (q₀ , w) ⊢* (⊍inj₁ q , w')
 lem₂ q w w' (n , prf) with ⊍inj₁ q₀₁ ∈ᵈ δ q₀ E | inspect (δ q₀ E) (⊍inj₁ q₀₁)
 lem₂ q w w' (n , prf) | true  | [ eq ]
   = suc n , ⊍inj₁ q₀₁ , E , w , inj₂ (refl , refl) , (refl , eq) , lem₃ q₀₁ w n q w' prf
 lem₂ q w w' (n , prf) | false | [ eq ] with Q₁? q₀₁ q₀₁
 lem₂ q w w' (n , prf) | false | [ () ] | yes refl    
 lem₂ q w w' (n , prf) | false | [ eq ] | no  q₀₁≢q₀₁ = ⊥-elim (q₀₁≢q₀₁ refl)


 lem₁ : ∀ {w}
        → w ∈ Lᵉᴺ nfa₁
        → w ∈ Lᵉᴺ nfa
 lem₁ {w} (q , q∈F , q₀₁w⊢*q[])
   = ⊍inj₁ q , q∈F , lem₂ q (toΣᵉ* w) [] q₀₁w⊢*q[]

module Lᴿ⊇Lᴺ where
 lem₇ : ∀ q w n q' w'
        → ¬ (⊍inj₁ q , w) ⊢ᵏ n ─ (⊍inj₂ q' , w')
 lem₇ q w zero    q' .w  (() , refl)
 lem₇ q w (suc n) q'  w' (init    , _ , _ , _ , (_ , ()) ,   _)
 lem₇ q w (suc n) q'  w' (⊍inj₁ p , _ , u , _ , _        , prf)
   = lem₇ p u n q' w' prf
 lem₇ q w (suc n) q'  w' (⊍inj₂ _ , _ , _ , _ , (_ , ()) ,   _)

 lem₆ : ∀ q w n q' w'
        → (⊍inj₂ q , w) ⊢ᵏ n ─ (⊍inj₂ q' , w')
        → (q , w) ⊢ᵏₑ₂ n ─ (q' , w')
 lem₆ q w zero    .q  .w  (refl , refl) = refl , refl
 lem₆ q w (suc n)  q'  w' (init    , _ , _ , _     , (_ , ()) ,    _)
 lem₆ q w (suc n)  q'  w' (⊍inj₁ p , _ , _ , _     , (_ , ()) ,    _)
 lem₆ q w (suc n)  q'  w' (⊍inj₂ p , a , u , prf₁  , prf₂     , prf₃)
   = p , a , u , prf₁ , prf₂ , lem₆ p u n q' w' prf₃

 lem₅ : ∀ {w q}
        → (q₀ , w) ⊢* (⊍inj₂ q , [])
        → (q₀₂ , w) ⊢*ₑ₂ (q , [])
 lem₅ {w} {q} (zero  , () , _)
 lem₅ {w} {q} (suc n , init       ,  (α _) ,  _ , inj₁ (_    ,    _) , (_ , ()) , _)
 lem₅ {w} {q} (suc n , init       ,  E     ,  _ , inj₁ (_    ,  E≢E) , (_ ,  _) , _) = ⊥-elim (E≢E refl)
 lem₅ {w} {q} (suc n , init       , .E     ,  _ , inj₂ (refl , refl) , (_ , ()) , _)
 lem₅ {w} {q} (suc n , ⊍inj₂  _   ,  (α _) ,  _ , inj₁ (_    ,    _) , (_ , ()) , _)
 lem₅ {w} {q} (suc n , ⊍inj₂  _   ,  E     ,  _ , inj₁ (_    ,  E≢E) , (_ ,  _) , _) = ⊥-elim (E≢E refl)
 lem₅ {w} {q} (suc n , ⊍inj₂  p   , .E     , .w , inj₂ (refl , refl) , (_ ,  _) , _) with Q₂? p q₀₂
 lem₅ {w} {q} (suc n , ⊍inj₂ .q₀₂ , .E     , .w , inj₂ (refl , refl) , (_ ,  _) , prf) | yes refl  = n , lem₆ q₀₂ w n q [] prf
 lem₅ {w} {q} (suc n , ⊍inj₂  p   , .E     , .w , inj₂ (refl , refl) , (_ , ()) ,   _) | no  p≢q₀₂
 lem₅ {w} {q} (suc n , ⊍inj₁  p   ,  _     ,  u , _                  , (_ ,  _) , prf) = ⊥-elim (lem₇ p u n q [] prf)
 
 lem₄ : ∀ q w n q' w'
        → ¬ (⊍inj₂ q , w) ⊢ᵏ n ─ (⊍inj₁ q' , w')
 lem₄ q w zero    q' .w  (() , refl)
 lem₄ q w (suc n) q'  w' (init    , _ , _ , _ , (_ , ()) ,    _)
 lem₄ q w (suc n) q'  w' (⊍inj₁ _ , _ , _ , _ , (_ , ()) ,    _) 
 lem₄ q w (suc n) q'  w' (⊍inj₂ p , _ , u , _ , _        , prf₃)
   = lem₄ p u n q' w' prf₃

 lem₃ : ∀ q w n q' w'
        → (⊍inj₁ q , w) ⊢ᵏ n ─ (⊍inj₁ q' , w')
        → (q , w) ⊢ᵏₑ₁ n ─ (q' , w')
 lem₃ q w zero    .q  .w  (refl , refl) = refl , refl
 lem₃ q w (suc n)  q'  w' (init    , _ , _ , _     , (_ , ()) ,    _)
 lem₃ q w (suc n)  q'  w' (⊍inj₁ p , a , u , prf₁  , prf₂     , prf₃)
   = p , a , u , prf₁ , prf₂ , lem₃ p u n q' w' prf₃
 lem₃ q w (suc n)  q'  w' (⊍inj₂ p , _ , _ , _     , (_ , ()) ,    _)

 lem₂ : ∀ {w q}
        → (q₀ , w) ⊢* (⊍inj₁ q , [])
        → (q₀₁ , w) ⊢*ₑ₁ (q , [])
 lem₂ {w} {q} (zero  , () , _)
 lem₂ {w} {q} (suc n , init       ,  (α _) ,  _ , inj₁ (_    ,    _) , (_ , ()) ,  _)
 lem₂ {w} {q} (suc n , init       ,  E     ,  _ , inj₁ (_    ,  E≢E) , (_ ,  _) ,  _) = ⊥-elim (E≢E refl)
 lem₂ {w} {q} (suc n , init       , .E     ,  _ , inj₂ (refl , refl) , (_ , ()) ,  _)
 lem₂ {w} {q} (suc n , ⊍inj₁  _   ,  (α _) ,  _ , inj₁ (_    ,    _) , (_ , ()) ,  _)
 lem₂ {w} {q} (suc n , ⊍inj₁  _   ,  E     ,  u , inj₁ (_    ,  E≢E) , (_ ,  _) ,  _) = ⊥-elim (E≢E refl)
 lem₂ {w} {q} (suc n , ⊍inj₁  p   , .E     , .w , inj₂ (refl , refl) , (_ ,  _) ,  _) with Q₁? p q₀₁
 lem₂ {w} {q} (suc n , ⊍inj₁ .q₀₁ , .E     , .w , inj₂ (refl , refl) , (_ ,  _) , prf) | yes refl  = n , lem₃ q₀₁ w n q [] prf
 lem₂ {w} {q} (suc n , ⊍inj₁  p   , .E     , .w , inj₂ (refl , refl) , (_ , ()) ,   _) | no  p≢q₀₁ 
 lem₂ {w} {q} (suc n , ⊍inj₂  p   ,  a     ,  u , _                  , (_ ,  _) , prf) = ⊥-elim (lem₄ p u n q [] prf)

 lem₁ : ∀ w
        → w ∈ Lᵉᴺ nfa
        → w ∈ Lᵉᴺ nfa₁ ⊎ w ∈ Lᵉᴺ nfa₂
 lem₁ w (init    , ()   ,   _)
 lem₁ w (⊍inj₁ q , q∈F₁ , prf) = inj₁ (q , q∈F₁ , lem₂ prf)
 lem₁ w (⊍inj₂ q , q∈F₂ , prf) = inj₂ (q , q∈F₂ , lem₅ prf)
