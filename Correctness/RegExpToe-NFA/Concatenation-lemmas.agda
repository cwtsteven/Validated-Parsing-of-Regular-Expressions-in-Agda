open import Util
open import RegularExpression
module Correctness.RegExpToe-NFA.Concatenation-lemmas (Σ : Set)(dec : DecEq Σ)(e₁ : RegularExpression.RegExp Σ)(e₂ : RegularExpression.RegExp Σ) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ)
open import Language Σ
open import Automata Σ
open import Translation Σ dec
open import State

nfa : ε-NFA
nfa = regexToε-NFA (e₁ ∙ e₂)

nfa₁ : ε-NFA
nfa₁ = regexToε-NFA e₁

nfa₂ : ε-NFA
nfa₂ = regexToε-NFA e₂

open ε-NFA nfa
open ε-NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
open ε-NFA nfa₂ renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
open ε-NFA-Operations nfa
open ε-NFA-Operations nfa₁
  renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₁ ; ⊢*-lem₂ to ⊢*-lem₂ₑ₁ ; ⊢*-lem₃ to ⊢*-lem₃ₑ₁)
open ε-NFA-Operations nfa₂
  renaming (_⊢_ to _⊢ₑ₂_ ; _⊢*_ to _⊢*ₑ₂_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₂_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₂ ; ⊢*-lem₂ to ⊢*-lem₂ₑ₂ ; ⊢*-lem₃ to ⊢*-lem₃ₑ₂)

module Lᴿ⊆Lᴺ where

 lem₅ : ∀ q w n q' w' u t v
        → w  ≡ u ++ v
        → w' ≡ t ++ v
        → (q , u) ⊢ᵏₑ₁ n ─ (q' , t)
        → (⍟inj₁ q , w) ⊢ᵏ n ─ (⍟inj₁ q' , w')
 lem₅ q w zero    q' w' u t v w≡uv w'≡tv (q≡q' , u≡t)
   = cong ⍟inj₁ q≡q' , List-lem₄ w≡uv w'≡tv u≡t
 lem₅ q w (suc n) q' w' u t v w≡uv w'≡tv (p , a , u' , inj₁ (u≡au' , a≢E)  , (refl , p≡δqa) , prf₃)
   = ⍟inj₁ p , a , u' ++ v , inj₁ (List-lem₅ w≡uv u≡au' , a≢E)
     , (refl , p≡δqa) , lem₅ p (u' ++ v) n q' w' u' t v refl w'≡tv prf₃
 lem₅ q w (suc n) q' w' u t v w≡uv w'≡tv (p , E , u' , inj₂ (u≡u'  , refl) , (refl , p≡δqE) , prf₃)
   = ⍟inj₁ p , E , u' ++ v , inj₂ (List-lem₅ w≡uv u≡u'  , refl)
     , (refl , p≡δqE) , lem₅ p (u' ++ v) n q' w' u' t v refl w'≡tv prf₃


 lem₄ : ∀ q w n q' w'
        → (q , w) ⊢ᵏₑ₂ n ─ (q' , w')
        → (⍟inj₂ q , w) ⊢ᵏ n ─ (⍟inj₂ q' , w')
 lem₄ q w zero    q' w' (q≡q' , w≡w')
   = cong ⍟inj₂ q≡q' , w≡w'
 lem₄ q w (suc n) q' w' (p , a , u , prf₁ , prf₂ , prf₃)
   = ⍟inj₂ p , a , u , prf₁ , prf₂ , lem₄ p u n q' w' prf₃


 lem₆ : ∀ q w n q' w'
        → ¬ (⍟inj₂ q , w) ⊢ᵏ n ─ (⍟inj₁ q' , w')
 lem₆ q w zero    q' w' (() , w≡w')
 lem₆ q w (suc n) q' w' (⍟inj₁ p , a , u , prf₁ , (refl , ()) , prf₃)
 lem₆ q w (suc n) q' w' (mid     , a , u , prf₁ , (refl , ()) , prf₃)
 lem₆ q w (suc n) q' w' (⍟inj₂ p , a , u , prf₁ , prf₂        , prf₃)
   = lem₆ p u n q' w' prf₃


 lem₇ : ∀ w n q' w'
        → ¬ ((mid , w) ⊢ᵏ n ─ (⍟inj₁ q' , w'))
 lem₇ w zero    q' w' (() , w≡w')
 lem₇ w (suc n) q' w' (⍟inj₁ p , α a , u , prf₁ , (refl , ()) ,    _)
 lem₇ w (suc n) q' w' (⍟inj₁ p , E   , u , prf₁ , (refl , ()) ,    _)
 lem₇ w (suc n) q' w' (mid     , a   , u , prf₁ , (refl , _)  , prf₃)
   = lem₇ u n q' w' prf₃
 lem₇ w (suc n) q' w' (⍟inj₂ p , a   , u , prf₁ , prf₂        , prf₃)
   = lem₆ p u n q' w' prf₃


 lem₃ : ∀ q w n q' w'
        → (⍟inj₁ q , w) ⊢ᵏ n ─ (⍟inj₁ q' , w')
        → (⍟inj₁ q' , E , w') ⊢ (mid , w')
        → (⍟inj₁ q , w) ⊢ᵏ (suc n) ─ (mid , w')
 lem₃ q w zero    q' w' (q≡q' , w≡w') (refl , mid∈δq'E)
   = mid , E , w' , inj₂ (w≡w' , refl) , (refl , subst (λ p → mid ∈ᵍ δ p E) (sym q≡q') mid∈δq'E) , refl , refl
 lem₃ q w (suc n) q' w' (⍟inj₁ p , a , u , prf₁ , prf₂ , prf₃) prf₄
   = ⍟inj₁ p , a , u , prf₁ , prf₂ , lem₃ p u n q' w' prf₃ prf₄
 lem₃ q w (suc n) q' w' (mid     , a , u , prf₁ , prf₂ , prf₃) prf₄
   = ⊥-elim (lem₇ u n q' w' prf₃)
 lem₃ q w (suc n) q' w' (⍟inj₂ p , a , u , prf₁ , prf₂ , prf₃) prf₄
   = ⊥-elim (lem₆ p u n q' w' prf₃)


 lem₂ : ∀ u q₁ v q₂ w w'
        → q₁ ∈ᵍ F₁
        → w ≡ u ++ v
        → (q₀₁ , u) ⊢*ₑ₁ (q₁ , [])
        → (q₀₂ , v) ⊢*ₑ₂ (q₂ , w')
        → (q₀ , w) ⊢* (⍟inj₂ q₂ , w')
 lem₂ u q₁ v q₂ w w' q₁∈F₁ w≡uv (n₁ , prf₁) (n₂ , prf₂) with δ mid E (⍟inj₂ q₀₂) | inspect (δ mid E) (⍟inj₂ q₀₂)
 lem₂ u q₁ v q₂ w w' q₁∈F₁ w≡uv (n₁ , prf₁) (n₂ , prf₂) | true  | [ eq ]
   = ⊢*-lem₂
     (suc n₁ , suc n₂ , mid , v , lem₃ q₀₁ w n₁ q₁ v
       (lem₅ q₀₁ w n₁ q₁ v u [] v w≡uv refl prf₁) (refl , q₁∈F₁)
       , ((⍟inj₂ q₀₂) , E , v , (inj₂ (refl , refl)) , (refl , eq) , lem₄ q₀₂ v n₂ q₂ w' prf₂))
 lem₂ u q₁ v q₂ w w' q₁∈F₁ w≡uv (n₁ , prf₁) (n₂ , prf₂) | false | [ eq ] with Q₂? q₀₂ q₀₂
 lem₂ u q₁ v q₂ w w' q₁∈F₁ w≡uv (n₁ , prf₁) (n₂ , prf₂) | false | [ () ] | yes refl
 lem₂ u q₁ v q₂ w w' q₁∈F₁ w≡uv (n₁ , prf₁) (n₂ , prf₂) | false | [ eq ] | no  q₀₂≢q₀₂ = ⊥-elim (q₀₂≢q₀₂ refl)

 lem₁ : ∀ {w u v}
        → w ≡ u ++ v
        → u ∈ Lᵉᴺ nfa₁
        → v ∈ Lᵉᴺ nfa₂
        → w ∈ Lᵉᴺ nfa
 lem₁ {w} {u} {v} w≡uv (q₁ , q₁∈F₁ , q₀₁w₁⊢*q₁[]) (q₂ , q₂∈F₂ , q₀₂w₂⊢*q₂[])
      = ⍟inj₂ q₂ , q₂∈F₂
        , lem₂ (toΣᵉ* u) q₁ (toΣᵉ* v) q₂ (toΣᵉ* w) [] q₁∈F₁
               (Σᵉ*-lem₁ {w} {u} {v} w≡uv)
               q₀₁w₁⊢*q₁[] q₀₂w₂⊢*q₂[]

module Lᴿ⊇Lᴺ where
 lem₁ : ∀ w
        → w ∈ Lᵉᴺ nfa
        → w ∈ Lᴿ Σ (e₁ ∙ e₂)
 lem₁ w (q , q∈F , prf₁) with ⊢*-lem₃ prf₁
 lem₁ w (._ , ()   ,   _) | zero  , zero  , ._ , ._ , (refl , refl) , (refl , _)
 lem₁ w ( q , q∈F , prf₁) | zero  , suc m , ._ , ._ , (refl , refl) , prf           = {!!}
 lem₁ w ( q , q∈F , prf₁) | suc n , zero  , ._ , ._ , prf           , (refl , refl) = {!!}
 lem₁ w ( q , q∈F , prf₁) | suc n , suc m ,  p ,  u , prf₂          , prf₃          = {!!}
