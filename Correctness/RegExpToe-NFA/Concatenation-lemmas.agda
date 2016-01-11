{-
  This module contains the following proofs:

  Steven Cheung 2015.
  Version 11-01-2016
-}
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
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_)
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
  renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢*₂_ to _⊢*₂ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₁ ; ⊢*-lem₂ to ⊢*-lem₂ₑ₁ ; ⊢*-lem₃ to ⊢*-lem₃ₑ₁ ; ⊢ᵏ₂-lem₂ to ⊢ᵏ₂ₑ₁-lem₂)
open ε-NFA-Operations nfa₂
  renaming (_⊢_ to _⊢ₑ₂_ ; _⊢*_ to _⊢*ₑ₂_ ; _⊢*₂_ to _⊢*₂ₑ₂_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₂_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₂ ; ⊢*-lem₂ to ⊢*-lem₂ₑ₂ ; ⊢*-lem₃ to ⊢*-lem₃ₑ₂ ; ⊢ᵏ₂-lem₂ to ⊢ᵏ₂ₑ₂-lem₂)

open ≡-Reasoning 

module Lᴿ⊆Lᴺ where
 lem₆ : ∀ p vᵉ m q₂
        → (p , vᵉ) ⊢ᵏₑ₂ m ─ (q₂ , [])
        → (⍟inj₂ p , vᵉ) ⊢ᵏ m ─ (⍟inj₂ q₂ , [])
 lem₆ p .[] zero    .p  (refl , refl) = refl , refl
 lem₆ p ._  (suc m)  q₂ (r , a , uᵉ , refl , (refl , prf₁) , prf₂)
   = ⍟inj₂ r , a , uᵉ , refl , (refl , prf₁) , lem₆ r uᵉ m q₂ prf₂

 lem₅ : ∀ m q₂ vᵉ
        → (q₀₂ , vᵉ) ⊢ᵏₑ₂ m ─ (q₂ , [])
        → (mid , E ∷ vᵉ) ⊢ᵏ suc m ─ (⍟inj₂ q₂ , [])
 lem₅ m q₂ vᵉ prf with (⍟inj₂ q₀₂) ∈ᵈ δ mid E | inspect (δ mid E) (⍟inj₂ q₀₂)
 lem₅ m q₂ vᵉ prf | true  | [ eq ] = ⍟inj₂ q₀₂ , E , vᵉ , refl , (refl , eq) , lem₆ q₀₂ vᵉ m q₂ prf
 lem₅ m q₂ vᵉ prf | false | [ eq ] with Q₂? q₀₂ q₀₂
 lem₅ m q₂ vᵉ prf | false | [ () ] | yes refl
 lem₅ m q₂ vᵉ prf | false | [ eq ] | no  q₀₂≢q₀₂ = ⊥-elim (q₀₂≢q₀₂ refl)

 lem₄ : ∀ p sᵉ n q₁ vᵉ
        → q₁ ∈ᵍ F₁
        → (p , sᵉ) ⊢ᵏₑ₁ n ─ (q₁ , [])
        → (⍟inj₁ p , sᵉ ++ E ∷ vᵉ) ⊢ᵏ suc n ─ (mid , vᵉ)
 lem₄ .q₁ .[] zero    q₁ vᵉ q₁∈F₁ (refl , refl) = mid , E , vᵉ , refl , (refl , q₁∈F₁) , (refl , refl)
 lem₄  p  ._  (suc n) q₁ vᵉ q₁∈F₁ (r , aᵉ , tᵉ , refl , (refl , prf₁) , prf₂)
   = ⍟inj₁ r , aᵉ , tᵉ ++ E ∷ vᵉ , refl , (refl , prf₁) , lem₄ r tᵉ n q₁ vᵉ q₁∈F₁ prf₂


 lem₃ : ∀ uᵉ q₁ vᵉ n
        → q₁ ∈ᵍ F₁
        → (q₀₁ , uᵉ) ⊢ᵏₑ₁ n ─ (q₁ , [])
        → (q₀ , uᵉ ++ E ∷ E ∷ vᵉ) ⊢ᵏ suc n ─ (mid , E ∷ vᵉ)
 lem₃ .[] .q₀₁ vᵉ zero    q₁∈F₁ (refl , refl) = mid , E , E ∷ vᵉ , refl , (refl , q₁∈F₁) , (refl , refl)
 lem₃ ._   q₁  vᵉ (suc n) q₁∈F₁ (p , aᵉ , sᵉ , refl , (refl , prf₁) , prf₂)
   = ⍟inj₁ p , aᵉ , sᵉ ++ E ∷ E ∷ vᵉ , refl , (refl , prf₁) , lem₄ p sᵉ n q₁ (E ∷ vᵉ) q₁∈F₁ prf₂


 lem₂ : ∀ uᵉ q₁ vᵉ q₂
        → q₁ ∈ᵍ F₁
        → (q₀₁ , uᵉ) ⊢*ₑ₁ (q₁ , [])
        → (q₀₂ , vᵉ) ⊢*ₑ₂ (q₂ , [])
        → (q₀ , uᵉ ++ E ∷ E ∷ vᵉ) ⊢* (⍟inj₂ q₂ , [])
 lem₂ uᵉ q₁ vᵉ q₂ q₁∈F₁ (n , prf₁) (m , prf₂)
   = ⊢*-lem₂ (suc n , suc m , mid , E ∷ vᵉ , lem₃ uᵉ q₁ vᵉ n q₁∈F₁ prf₁ , lem₅ m q₂ vᵉ prf₂)


 lem₁ : ∀ {w u v}
        → w ≡ u ++ v
        → u ∈ Lᵉᴺ nfa₁
        → v ∈ Lᵉᴺ nfa₂
        → w ∈ Lᵉᴺ nfa
 lem₁ {w} {u} {v} w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , prf₁) (vᵉ , v≡vᵉ , q₂ , q₂∈F₂ , prf₂)
      = uᵉ ++ E ∷ E ∷ vᵉ , w≡uᵉEEvᵉ , ⍟inj₂ q₂ , q₂∈F₂
        , lem₂ uᵉ q₁ vᵉ q₂ q₁∈F₁ prf₁ prf₂
      where
       w≡uᵉEEvᵉ : w ≡ toΣ* (uᵉ ++ E ∷ E ∷ vᵉ)
       w≡uᵉEEvᵉ = begin
                  w                            ≡⟨ w≡uv ⟩
                  u ++ v                       ≡⟨ cong (λ u → u ++ v) u≡uᵉ ⟩
                  toΣ* uᵉ ++ v                 ≡⟨ cong (λ v → toΣ* uᵉ ++ v) v≡vᵉ ⟩
                  toΣ* uᵉ ++ toΣ* vᵉ           ≡⟨ cong (λ v → toΣ* uᵉ ++ v) refl ⟩
                  toΣ* uᵉ ++ toΣ* (E ∷ vᵉ)     ≡⟨ cong (λ v → toΣ* uᵉ ++ v) refl ⟩
                  toΣ* uᵉ ++ toΣ* (E ∷ E ∷ vᵉ) ≡⟨ Σᵉ*-lem₁ {uᵉ} {E ∷ E ∷ vᵉ} ⟩
                  toΣ* (uᵉ ++ E ∷ E ∷ vᵉ)
                  ∎


module Lᴿ⊇Lᴺ where
 find-uᵉ : ∀ q wᵉ n q' wᵉ'
         → (q , wᵉ) ⊢ᵏ n ─ (q' , wᵉ')
         → Σᵉ*
 find-uᵉ q wᵉ zero    .q  .wᵉ  (refl , refl)              = []
 find-uᵉ q wᵉ (suc n)  q'  wᵉ' (p , a , uᵉ , _ , _ , prf) = a ∷ find-uᵉ p uᵉ n q' wᵉ' prf

 find-uᵉ' : ∀ q wᵉ n wᵉ'
          → (q , wᵉ) ⊢ᵏ suc n ─ (mid , wᵉ')
          → Σᵉ*
 find-uᵉ' q wᵉ zero    wᵉ'  _                         = []
 find-uᵉ' q wᵉ (suc n) wᵉ' (p , a , uᵉ , _ , _ , prf) = a ∷ find-uᵉ' p uᵉ n wᵉ' prf


 lem₁₁ : ∀ q wᵉ n q' vᵉ prf
         → wᵉ ≡ find-uᵉ q wᵉ n q' vᵉ prf ++ vᵉ
 lem₁₁ q  wᵉ zero    .q .wᵉ (refl , refl) = refl
 lem₁₁ q ._ (suc n)   q' vᵉ (p , a , uᵉ , refl , (refl , _) , prf)
   = cong (λ w → a ∷ w) (lem₁₁ p uᵉ n q' vᵉ prf)


 lem₁₀ : ∀ p vᵉ n q
         → (⍟inj₂ p , vᵉ) ⊢ᵏ n ─ (⍟inj₂ q , [])
         → (p , vᵉ) ⊢ᵏₑ₂ n ─ (q , [])
 lem₁₀ p .[] zero    .p (refl , refl) = refl , refl
 lem₁₀ p ._  (suc n)  q (⍟inj₁ r , a , uᵉ , refl , (refl ,   ()) , prf₂) 
 lem₁₀ p ._  (suc n)  q (mid     , a , uᵉ , refl , (refl ,   ()) , prf₂)
 lem₁₀ p ._  (suc n)  q (⍟inj₂ r , a , uᵉ , refl , (refl , prf₁) , prf₂)
   = r , a , uᵉ , refl , (refl , prf₁) , lem₁₀ r uᵉ n q prf₂


 lem₉ : ∀ q vᵉ m
        → ⍟inj₂ q ∈ᵍ F
        → (mid , vᵉ) ⊢ᵏ m ─ (⍟inj₂ q , [])
        → toΣ* vᵉ ∈ Lᵉᴺ nfa₂
 lem₉ q vᵉ zero    q∈F (() , _)
 lem₉ q []         (suc m) q∈F (_          ,  _    ,  _  , ()   , (refl ,     _) ,    _)
 lem₉ q (α a ∷ vᵉ) (suc m) q∈F (p          ,  α .a , .vᵉ , refl , (refl ,    ()) ,    _)
 lem₉ q (E   ∷ vᵉ) (suc m) q∈F (⍟inj₁ _    , .E    , .vᵉ , refl , (refl ,    ()) ,    _)
 lem₉ q (E   ∷ vᵉ) (suc m) q∈F (mid        , .E    , .vᵉ , refl , (refl ,  prf₁) , prf₂) = lem₉ q vᵉ m q∈F prf₂
 lem₉ q (E   ∷ vᵉ) (suc m) q∈F (⍟inj₂ p    , .E    , .vᵉ , refl , (refl ,  prf₁) , prf₂) with Q₂? p q₀₂
 lem₉ q (E   ∷ vᵉ) (suc m) q∈F (⍟inj₂ .q₀₂ , .E    , .vᵉ , refl , (refl ,  prf₁) , prf₂) | yes refl = vᵉ , refl , q , q∈F , m , lem₁₀ q₀₂ vᵉ m q prf₂
 lem₉ q (E   ∷ vᵉ) (suc m) q∈F (⍟inj₂ p    , .E    , .vᵉ , refl , (refl ,    ()) , prf₂) | no  _

-- --

 lem₈ : ∀ q u₁ n vᵉ
        → ¬ (⍟inj₂ q , u₁) ⊢ᵏ n ─ (mid , vᵉ)
 lem₈ q  u₁ zero    vᵉ (() , _)
 lem₈ q ._  (suc n) vᵉ (⍟inj₁ p , a , uᵉ , refl , (refl ,   ()) , prf₂)
 lem₈ q ._  (suc n) vᵉ (mid     , a , uᵉ , refl , (refl ,   ()) , prf₂)
 lem₈ q ._  (suc n) vᵉ (⍟inj₂ p , a , uᵉ , refl , (refl , prf₁) , prf₂)
   = lem₈ p uᵉ n vᵉ prf₂

{-
 lem₇ : ∀ uᵉ n vᵉ
        → ¬ (mid , uᵉ) ⊢ᵏ suc n ─ (mid , vᵉ)
 lem₇ ._ n vᵉ (⍟inj₁ _ , α _ , u₁ , refl , (refl ,   ()) , prf₂)
 lem₇ ._ n vᵉ (⍟inj₁ _ , E   , u₁ , refl , (refl ,   ()) , prf₂)
 lem₇ ._ n vᵉ (mid     , α _ , u₁ , refl , (refl ,   ()) , prf₂)
 lem₇ ._ n vᵉ (mid     , E   , u₁ , refl , (refl , prf₁) , prf₂) = {!!}
 lem₇ ._ n vᵉ (⍟inj₂ p , a   , u₁ , refl , (refl ,    _) , prf₂)
   = ⊥-elim (lem₈ p u₁ n vᵉ prf₂)
-}

 lem₆ : ∀ q a uᵉ p₁ n p
         → (q , a , uᵉ) ⊢ₑ₁ (p₁ , uᵉ)
         → (p₁ , uᵉ) ⊢ᵏₑ₁ n ─ (p , [])
         → (q , a ∷ uᵉ) ⊢ᵏₑ₁ suc n ─ (p , [])
 lem₆ q a uᵉ p₁ n p prf₁ prf₂ = p₁ , a , uᵉ , refl , prf₁ , prf₂


 lem₅ : ∀ q a uᵉ p₁ n p vᵉ
         → (⍟inj₁ q , a , uᵉ) ⊢ (⍟inj₁ p₁ , uᵉ)
         → (⍟inj₁ p₁ , uᵉ) ⊢ᵏ n ─ (⍟inj₁ p , vᵉ)
         → (⍟inj₁ q , a ∷ uᵉ) ⊢ᵏ suc n ─ (⍟inj₁ p , vᵉ)
 lem₅ q a uᵉ p₁ n p vᵉ prf₁ prf₂ = ⍟inj₁ p₁ , a , uᵉ , refl , prf₁ , prf₂

 lem₇ : ∀ wᵉ n vᵉ
        → (prf : (mid , wᵉ) ⊢ᵏ n ─ (mid , vᵉ))
        → toΣ* wᵉ ≡ toΣ* vᵉ × toΣ* (find-uᵉ mid wᵉ n mid vᵉ prf) ≡ [] 
 lem₇ ._ zero    vᵉ (refl , refl) = refl , refl
 lem₇ ._ (suc n) vᵉ (⍟inj₁ p , α _ , u₁ , refl , (refl ,   ()) , prf₂)
 lem₇ ._ (suc n) vᵉ (⍟inj₁ p , E   , u₁ , refl , (refl ,   ()) , prf₂)
 lem₇ ._ (suc n) vᵉ (mid     , α _ , u₁ , refl , (refl ,   ()) , prf₂)
 lem₇ ._ (suc n) vᵉ (mid     , E   , u₁ , refl , (refl , prf₁) , prf₂) = lem₇ u₁ n vᵉ prf₂
 lem₇ ._ (suc n) vᵉ (⍟inj₂ p , α _ , u₁ , refl , (refl ,   ()) , prf₂) 
 lem₇ ._ (suc n) vᵉ (⍟inj₂ p , E   , u₁ , refl , (refl , prf₁) , prf₂) = ⊥-elim (lem₈ p u₁ n vᵉ prf₂)

 lem₄ : ∀ q wᵉ n vᵉ
        → (prf  : (⍟inj₁ q  , wᵉ) ⊢ᵏ suc n ─ (mid , vᵉ))
        → Σ[ n₁ ∈ ℕ ] Σ[ p ∈ Q₁ ] Σ[ uᵉ ∈ Σᵉ* ] Σ[ prf₁ ∈ (⍟inj₁ q , wᵉ) ⊢ᵏ n₁ ─ (⍟inj₁ p , uᵉ) ]
          ( toΣ* (find-uᵉ (⍟inj₁ q) wᵉ (suc n) mid vᵉ prf) ≡ toΣ* (find-uᵉ (⍟inj₁ q) wᵉ n₁ (⍟inj₁ p) uᵉ prf₁)
            × p ∈ᵍ F₁
            × (q , find-uᵉ (⍟inj₁ q) wᵉ n₁ (⍟inj₁ p) uᵉ prf₁) ⊢ᵏₑ₁ n₁ ─ (p , []) )
 lem₄ q ._ zero    vᵉ (.mid , α _ , .vᵉ  , refl , (refl ,   ()) , (refl , refl)) 
 lem₄ q ._ zero    vᵉ (.mid , E   , .vᵉ  , refl , (refl , q∈F₁) , (refl , refl)) = zero , q , E ∷ vᵉ , (refl , refl) , refl , q∈F₁ , (refl , refl)
 lem₄ q ._ (suc n) vᵉ (⍟inj₁ p₁    , α a ,  uᵉ , refl , (refl ,   q⊢p₁) , prf₁) with lem₄ p₁ uᵉ n vᵉ prf₁
 lem₄ q ._ (suc n) vᵉ (⍟inj₁ p₁    , α a ,  uᵉ , refl , (refl ,   q⊢p₁) , prf₁) | n₁ , p , u₁ , prf₁' , w≡w , p∈F₁ , prf₂
   = suc n₁ , p , u₁ , lem₅ q (α a) uᵉ p₁ n₁ p u₁ (refl , q⊢p₁) prf₁' , cong (λ w → a ∷ w) w≡w , p∈F₁ , lem₆ q (α a) (find-uᵉ (⍟inj₁ p₁) uᵉ n₁ (⍟inj₁ p) u₁ prf₁') p₁ n₁ p (refl , q⊢p₁) prf₂
 lem₄ q ._ (suc n) vᵉ (⍟inj₁ p₁    , E   ,  uᵉ , refl , (refl ,   q⊢p₁) , prf₁) with lem₄ p₁ uᵉ n vᵉ prf₁
 lem₄ q ._ (suc n) vᵉ (⍟inj₁ p₁    , E   ,  uᵉ , refl , (refl ,   q⊢p₁) , prf₁) | n₁ , p , u₁ , prf₁' , w≡w , p∈F₁ , prf₂
   = suc n₁ , p , u₁ , lem₅ q E uᵉ p₁ n₁ p u₁ (refl , q⊢p₁) prf₁' , w≡w , p∈F₁ , lem₆ q E (find-uᵉ (⍟inj₁ p₁) uᵉ n₁ (⍟inj₁ p) u₁ prf₁') p₁ n₁ p (refl , q⊢p₁) prf₂
 lem₄ q ._ (suc n) vᵉ (mid         , α _ ,  uᵉ , refl , (refl ,     ()) , prf₁)
 lem₄ q ._ (suc n) vᵉ (mid         , E   ,  uᵉ , refl , (refl ,   q⊢p₁) , prf₁) with lem₇ uᵉ (suc n) vᵉ prf₁
 lem₄ q ._ (suc n) vᵉ (mid         , E   ,  uᵉ , refl , (refl ,   q⊢p₁) , prf₁) | u≡v , find-u≡[] = zero , q , E ∷ uᵉ , (refl , refl) , find-u≡[] , q⊢p₁ , (refl , refl)
 lem₄ q ._ (suc n) vᵉ (⍟inj₂ _     , a   ,  uᵉ , refl , (refl ,     ()) , prf₁)


 lem₃ : ∀ wᵉ n vᵉ
        → (prf : (q₀  , wᵉ) ⊢ᵏ n ─ (mid , vᵉ))
        → toΣ* (find-uᵉ q₀ wᵉ n mid vᵉ prf) ∈ Lᵉᴺ nfa₁
 lem₃ wᵉ zero    vᵉ (() , _)
 lem₃ wᵉ (suc n) vᵉ prf with lem₄ q₀₁ wᵉ n vᵉ prf
 ... | n₁ , p , uᵉ , prf₁ , w≡wᵉ , p∈F₁ , prf₂
   = find-uᵉ q₀ wᵉ n₁ (⍟inj₁ p) uᵉ prf₁ , w≡wᵉ , p , p∈F₁ , n₁ , prf₂


 lem₃₁ : ∀ q uᵉ n p vᵉ
         → ¬ (⍟inj₂ q , uᵉ) ⊢ᵏ n ─ (⍟inj₁ p , vᵉ)
 lem₃₁ q  uᵉ zero    p vᵉ (() , _)
 lem₃₁ q ._  (suc n) p vᵉ (⍟inj₁ p' , a , uᵉ , refl , (_ , ()) , prf₂)
 lem₃₁ q ._  (suc n) p vᵉ (mid      , a , uᵉ , refl , (_ , ()) , prf₂)
 lem₃₁ q ._  (suc n) p vᵉ (⍟inj₂ p' , a , uᵉ , refl , prf₁     , prf₂)
   = lem₃₁ p' uᵉ n p vᵉ prf₂

 lem₃₀ : ∀ uᵉ n p vᵉ
         → ¬ (mid , uᵉ) ⊢ᵏ n ─ (⍟inj₁ p , vᵉ)
 lem₃₀  uᵉ zero    p vᵉ (() , _)
 lem₃₀ ._  (suc n) p vᵉ (⍟inj₁ p' , α _ , uᵉ , refl , (_ ,   ()) , prf₂)
 lem₃₀ ._  (suc n) p vᵉ (⍟inj₁ p' , E   , uᵉ , refl , (_ ,   ()) , prf₂)
 lem₃₀ ._  (suc n) p vᵉ (mid      , α _ , uᵉ , refl , (_ ,   ()) , prf₂)
 lem₃₀ ._  (suc n) p vᵉ (mid      , E   , uᵉ , refl , (_ , prf₁) , prf₂) = lem₃₀ uᵉ n p vᵉ prf₂
 lem₃₀ ._  (suc n) p vᵉ (⍟inj₂ p' , a , uᵉ , refl , prf₁ , prf₂)
   = ⊥-elim (lem₃₁ p' uᵉ n p vᵉ prf₂)


 lem₁₉ : ∀ q wᵉ n p a uᵉ q'
         → (⍟inj₁ q , wᵉ) ⊢ᵏ n ─ (⍟inj₁ p , a ∷ uᵉ)
         → (⍟inj₁ p , a , uᵉ) ⊢ (⍟inj₁ q' , uᵉ)
         → (⍟inj₁ q , wᵉ) ⊢ᵏ suc n ─ (⍟inj₁ q' , uᵉ)
 lem₁₉ q ._ zero    .q a uᵉ q' (refl , refl) p⊢q' = ⍟inj₁ q' , a , uᵉ , refl , p⊢q' , (refl , refl)
 lem₁₉ q ._ (suc n)  p a uᵉ q' (⍟inj₁ p₁ , a₁   , u₁ , refl , (refl , prf₁) , prf₂) p⊢q'
   = ⍟inj₁ p₁ , a₁ , u₁ , refl , (refl , prf₁) , lem₁₉ p₁ u₁ n p a uᵉ q' prf₂ p⊢q'
 lem₁₉ q ._ (suc n)  p a uᵉ q' (mid      , a₁   , u₁ , refl , (refl , prf₁) , prf₂) p⊢q'
   = ⊥-elim (lem₃₀ u₁ n p (a ∷ uᵉ) prf₂)
 lem₁₉ q ._ (suc n)  p a uᵉ q' (⍟inj₂ p₁ , a₁   , u₁ , refl , (refl ,   ()) , prf₂) p⊢q'


 lem₁₈ : ∀ q wᵉ n p uᵉ
         → (⍟inj₁ q , wᵉ) ⊢ᵏ n ─ (⍟inj₁ p , E ∷ uᵉ)
         → (⍟inj₁ p , E , uᵉ) ⊢ (mid , uᵉ)
         → (⍟inj₁ q , wᵉ) ⊢ᵏ suc n ─ (mid , uᵉ)
 lem₁₈ q ._ zero    .q uᵉ (refl , refl) p⊢mid
   = mid , E , uᵉ , refl , p⊢mid , (refl , refl)
 lem₁₈ q ._ (suc n)  p uᵉ (⍟inj₂ p₁ , a₁ ,  u₁ , refl , (refl ,   ()) , prf₂) p⊢mid
 lem₁₈ q ._ (suc n)  p uᵉ (mid      , a₁ ,  u₁ , refl , (refl , prf₁) , prf₂) p⊢mid
   = ⊥-elim (lem₃₀ u₁ n p (E ∷ uᵉ) prf₂)
 lem₁₈ q ._ (suc n)  p uᵉ (⍟inj₁ p₁ , a₁ ,  u₁ , refl , (refl , prf₁) , prf₂) p⊢mid
   = ⍟inj₁ p₁ , a₁ , u₁ , refl , (refl , prf₁) , lem₁₈ p₁ u₁ n p uᵉ prf₂ p⊢mid
   

 lem₁₇ : ∀ q wᵉ n p uᵉ m q'
         → (⍟inj₁ q , wᵉ) ⊢ᵏ n ─ (⍟inj₁ p , uᵉ)
         → (⍟inj₁ p , uᵉ) ⊢ᵏ m ─ (⍟inj₂ q' , [])
         → Σ[ n₁ ∈ ℕ ] Σ[ m₁ ∈ ℕ ] Σ[ vᵉ ∈ Σᵉ* ] ( (⍟inj₁ q , wᵉ) ⊢ᵏ n₁ ─ (mid , vᵉ) × (mid , vᵉ) ⊢ᵏ m₁ ─ (⍟inj₂ q' , []) )
 lem₁₇ q wᵉ n p  _ zero    q' prf₁ (() , _)
 lem₁₇ q wᵉ n p ._ (suc m) q' prf₁ (⍟inj₁ p₁ , a   , u₁ , refl , (refl , prf₂) , prf₃)
   = lem₁₇ q wᵉ (suc n) p₁ u₁ m q' (lem₁₉ q wᵉ n p a u₁ p₁ prf₁ (refl , prf₂)) prf₃
 lem₁₇ q wᵉ n p ._ (suc m) q' prf₁ (mid      , α _ , u₁ , refl , (refl ,   ()) , prf₃)
 lem₁₇ q wᵉ n p ._ (suc m) q' prf₁ (mid      , E   , u₁ , refl , (refl , prf₂) , prf₃)
   = suc n , m , u₁ , lem₁₈ q wᵉ n p u₁ prf₁ (refl , prf₂) , prf₃
 lem₁₇ q wᵉ n p ._ (suc m) q' prf₁ (⍟inj₂ p₁ , a   , u₁ , refl , (refl ,   ()) , prf₃)

 lem₂₀ : ∀ q wᵉ n p uᵉ m q'
         → (⍟inj₁ q , wᵉ) ⊢ᵏ n ─ (⍟inj₂ p , uᵉ)
         → (⍟inj₂ p , uᵉ) ⊢ᵏ m ─ (⍟inj₂ q' , [])
         → Σ[ n₁ ∈ ℕ ] Σ[ m₁ ∈ ℕ ] Σ[ vᵉ ∈ Σᵉ* ] ( (⍟inj₁ q , wᵉ) ⊢ᵏ n₁ ─ (mid , vᵉ) × (mid , vᵉ) ⊢ᵏ m₁ ─ (⍟inj₂ q' , []) )
 lem₂₀ q _  zero    p uᵉ m q' (() , _) prf₁ 
 lem₂₀ q wᵉ (suc n) p uᵉ m q' prf₁ prf₂ with ⊢ᵏ₂-lem₂ {⍟inj₁ q} {wᵉ} {suc n} {⍟inj₂ p} {uᵉ} prf₁
 lem₂₀ q wᵉ (suc n) p uᵉ m q' prf₁ prf₂ | ⍟inj₁ p₁ , a   , prf₃ , (refl ,   ())
 lem₂₀ q wᵉ (suc n) p uᵉ m q' prf₁ prf₂ | mid      , α _ , prf₃ , (refl ,   ())
 lem₂₀ q wᵉ (suc n) p uᵉ m q' prf₁ prf₂ | mid      , E   , prf₃ , (refl , prf₄)
   = n , suc m , (E ∷ uᵉ) , prf₃ , (⍟inj₂ p , E , uᵉ , refl , (refl , prf₄) , prf₂)
 lem₂₀ q wᵉ (suc n) p uᵉ m q' prf₁ prf₂ | ⍟inj₂ p₁ , a   , prf₃ , (refl , prf₄)
   = lem₂₀ q wᵉ n p₁ (a ∷ uᵉ) (suc m) q' prf₃ (⍟inj₂ p , a , uᵉ , refl , (refl , prf₄) , prf₂)

 lem₁₆ : ∀ wᵉ q
         → (q₀ , wᵉ) ⊢*₂ (⍟inj₂ q , [])
         → Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] Σ[ vᵉ ∈ Σᵉ* ] ( (q₀ , wᵉ) ⊢ᵏ n ─ (mid , vᵉ) × (mid , vᵉ) ⊢ᵏ m ─ (⍟inj₂ q , []) )
 lem₁₆ wᵉ q (n , m , ⍟inj₁ p , uᵉ , prf₁ , prf₂) = lem₁₇ q₀₁ wᵉ n p uᵉ m q prf₁ prf₂
 lem₁₆ wᵉ q (n , m , mid     , uᵉ , prf₁ , prf₂) = n , m , uᵉ , prf₁ , prf₂
 lem₁₆ wᵉ q (n , m , ⍟inj₂ p , uᵉ , prf₁ , prf₂) = lem₂₀ q₀₁ wᵉ n p uᵉ m q prf₁ prf₂


 lem₂ : ∀ q w wᵉ
        → w ≡ toΣ* wᵉ
        → ⍟inj₂ q ∈ᵍ F
        → (q₀ , wᵉ) ⊢*₂ (⍟inj₂ q , [])
        → Σ[ u ∈ Σ* ] Σ[ v ∈ Σ* ] (u ∈ Lᵉᴺ nfa₁ × v ∈ Lᵉᴺ nfa₂ × w ≡ u ++ v)
 lem₂ q w wᵉ w≡wᵉ q∈F prf with lem₁₆ wᵉ q prf
 ... | n , m , vᵉ , prf₁ , prf₂ = toΣ* uᵉ , toΣ* vᵉ , lem₃ wᵉ n vᵉ prf₁ , lem₉ q vᵉ m q∈F prf₂ , trans w≡wᵉ wᵉ≡uᵉvᵉ
  where
   uᵉ : Σᵉ*
   uᵉ = find-uᵉ q₀ wᵉ n mid vᵉ prf₁
   wᵉ≡uᵉvᵉ : toΣ* wᵉ ≡ toΣ* uᵉ ++ toΣ* vᵉ
   wᵉ≡uᵉvᵉ = begin
             toΣ* wᵉ            ≡⟨ cong toΣ* (lem₁₁ q₀ wᵉ n mid vᵉ prf₁) ⟩ 
             toΣ* (uᵉ ++ vᵉ)    ≡⟨ sym (Σᵉ*-lem₁ {uᵉ} {vᵉ}) ⟩ 
             toΣ* uᵉ ++ toΣ* vᵉ
             ∎

 lem₁ : ∀ w
        → w ∈ Lᵉᴺ nfa
        → Σ[ u ∈ Σ* ] Σ[ v ∈ Σ* ] (u ∈ Lᵉᴺ nfa₁ × v ∈ Lᵉᴺ nfa₂ × w ≡ u ++ v)
 lem₁ w (wᵉ , w≡wᵉ , ⍟inj₁ _ , ()  , prf)
 lem₁ w (wᵉ , w≡wᵉ , mid     , ()  , prf)
 lem₁ w (wᵉ , w≡wᵉ , ⍟inj₂ q , q∈F , prf) = lem₂ q w wᵉ w≡wᵉ q∈F (⊢*-lem₃ prf)
