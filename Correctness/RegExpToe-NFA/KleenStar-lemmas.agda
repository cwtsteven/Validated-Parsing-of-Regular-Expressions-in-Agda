open import Util
open import RegularExpression
module Correctness.RegExpToe-NFA.KleenStar-lemmas (Σ : Set)(dec : DecEq Σ)(e : RegularExpression.RegExp Σ) where

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
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_)
open import Language Σ
open import Automata Σ
open import Translation Σ dec
open import State

nfa : ε-NFA
nfa = regexToε-NFA (e *)

nfa₁ : ε-NFA
nfa₁ = regexToε-NFA e

open ε-NFA nfa
open ε-NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
open ε-NFA-Operations nfa
open ε-NFA-Operations nfa₁
  renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢*₂_ to _⊢*₂ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₁ ; ⊢*-lem₂ to ⊢*-lem₂ₑ₁ ; ⊢*-lem₃ to ⊢*-lem₃ₑ₁)

¬lem₂ : ∀ q wᵉ n vᵉ
        → ¬ (inj q , wᵉ) ⊢ᵏ n ─ (init , vᵉ)
¬lem₂ q wᵉ zero    vᵉ (() , _)
¬lem₂ q wᵉ (suc n) vᵉ (init  , α _ , uᵉ , _ , (refl ,   ()) , prf₂)
¬lem₂ q wᵉ (suc n) vᵉ (init  , E   , uᵉ , _ , (refl ,   ()) , prf₂)
¬lem₂ q wᵉ (suc n) vᵉ (inj p , a   , uᵉ , _ , (refl , prf₁) , prf₂)
  = ¬lem₂ p uᵉ n vᵉ prf₂

¬lem₁ : ∀ wᵉ n vᵉ
        → ¬ (init , wᵉ) ⊢ᵏ suc n ─ (init , vᵉ)
¬lem₁ ._ zero    .uᵉ (.init  , α _ , uᵉ , refl , (refl ,   ()) , (refl , refl))
¬lem₁ ._ zero    .uᵉ (.init  , E   , uᵉ , refl , (refl ,   ()) , (refl , refl))
¬lem₁ ._ (suc n)  vᵉ ( init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂)
¬lem₁ ._ (suc n)  vᵉ ( init  , E   , uᵉ , refl , (refl ,   ()) , prf₂) 
¬lem₁ ._ (suc n)  vᵉ ( inj p , a   , uᵉ , refl , (refl , prf₁) , prf₂)
  = ¬lem₂ p uᵉ (suc n) vᵉ prf₂


module Lᴿ⊆Lᴺ where


 lem₄ : ∀ wᵉ n q₁
        → (q₀ , wᵉ)  ⊢ᵏ suc n ─ (inj q₁ , [])
        → Σ[ uᵉ ∈ Σᵉ* ] (wᵉ ≡ E ∷ uᵉ × (inj q₀₁ , uᵉ) ⊢ᵏ n ─ (inj q₁ , []))
 lem₄ ._ n  q₁ (init     , α _ , u , refl , (refl ,   ()) , prf₂)
 lem₄ ._ n  q₁ (init     , E   , u , refl , (refl ,   ()) , prf₂)
 lem₄ ._ n  q₁ (inj  p   , α _ , u , refl , (refl ,   ()) , prf₂)
 lem₄ ._ n  q₁ (inj  p   , E   , u , refl , (refl , prf₁) , prf₂) with Q₁? p q₀₁
 lem₄ ._ n  q₁ (inj .q₀₁ , E   , u , refl , (refl , prf₁) , prf₂) | yes refl = u , refl , prf₂
 lem₄ ._ n  q₁ (inj  p   , E   , u , refl , (refl ,   ()) , prf₂) | no p≢q₀₁


 lem₃ : ∀ q wᵉ uᵉ n q' vᵉ
        → wᵉ ≡ uᵉ ++ vᵉ
        → (q , uᵉ) ⊢ᵏₑ₁ n ─ (q' , [])
        → (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , vᵉ)
 lem₃ q wᵉ .[] zero    .q  vᵉ w≡uv (refl , refl) = refl , w≡uv
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , α a , u₁ , refl , (refl , prf₁) , prf₂)
   = inj p , α a , u₁ ++ vᵉ , w≡uv , (refl , prf₁) , lem₃ p (u₁ ++ vᵉ) u₁ n q' vᵉ refl prf₂
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) with inj p ∈ᵈ δ (inj q) E | inspect (δ (inj q) E) (inj p)
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | true  | [ eq ]
   = inj p , E , u₁ ++ vᵉ , w≡uv , (refl , eq) , lem₃ p (u₁ ++ vᵉ) u₁ n q' vᵉ refl prf₂
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | false | [ eq ] with p ∈ᵈ δ₁ q E | inspect (δ₁ q E) p
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | false | [ () ] | true  | [ eq₁ ]
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl ,   ()) , prf₂) | false | [ eq ] | false | [ eq₁ ]


 lem₂ : ∀ wᵉ uᵉ n q vᵉ
        → wᵉ ≡ uᵉ ++ vᵉ
        → (q₀₁ , uᵉ) ⊢ᵏₑ₁ n ─ (q , [])
        → (init , E ∷ wᵉ) ⊢ᵏ suc n ─ (inj q , vᵉ)
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf with inj q₀₁ ∈ᵈ δ q₀ E | inspect (δ q₀ E) (inj q₀₁)
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | true  | [ eq ] = inj q₀₁ , E , wᵉ , refl , (refl , eq) , lem₃ q₀₁ wᵉ uᵉ n q vᵉ w≡uv prf
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | false | [ eq ] with Q₁? q₀₁ q₀₁
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | false | [ () ] | yes refl
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | false | [ eq ] | no  q₀₁≢q₀₁ = ⊥-elim (q₀₁≢q₀₁ refl)


module Lᴿ⊇Lᴺ where
