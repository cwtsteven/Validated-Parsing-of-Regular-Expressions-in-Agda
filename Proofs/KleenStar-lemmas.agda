open import RegularExpression
open import Data.Nat
module Proofs.KleenStar-lemmas (Σ : Set)(e : RegularExpression.RegExp Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty

open import Util
open import Subset
open import Language Σ
open import Automata Σ
open import Translation Σ
open import State

nfa : ε-NFA
nfa = regexToε-NFA (e *)

nfa₁ : ε-NFA
nfa₁ = regexToε-NFA e

open ε-NFA nfa
open ε-NFA nfa₁ renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
open ε-NFA-Operations nfa
open ε-NFA-Operations nfa₁ renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₁)

lem₆ : ∀ q w n q' u v
       → w ≡ u ++ v
       → (q , u) ⊢ᵏₑ₁ n ─ (q' , [])
       → (inj q , w) ⊢ᵏ n ─ (inj q' , v)
lem₆ q w zero    q' .[] u w≡u[] (q≡q' , refl)
  = cong inj q≡q' , trans w≡u[] refl
lem₆ q w (suc n) q' u v w≡uv (p , (α a) , u' , inj₁ (u≡au' , a≢E)  , (refl , p≡δqa) , prf₃)
  = inj p , (α a) , u' ++ v , inj₁ (List-lem₅ w≡uv u≡au' , a≢E)
    , (refl , p≡δqa) , lem₆ p (u' ++ v) n q' u' v refl prf₃
lem₆ q w (suc n) q' u v w≡uv (p , E , u' , inj₁ (u≡au' , a≢E)  , (refl , p≡δqa) , prf₃) = ⊥-elim (a≢E refl)
lem₆ q w (suc n) q' u v w≡uv (p , .E , u' , inj₂ (u≡u'  , refl) , (refl , p≡δqE) , prf₃)
  = inj p , E , u' ++ v , inj₂ (List-lem₅ w≡uv u≡u'  , refl)
    , (refl , inj₂ p≡δqE) , lem₆ p (u' ++ v) n q' u' v refl prf₃

lem₅ : ∀ w n q' u v
       → w ≡ u ++ v
       → (q₀₁ , u) ⊢ᵏₑ₁ n ─ (q' , [])
       → (init , w) ⊢ᵏ suc n ─ (inj q' , v)
lem₅ w n q' u v w≡uv q₀₁u⊢ᵏₑ₁q'[]
  = inj q₀₁ , E , w , inj₂ (refl , refl) , (refl , refl) , lem₆ q₀₁ w n q' u v w≡uv q₀₁u⊢ᵏₑ₁q'[]

lem₄ : ∀ q a w q' w'
       → (q , a , w) ⊢ₑ₁ (q' , w')
       → (inj q , a , w) ⊢ (inj q' , w')
lem₄ q E     w q' w' (w≡w' , q'∈δqE) = w≡w' , inj₂ q'∈δqE
lem₄ q (α a) w q' w' (w≡w' , q'∈δqE) = w≡w' , q'∈δqE

lem₃ : ∀ q w n q' w'
       → (q , w) ⊢ᵏₑ₁ n ─ (q' , w')
       → (inj q , w) ⊢ᵏ n ─ (inj q' , w')
lem₃ q w zero    .q  .w  (refl , refl) = refl , refl
lem₃ q w (suc n)  q' w' (p , a , u , prf₁ , prf₂ , prf₃)
  = inj p , a , u , prf₁ , lem₄ q a u p u prf₂  , lem₃ p u n q' w' prf₃

lem₂ : ∀ w q' w'
       → (q₀₁ , w) ⊢*ₑ₁ (q' , w')
       → (init , w) ⊢* (inj q' , w')
lem₂ w q' w' (n , prf) = suc n , inj q₀₁ , E , w , inj₂ (refl , refl) , (refl , refl) , lem₃ q₀₁ w n q' w' prf

lem₁ : ∀ w u
       → w ≡ u ++ []
       → u ∈ Lᵉᴺ nfa₁
       → w ∈ Lᵉᴺ nfa
lem₁ w u w≡u[] (q , q∈F₁ , q₀₁u⊢*̂ₑ₁q[])
  = inj q , q∈F₁
    , lem₂ (toΣᵉ* w) q []
      (subst (λ w → (q₀₁ , (toΣᵉ* w)) ⊢*ₑ₁ (q , []))
        (trans (sym (List-lem₂ u)) (sym w≡u[])) q₀₁u⊢*̂ₑ₁q[])
