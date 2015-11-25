open import Approach3.RegularExpression
module Approach3.Proofs.Concatenation-lemmas (Σ : Set)(e₁ : Approach3.RegularExpression.RegExp Σ)(e₂ : Approach3.RegularExpression.RegExp Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Util
open import Approach3.Subset
open import Approach3.Language Σ
open import Approach3.Automata Σ
open import Approach3.Parsing Σ

nfa : ε-NFA
nfa = parseToε-NFA (e₁ ∙ e₂)
nfa₁ : ε-NFA
nfa₁ = parseToε-NFA e₁
nfa₂ : ε-NFA
nfa₂ = parseToε-NFA e₂

open ε-NFA nfa
open ε-NFA nfa₁ renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
open ε-NFA nfa₂ renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
open ε-NFA-Operations nfa
open ε-NFA-Operations nfa₁ renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_ ; ⊢*₂→⊢* to ⊢*₂→⊢*ₑ₁ )
open ε-NFA-Operations nfa₂ renaming (_⊢_ to _⊢ₑ₂_ ; _⊢*_ to _⊢*ₑ₂_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₂_─_ ; ⊢*₂→⊢* to ⊢*₂→⊢*ₑ₂ )

lem₅ : ∀ q w n q' w' w₁ w₁' w₂ → w ≡ w₁ ++ w₂ → w' ≡ w₁' ++ w₂ → (q , w₁) ⊢ᵏₑ₁ n ─ (q' , w₁') → (⍟inj₁ q , w) ⊢ᵏ n ─ (⍟inj₁ q' , w')
lem₅ q w zero    q' w' w₁ w₁' w₂ w≡w₁w₂ w'≡w₁'w₂ (q≡q' , w₁≡w₁')
                       = cong ⍟inj₁ q≡q' , List-lem₄ w w' w₁ w₁' w₂ w≡w₁w₂ w'≡w₁'w₂ w₁≡w₁'
lem₅ q w (suc n) q' w' w₁ w₁' w₂ w≡w₁w₂ w'≡w₁'w₂ (p , a , w₃ , inj₁ (w₁≡aw₃ , a≢E)  , (refl , q≡δqa) , prf₃)
                       = ⍟inj₁ p , a , w₃ ++ w₂ , inj₁ (List-lem₅ w w₁ (a ∷ w₃) w₂ w≡w₁w₂ w₁≡aw₃ , a≢E) , (refl , q≡δqa) , lem₅ p (w₃ ++ w₂) n q' w' w₃ w₁' w₂ refl w'≡w₁'w₂ prf₃
lem₅ q w (suc n) q' w' w₁ w₁' w₂ w≡w₁w₂ w'≡w₁'w₂ (p , E , w₃ , inj₂ (w₁≡w₃  , refl) , (refl , q≡δqE) , prf₃)
                       = ⍟inj₁ p , E , w₃ ++ w₂ , inj₂ (List-lem₅ w w₁ w₃ w₂ w≡w₁w₂ w₁≡w₃ , refl) , (refl , q≡δqE) , lem₅ p (w₃ ++ w₂) n q' w' w₃ w₁' w₂ refl w'≡w₁'w₂ prf₃


lem₄ : ∀ q w n q' w' → (q , w) ⊢ᵏₑ₂ n ─ (q' , w') → (⍟inj₂ q , w) ⊢ᵏ n ─ (⍟inj₂ q' , w')
lem₄ q w zero    q' w' (q≡q' , w≡w')                     = cong ⍟inj₂ q≡q' , w≡w'
lem₄ q w (suc n) q' w' (p , a , w₁ , prf₁ , prf₂ , prf₃) = ⍟inj₂ p , a , w₁ , prf₁ , prf₂ , lem₄ p w₁ n q' w' prf₃


¬inj₂⊢ᵏinj₁ : ∀ q w n q' w' → ¬ (⍟inj₂ q , w) ⊢ᵏ n ─ (⍟inj₁ q' , w')
¬inj₂⊢ᵏinj₁ q w zero    q' w' (() , w≡w')
¬inj₂⊢ᵏinj₁ q w (suc n) q' w' (⍟inj₁ p , a , w₁ , prf₁ , (refl , ()) , prf₃)
¬inj₂⊢ᵏinj₁ q w (suc n) q' w' (mid     , a , w₁ , prf₁ , (refl , ()) , prf₃)
¬inj₂⊢ᵏinj₁ q w (suc n) q' w' (⍟inj₂ p , a , w₁ , prf₁ , prf₂        , prf₃) = ¬inj₂⊢ᵏinj₁ p w₁ n q' w' prf₃


¬mid⊢ᵏinj₁ : ∀ w n q' w' → ¬ ((mid , w) ⊢ᵏ n ─ (⍟inj₁ q' , w'))
¬mid⊢ᵏinj₁ w zero    q' w' (() , w≡w')
¬mid⊢ᵏinj₁ w (suc n) q' w' (⍟inj₁ p , a , w₁ , prf₁ , (refl , ()) , prf₃)
¬mid⊢ᵏinj₁ w (suc n) q' w' (mid     , a , w₁ , prf₁ , (refl , ()) , prf₃)
¬mid⊢ᵏinj₁ w (suc n) q' w' (⍟inj₂ p , a , w₁ , prf₁ , prf₂        , prf₃) = ¬inj₂⊢ᵏinj₁ p w₁ n q' w' prf₃


lem₃ : ∀ q w n p w' → (⍟inj₁ q , w) ⊢ᵏ n ─ (⍟inj₁ p , w') → (⍟inj₁ p , E , w') ⊢ (mid , w') → (⍟inj₁ q , w) ⊢ᵏ (suc n) ─ (mid , w')
lem₃ q w zero    p w' (q≡p , w≡w') (refl , mid∈δpE)                 = mid , E , w' , inj₂ (w≡w' , refl) , (refl , subst (λ p → mid ∈ δ p E) (sym q≡p) mid∈δpE) , refl , refl
lem₃ q w (suc n) p w' (⍟inj₁ p' , a , w₁ , prf₁ , prf₂ , prf₃) prf₄ = ⍟inj₁ p' , a , w₁ , prf₁ , prf₂ , lem₃ p' w₁ n p w' prf₃ prf₄
lem₃ q w (suc n) p w' (mid      , a , w₁ , prf₁ , prf₂ , prf₃) prf₄ = ⊥-elim (¬mid⊢ᵏinj₁ w₁ n p w' prf₃)
lem₃ q w (suc n) p w' (⍟inj₂ p' , a , w₁ , prf₁ , prf₂ , prf₃) prf₄ = ⊥-elim (¬inj₂⊢ᵏinj₁ p' w₁ n p w' prf₃)


lem₂ : ∀ w₁ q₁ w₂ q₂ w w' → q₁ ∈ F₁ → w ≡ w₁ ++ w₂ → (q₀₁ , w₁) ⊢*ₑ₁ (q₁ , []) → (q₀₂ , w₂) ⊢*ₑ₂ (q₂ , w') → (q₀ , w) ⊢* (⍟inj₂ q₂ , w')
lem₂ w₁ q₁ w₂ q₂ w w' q₁∈F₁ w≡w₁w₂ (n₁ , prf₁) (n₂ , prf₂)
     = ⊢*₂→⊢* q₀ w (⍟inj₂ q₂) w' (suc n₁ , suc n₂ , mid , w₂ , lem₃ q₀₁ w n₁ q₁ w₂ (lem₅ q₀₁ w n₁ q₁ w₂ w₁ [] w₂ w≡w₁w₂ refl prf₁) (refl , q₁∈F₁) , ((⍟inj₂ q₀₂) , E , w₂ , (inj₂ (refl , refl)) , (refl , refl) , lem₄ q₀₂ w₂ n₂ q₂ w' prf₂))


lem₁ : ∀ w w₁ w₂ → w ≡ w₁ ++ w₂ → w₁ ∈ Lᵉᴺ nfa₁ → w₂ ∈ Lᵉᴺ nfa₂ → w ∈ Lᵉᴺ nfa
lem₁ w w₁ w₂ w≡w₁w₂ (q₁ , q₁∈F₁ , q₀₁-w₁⊢*q₁-[]) (q₂ , q₂∈F₂ , q₀₂-w₂⊢*q₂-[])
     = ⍟inj₂ q₂ , q₂∈F₂ , lem₂ (toΣᵉ* w₁) q₁ (toΣᵉ* w₂) q₂ (toΣᵉ* w) [] q₁∈F₁ (Σᵉ*-lem₁ w w₁ w₂ (toΣᵉ* w) (toΣᵉ* w₁) (toΣᵉ* w₂) refl refl refl w≡w₁w₂) q₀₁-w₁⊢*q₁-[] q₀₂-w₂⊢*q₂-[]
