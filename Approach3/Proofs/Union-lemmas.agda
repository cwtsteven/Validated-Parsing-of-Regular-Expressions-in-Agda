open import Approach3.RegularExpression
module Approach3.Proofs.Union-lemmas (Σ : Set)(e₁ : Approach3.RegularExpression.RegExp Σ)(e₂ : Approach3.RegularExpression.RegExp Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Nat

open import Approach3.Subset
open import Approach3.Language Σ
open import Approach3.Automata Σ
open import Approach3.Parsing Σ

nfa : ε-NFA
nfa = parseToε-NFA (e₁ ∣ e₂)
nfa₁ : ε-NFA
nfa₁ = parseToε-NFA e₁
nfa₂ : ε-NFA
nfa₂ = parseToε-NFA e₂

open ε-NFA nfa
open ε-NFA nfa₁ renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
open ε-NFA nfa₂ renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
open ε-NFA-Operations nfa
open ε-NFA-Operations nfa₁ renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_)
open ε-NFA-Operations nfa₂ renaming (_⊢_ to _⊢ₑ₂_ ; _⊢*_ to _⊢*ₑ₂_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₂_─_)

lem₆ : ∀ q w n q' w' → (q , w) ⊢ᵏₑ₂ n ─ (q' , w') → (⊍inj₂ q , w) ⊢ᵏ n ─ (⊍inj₂ q' , w')
lem₆ q w zero    q' w' (q≡q' , w≡w')                     = cong ⊍inj₂ q≡q' , w≡w'
lem₆ q w (suc n) q' w' (p , a , w₁ , prf₁ , prf₂ , prf₃) = ⊍inj₂ p , a , w₁ , prf₁ , prf₂ , lem₆ p w₁ n q' w' prf₃

lem₅ : ∀ q w w' → (q₀₂ , w) ⊢*ₑ₂ (q , w') → (q₀ , w) ⊢* (⊍inj₂ q , w')
lem₅ q w w' (n , prf) = suc n , ⊍inj₂ q₀₂ , E , w , inj₂ (refl , refl) , (refl , refl) , lem₆ q₀₂ w n q w' prf
    
lem₄ : ∀ w → w ∈ Lᵉᴺ nfa₂ → w ∈ Lᵉᴺ nfa
lem₄ w (q , q∈F , q₀₂-w⊢*q-[]) = ⊍inj₂ q , q∈F , lem₅ q (toΣᵉ* w) [] q₀₂-w⊢*q-[]

lem₃ : ∀ q w n q' w' → (q , w) ⊢ᵏₑ₁ n ─ (q' , w') → (⊍inj₁ q , w) ⊢ᵏ n ─ (⊍inj₁ q' , w')
lem₃ q w zero    q' w' (q≡q' , w≡w')                     = cong ⊍inj₁ q≡q' , w≡w'
lem₃ q w (suc n) q' w' (p , a , w₁ , prf₁ , prf₂ , prf₃) = ⊍inj₁ p , a , w₁ , prf₁ , prf₂ , lem₃ p w₁ n q' w' prf₃

lem₂ : ∀ q w w' → (q₀₁ , w) ⊢*ₑ₁ (q , w') → (q₀ , w) ⊢* (⊍inj₁ q , w')
lem₂ q w w' (n , prf) = suc n , ⊍inj₁ q₀₁ , E , w , inj₂ (refl , refl) , (refl , refl) , lem₃ q₀₁ w n q w' prf
  
lem₁ : ∀ w → w ∈ Lᵉᴺ nfa₁ → w ∈ Lᵉᴺ nfa
lem₁ w (q , q∈F , q₀₁-w⊢*q-[]) = ⊍inj₁ q , q∈F , lem₂ q (toΣᵉ* w) [] q₀₁-w⊢*q-[]

