open import Util
module Proofs (Σ : Set)(dec : DecEq Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Subset renaming (Ø to ø)
open import RegularExpression Σ dec
open import Automata Σ dec
open import Parsing Σ dec

open ≡-Reasoning

-- L(Regex) = L(NFA)
Lᴿ⊆Lᴺ : ∀ regex → Lᴿ regex ⊆ Lᴺ (Regex2NFA regex)
-- null
Lᴿ⊆Lᴺ Ø _ ()
-- ε
Lᴿ⊆Lᴺ ε []       refl = init , tt , (0 , (refl , refl))
Lᴿ⊆Lᴺ ε (x ∷ xs) ()
-- singleton
Lᴿ⊆Lᴺ (σ a) []           ()
Lᴿ⊆Lᴺ (σ a) (x ∷ y ∷ xs) ()
Lᴿ⊆Lᴺ (σ a) (.a  ∷ [])   refl = accept , tt , 1 , accept , (α a) , [] , inj₁ (refl , λ ()) , (refl , refl) , refl , refl
-- union
-- case w ∈ Lᴿ(e₁)
Lᴿ⊆Lᴺ (e₁ ∣ e₂) w (inj₁ w∈Lᴿ) = lem₁ (Lᴿ⊆Lᴺ e₁ w w∈Lᴿ)
 where
  nfa : NFA
  nfa = Regex2NFA (e₁ ∣ e₂)
  nfa₁ : NFA
  nfa₁ = Regex2NFA e₁
  open NFA nfa
  open NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; {-It to It₁ ;-} δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
  open NFA-Operations nfa
  open NFA-Operations nfa₁ renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_)

  lem₅ : ∀ q a w₁ p → (q , a , w₁) ⊢ₑ₁ (p , w₁) → (∥inj₁ q , a , w₁) ⊢ (∥inj₁ p , w₁)
  lem₅ q a w₁ p (refl , prf) = refl , prf

  lem₄ : ∀ q w n q' w' → (q , w) ⊢ᵏₑ₁ n ─ (q' , w') → (∥inj₁ q , w) ⊢ᵏ n ─ (∥inj₁ q' , w')
  lem₄ q w zero    q' w' (prf₁ , prf₂)                      = cong ∥inj₁ prf₁ , prf₂
  lem₄ q w (suc n) q' w' (p , a , w₁ , w≡aw₁ , prf₁ , prf₂) = ∥inj₁ p , a , w₁ , w≡aw₁ , lem₅ q a w₁ p prf₁ , lem₄ p w₁ n q' w' prf₂

  lem₃ : ∀ w → (q₀ , E , w) ⊢ (∥inj₁ q₀₁ , w)
  lem₃ w = refl , refl

  lem₂ : ∀ q w w' → (q₀₁ , w) ⊢*ₑ₁ (q , w') → (q₀ , w) ⊢* (∥inj₁ q , w')
  lem₂ q w w' (n , prf) = suc n , ∥inj₁ q₀₁ , E , w , inj₂ (refl , refl) , lem₃ w , lem₄ q₀₁ w n q w' prf
    
  lem₁ : w ∈ Lᴺ nfa₁ → w ∈ Lᴺ nfa
  lem₁ (q , q∈F , q₀₁-w⊢*q-[]) = ∥inj₁ q , q∈F , lem₂ q (Data.List.map α w) [] q₀₁-w⊢*q-[]
-- case w ∈ Lᴿ(e₂)
Lᴿ⊆Lᴺ (e₁ ∣ e₂) w (inj₂ w∈Lᴿ) = lem₁ (Lᴿ⊆Lᴺ e₂ w w∈Lᴿ)
 where
  nfa : NFA
  nfa = Regex2NFA (e₁ ∣ e₂)
  nfa₂ : NFA
  nfa₂ = Regex2NFA e₂
  open NFA nfa
  open NFA nfa₂ renaming (Q to Q₂ ; Q? to Q₂? ; {-It to It₂ ;-} δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
  open NFA-Operations nfa
  open NFA-Operations nfa₂ renaming (_⊢_ to _⊢ₑ₂_ ; _⊢*_ to _⊢*ₑ₂_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₂_─_)

  lem₅ : ∀ q a w₁ p → (q , a , w₁) ⊢ₑ₂ (p , w₁) → (∥inj₂ q , a , w₁) ⊢ (∥inj₂ p , w₁)
  lem₅ q a w₁ p (refl , prf) = refl , prf

  lem₄ : ∀ q w n q' w' → (q , w) ⊢ᵏₑ₂ n ─ (q' , w') → (∥inj₂ q , w) ⊢ᵏ n ─ (∥inj₂ q' , w')
  lem₄ q w zero    q' w' (prf₁ , prf₂)                      = cong ∥inj₂ prf₁ , prf₂
  lem₄ q w (suc n) q' w' (p , a , w₁ , w≡aw₁ , prf₁ , prf₂) = ∥inj₂ p , a , w₁ , w≡aw₁ , lem₅ q a w₁ p prf₁ , lem₄ p w₁ n q' w' prf₂

  lem₃ : ∀ w → (q₀ , E , w) ⊢ (∥inj₂ q₀₂ , w)
  lem₃ w = refl , refl

  lem₂ : ∀ q w w' → (q₀₂ , w) ⊢*ₑ₂ (q , w') → (q₀ , w) ⊢* (∥inj₂ q , w')
  lem₂ q w w' (n , prf) = suc n , ∥inj₂ q₀₂ , E , w , inj₂ (refl , refl) , lem₃ w , lem₄ q₀₂ w n q w' prf
    
  lem₁ : w ∈ Lᴺ nfa₂ → w ∈ Lᴺ nfa
  lem₁ (q , q∈F , q₀₂-w⊢*q-[]) = ∥inj₂ q , q∈F , lem₂ q (Data.List.map α w) [] q₀₂-w⊢*q-[]
-- concatenation
Lᴿ⊆Lᴺ (e₁ ∙ e₂) w (w₁ , w₂ , w₁∈Lᴿe₁ , w₂∈Lᴿe₂ , w≡w₁w₂) = undefined
-- kleen star
Lᴿ⊆Lᴺ (e * ) w (n , w∈Lᴿeⁿ) = undefined

module ε-lemmas where
 nfa : NFA
 nfa = Regex2NFA ε
 open NFA nfa
 open NFA-Operations nfa

 lem₂ : ∀ w n → ¬ ((error , w) ⊢ᵏ n ─ (init , []))
 lem₂ w zero    (() , _)
 lem₂ w (suc n) (init  , a , w₁ , w≡aw₁ , (refl , ()) , pw₁⊢ᵏinit[])
 lem₂ w (suc n) (error , a , w₁ , w≡aw₁ , (refl , tt) , pw₁⊢ᵏinit[]) = lem₂ w₁ n pw₁⊢ᵏinit[]

 lem₁ : ∀ a w n → ¬ ((init , (α a) ∷ w) ⊢ᵏ n ─ (init , []))
 lem₁ a w zero    (refl , ())
 lem₁ a w (suc n) (init  , E     , w₁           , inj₁ (() , _) , (refl , _)  , pw₁⊢ᵏinit[])
 lem₁ a w (suc n) (init  , E     , []           , inj₂ (() , _) , (refl , _)  , pw₁⊢ᵏinit[])
 lem₁ a w (suc n) (init  , E     , (E ∷ w₁)     , inj₂ (() , _) , (refl , _)  , pw₁⊢ᵏinit[])
 lem₁ a w (suc n) (init  , E     , ((α c) ∷ w₁) , _             , (refl , _)  , pw₁⊢ᵏinit[]) = lem₁ c w₁ n pw₁⊢ᵏinit[]
 lem₁ a w (suc n) (init  , (α b) , w₁           , _             , (refl , ()) , pw₁⊢ᵏinit[])
 lem₁ a w (suc n) (error , b     , w₁           , _             , (refl , _)  , pw₁⊢ᵏinit[]) = lem₂ w₁ n pw₁⊢ᵏinit[]

Lᴿ⊇Lᴺ : ∀ regex → Lᴿ regex ⊇ Lᴺ (Regex2NFA regex)
-- null
Lᴿ⊇Lᴺ Ø w  (_ , () , _)
-- ε
Lᴿ⊇Lᴺ ε [] _ = refl
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , tt , zero  , _ , ())
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E     , w₁           , inj₁ (() , _) , (refl , tt) ,  initw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E     , []           , inj₂ (() , _) , (refl , tt) ,  initw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E     , (E ∷ w₁)     , inj₂ (() , _) , (refl , tt) ,  initw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E     , ((α a) ∷ w₁) , _             , (refl , tt) ,  initw₁⊢ᵏinit[]) = ⊥-elim (ε-lemmas.lem₁ a w₁ n initw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , tt , suc n , init  , (α a) , w₁           , _             , (refl , ()) ,  initw₁⊢ᵏinit[]) 
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , tt , suc n , error , E     , w₁           , _             , (refl , ()) , errorw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , tt , suc n , error , (α a) , w₁           , _             , (refl , tt) , errorw₁⊢ᵏinit[]) = ⊥-elim (ε-lemmas.lem₂ w₁ n errorw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (error , () , _)
-- others
Lᴿ⊇Lᴺ _ = undefined

Lᴿ=Lᴺ : ∀ regex → Lᴿ regex ≈ Lᴺ (Regex2NFA regex)
Lᴿ=Lᴺ regex = Lᴿ⊆Lᴺ regex , Lᴿ⊇Lᴺ regex
