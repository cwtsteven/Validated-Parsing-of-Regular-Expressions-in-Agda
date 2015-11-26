module Approach3.Automata (Σ : Set) where

open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Nat

open import Util
open import Approach3.Subset
open import Approach3.Language Σ


record ε-NFA : Set₁ where
 field
  Q  : Set
  δ  : Q → Σᵉ → Powerset Q {lzero}
  q₀ : Q
  F  : Powerset Q {lzero}
  F? : Decidable F

module ε-NFA-Operations (N : ε-NFA) where
 open ε-NFA N
 
 infix 7 _⊢_
 _⊢_ : (Q × Σᵉ × Σᵉ*) → (Q × Σᵉ*) → Set
 (q , x , xs) ⊢ (q' , w') = xs ≡ w' × q' ∈ δ q x

 infix 7 _⊢ᵏ_─_
 _⊢ᵏ_─_ : (Q × Σᵉ*) → ℕ → (Q × Σᵉ*) → Set
 (q , w) ⊢ᵏ zero    ─ (q' , w') = q ≡ q' × w ≡ w'
 (q , w) ⊢ᵏ (suc n) ─ (q' , w') = Σ[ p ∈ Q ] Σ[ a ∈ Σᵉ ] Σ[ w₁ ∈ Σᵉ* ] ( ((w ≡ a ∷ w₁ × a ≢ E) ⊎ (w ≡ w₁ × a ≡ E)) × (q , a , w₁) ⊢ (p , w₁) × (p , w₁) ⊢ᵏ n ─ (q' , w') )
 
 infix 7 _⊢*_
 _⊢*_ : (Q × Σᵉ*) → (Q × Σᵉ*) → Set
 (q , w) ⊢* (q' , w') = Σ[ n ∈ ℕ ] ((q , w) ⊢ᵏ n ─ (q' , w'))

 infix 7 _⊢*₂_
 _⊢*₂_ : (Q × Σᵉ*) → (Q × Σᵉ*) → Set
 (q , w) ⊢*₂ (q' , w') = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] Σ[ p ∈ Q ] Σ[ w₁ ∈ Σᵉ* ] ( (q , w) ⊢ᵏ n ─ (p , w₁) × (p , w₁) ⊢ᵏ m ─ (q' , w') )

 ⊢ᵏ-lem₃ : ∀ q w n q' w' p w₁ → p ≡ q' → w₁ ≡ w' → (q , w) ⊢ᵏ n ─ (p , w₁) → (q , w) ⊢ᵏ n ─ (q' , w')
 ⊢ᵏ-lem₃ q w zero    q' w' p w₁ p≡q' w₁≡w' (q≡p , w≡w₁)                              = trans q≡p p≡q' , trans w≡w₁ w₁≡w'
 ⊢ᵏ-lem₃ q w (suc n) q' w' p w₁ p≡q' w₁≡w' (p' , a , w₁' , prf₁ , prf₂ , p'w₁'⊢ᵏpw₁) = p' , a , w₁' , prf₁ , prf₂ , ⊢ᵏ-lem₃ p' w₁' n q' w' p w₁ p≡q' w₁≡w' p'w₁'⊢ᵏpw₁

 ⊢ᵏ-lem₂ : ∀ q w n q' w' → (q , w) ⊢ᵏ n ─ (q' , w') → (q , w) ⊢ᵏ (n + zero) ─ (q' , w')
 ⊢ᵏ-lem₂ q w zero    q' w' (q≡q' , w≡w')                     = (q≡q' , w≡w')
 ⊢ᵏ-lem₂ q w (suc n) q' w' (p , a , w₁ , prf₁ , prf₂ , prf₃) = p , a , w₁ , prf₁ , prf₂ , ⊢ᵏ-lem₂ p w₁ n q' w' prf₃

 ⊢ᵏ-lem₁ : ∀ q w n q' w' p w₁ m → (q , w) ⊢ᵏ n ─ (p , w₁) → (p , w₁) ⊢ᵏ m ─ (q' , w') → (q , w) ⊢ᵏ (n + m) ─ (q' , w')
 ⊢ᵏ-lem₁ q w zero    q' w' p w₁ zero       (q≡p , w≡w₁) (p≡q' , w₁≡w') = trans q≡p p≡q' , trans w≡w₁ w₁≡w'
 ⊢ᵏ-lem₁ q w zero    q' w' p w₁ (suc m) (q≡p , w≡w₁) (p' , a , w₁' , inj₁ (w₁≡aw₁' , a≢E) , (refl , p'∈δpa) , p'w₁'⊢ᵏq'w')
                             = p' , a , w₁' , inj₁ (trans w≡w₁ w₁≡aw₁' , a≢E)  , (refl , subst (λ p → p' ∈ δ p a) (sym q≡p) p'∈δpa) , p'w₁'⊢ᵏq'w'
 ⊢ᵏ-lem₁ q w zero    q' w' p w₁ (suc m) (q≡p , w≡w₁) (p' , a , w₁' , inj₂ (w₁≡w₁'  , a≡E) , (refl , p'∈δpE) , p'w₁'⊢ᵏq'w')
                             = p' , a , w₁' , inj₂ (trans w≡w₁ w₁≡w₁'  , a≡E)  , (refl , subst (λ p → p' ∈ δ p a) (sym q≡p) p'∈δpE) , p'w₁'⊢ᵏq'w'
 ⊢ᵏ-lem₁ q w (suc n) q' w' p w₁ zero    (p' , a , w₁' , prf₁ , prf₂ , p'w₁'⊢ᵏpw₁) (p≡q' , w₁≡w')
                           = p' , a , w₁' ,  prf₁ , prf₂ , ⊢ᵏ-lem₃ p' w₁' (n + zero) q' w' p w₁ p≡q' w₁≡w' (⊢ᵏ-lem₂ p' w₁' n p w₁ p'w₁'⊢ᵏpw₁)
 ⊢ᵏ-lem₁ q w (suc n) q' w' p w₁ (suc m) (p' , a , w₁' , prf₁ , prf₂ , p'w₁'⊢ᵏpw₁) pw₁⊢ᵏq'w'
                           = p' , a , w₁' , prf₁ , prf₂ , ⊢ᵏ-lem₁ p' w₁' n q' w' p w₁ (suc m) p'w₁'⊢ᵏpw₁ pw₁⊢ᵏq'w'

 ⊢*₂→⊢* : ∀ q w q' w' → (q , w) ⊢*₂ (q' , w') → (q , w) ⊢* (q' , w')
 ⊢*₂→⊢* q w q' w' (n  , m  , p , w₁ , prf₁ , prf₂) = n + m , ⊢ᵏ-lem₁ q w n q' w' p w₁ m prf₁ prf₂ 


Lᵉᴺ : ε-NFA → Language
Lᵉᴺ nfa = λ w → Σ[ q ∈ Q ] (q ∈ F × (q₀ , toΣᵉ* w) ⊢* (q , []))
 where
  open ε-NFA nfa
  open ε-NFA-Operations nfa


record NFA : Set₁ where
 field
  Q  : Set
  δ  : Q → Σ → Powerset Q {lzero}
  q₀ : Q
  F  : Powerset Q {lzero}
  F? : Decidable F

Lᴺ : NFA → Language {undefined}
Lᴺ = undefined


record DFA : Set₂ where
 field
  Q  : Set₁
  δ  : Q → Σ → Q
  q₀ : Q
  F  : Powerset Q {lzero} -- lsucc lzero?
  F? : Decidable F

module DFA-Operations (D : DFA) where
 open DFA D

 δ* : Q → Σ* → Q
 δ* q [] = q
 δ* q (a ∷ w) = δ* (δ q a) w
  
 δ₀ : Σ* → Q
 δ₀ w = δ* q₀ w
 

Lᴰ : DFA → Language
Lᴰ dfa = λ w → δ₀ w ∈ F
 where
  open DFA dfa
  open DFA-Operations dfa
