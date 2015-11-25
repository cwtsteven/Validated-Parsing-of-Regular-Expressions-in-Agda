module Approach3.Proofs.Epsilon-lemmas (Σ : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Nat

open import Approach3.Language Σ
open import Approach3.RegularExpression Σ
open import Approach3.Automata Σ
open import Approach3.Parsing Σ

nfa : ε-NFA
nfa = parseToε-NFA ε
open ε-NFA nfa
open ε-NFA-Operations nfa

lem₂ : ∀ w n → ¬ ((error , w) ⊢ᵏ n ─ (init , []))
lem₂ w zero    (() , _)
lem₂ w (suc n) (init  , a , w₁ , w≡aw₁ , (refl , ()) , pw₁⊢ᵏinit[])
lem₂ w (suc n) (error , a , w₁ , w≡aw₁ , (refl , tt) , pw₁⊢ᵏinit[]) = lem₂ w₁ n pw₁⊢ᵏinit[]

lem₁ : ∀ a w n → ¬ ((init , α a ∷ w) ⊢ᵏ n ─ (init , []))
lem₁ a w zero    (refl , ())
lem₁ a w (suc n) (init  , E   , w₁         , inj₁ (() , _) , (refl , _)  , pw₁⊢ᵏinit[])
lem₁ a w (suc n) (init  , E   , []         , inj₂ (() , _) , (refl , _)  , pw₁⊢ᵏinit[])
lem₁ a w (suc n) (init  , E   , (E ∷ w₁)   , inj₂ (() , _) , (refl , _)  , pw₁⊢ᵏinit[])
lem₁ a w (suc n) (init  , E   , (α c ∷ w₁) , _             , (refl , _)  , pw₁⊢ᵏinit[]) = lem₁ c w₁ n pw₁⊢ᵏinit[]
lem₁ a w (suc n) (init  , α b , w₁         , _             , (refl , ()) , pw₁⊢ᵏinit[])
lem₁ a w (suc n) (error , b   , w₁         , _             , (refl , _)  , pw₁⊢ᵏinit[]) = lem₂ w₁ n pw₁⊢ᵏinit[]
