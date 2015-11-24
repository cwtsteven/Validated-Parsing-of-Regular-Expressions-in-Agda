module Proofs.Epsilon-lemmas (Σ : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Nat

open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Parsing Σ

nfa : NFA
nfa = parseToNFA ε
open NFA nfa
open NFA-Operations nfa

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
