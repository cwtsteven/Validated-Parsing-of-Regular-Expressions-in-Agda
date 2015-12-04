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
open import Translation Σ

nfa : ε-NFA
nfa = regexToε-NFA ε

open ε-NFA nfa
open ε-NFA-Operations nfa

lem₂ : ∀ w n w' → ¬ ((error , w) ⊢ᵏ n ─ (init , w'))
lem₂ w zero    w' (() , _)
lem₂ w (suc n) w' (init  , a , u , w≡au , (refl , ()) , pu⊢ᵏinitw')
lem₂ w (suc n) w' (error , a , u , w≡au , (refl , tt) , pu⊢ᵏinitw') = lem₂ u n w' pu⊢ᵏinitw'

lem₁ : ∀ a w n → ¬ ((init , α a ∷ w) ⊢ᵏ n ─ (init , []))
lem₁ a w zero    (refl , ())
lem₁ a w (suc n) (init  , E   , u         , inj₁ (() , _) , (refl , _)  , pw₁⊢ᵏinit[])
lem₁ a w (suc n) (init  , E   , []         , inj₂ (() , _) , (refl , _) , pw₁⊢ᵏinit[])
lem₁ a w (suc n) (init  , E   , (E ∷ u)   , inj₂ (() , _) , (refl , _)  , pw₁⊢ᵏinit[])
lem₁ a w (suc n) (init  , E   , (α c ∷ u) , _             , (refl , _)  , pw₁⊢ᵏinit[]) = lem₁ c u n pw₁⊢ᵏinit[]
lem₁ a w (suc n) (init  , α b , u         , _             , (refl , ()) , pw₁⊢ᵏinit[])
lem₁ a w (suc n) (error , b   , u         , _             , (refl , _)  , pw₁⊢ᵏinit[]) = lem₂ u n [] pw₁⊢ᵏinit[]
