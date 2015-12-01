{-
  This module contains the following proofs:
    L(Regex) = L(ε-NFA)
    L(ε-NFA) = L(NFA)
    L(NFA)   = L(DFA)
    L(DFA)   is Decidable
    L(Regex) is Decidable

  Steven Cheung 2015.
  Version 26-11-2015
-}

module Proofs (Σ : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Util
open import Subset renaming (Ø to ø)
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Parsing Σ


{- proving L(Regex) = L(ε-NFA) -}

-- L(Regex) ⊆ L(ε-NFA)
Lᴿ⊆Lᵉᴺ : ∀ e → Lᴿ e ⊆ Lᵉᴺ (regexToε-NFA e)
-- null
Lᴿ⊆Lᵉᴺ Ø _ ()
-- ε
Lᴿ⊆Lᵉᴺ ε []       refl = init , tt , 0 , refl , refl
Lᴿ⊆Lᵉᴺ ε (x ∷ xs) ()
-- singleton
Lᴿ⊆Lᵉᴺ (σ a) []           ()
Lᴿ⊆Lᵉᴺ (σ a) (x ∷ y ∷ xs) ()
Lᴿ⊆Lᵉᴺ (σ a) (.a  ∷ [])   refl = accept , tt , 1 , accept , α a , [] , inj₁ (refl , λ ()) , (refl , refl) , refl , refl
-- union
Lᴿ⊆Lᵉᴺ (e₁ ∣ e₂) w (inj₁ w∈Lᴿ) = lem₁ (Lᴿ⊆Lᵉᴺ e₁ w w∈Lᴿ)
 where
  open import Proofs.Union-lemmas Σ e₁ e₂
Lᴿ⊆Lᵉᴺ (e₁ ∣ e₂) w (inj₂ w∈Lᴿ) = lem₄ (Lᴿ⊆Lᵉᴺ e₂ w w∈Lᴿ)
 where
  open import Proofs.Union-lemmas Σ e₁ e₂
-- concatenation
Lᴿ⊆Lᵉᴺ (e₁ ∙ e₂) w (u , v , u∈Lᴿe₁ , v∈Lᴿe₂ , w≡uv) = lem₁ w≡uv (Lᴿ⊆Lᵉᴺ e₁ u u∈Lᴿe₁) (Lᴿ⊆Lᵉᴺ e₂ v v∈Lᴿe₂)
 where
  open import Proofs.Concatenation-lemmas Σ e₁ e₂
-- kleen star
Lᴿ⊆Lᵉᴺ (e * ) .[] (zero , refl) = init , tt , 0 , refl , refl  
Lᴿ⊆Lᵉᴺ (e * )  w  (suc n , u , v , u∈Lᴿe , v∈Lᴿeⁿ , w≡uv) = lem₁ n w u v w≡uv (Lᴿ⊆Lᵉᴺ e u u∈Lᴿe) v∈Lᴿeⁿ
 where
  open import Proofs.KleenStar-lemmas Σ e n


-- L(Regex) ⊇ L(ε-NFA)
Lᴿ⊇Lᵉᴺ : ∀ e → Lᴿ e ⊇ Lᵉᴺ (regexToε-NFA e)
-- null
Lᴿ⊇Lᵉᴺ Ø w  (_ , () , _)
-- ε
Lᴿ⊇Lᵉᴺ ε [] _ = refl
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , zero  , _ , ())
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E   , w         , inj₁ (() , _) , (refl , tt) ,  initw⊢ᵏinit[])
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E   , []        , inj₂ (() , _) , (refl , tt) ,  initw⊢ᵏinit[])
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E   , (E ∷ w)   , inj₂ (() , _) , (refl , tt) ,  initw⊢ᵏinit[])
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E   , (α a ∷ w) , _             , (refl , tt) ,  initw⊢ᵏinit[])
  = ⊥-elim (lem₁ a w n initw⊢ᵏinit[])
 where
  open import Proofs.Epsilon-lemmas Σ
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , α a , w         , _             , (refl , ()) ,  initw⊢ᵏinit[]) 
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , error , E   , w         , _             , (refl , ()) , errorw⊢ᵏinit[])
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , error , α a , w         , _             , (refl , tt) , errorw⊢ᵏinit[])
  = ⊥-elim (lem₂ w n [] errorw⊢ᵏinit[])
 where
  open import Proofs.Epsilon-lemmas Σ
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (error , () , _)
-- singleton
Lᴿ⊇Lᵉᴺ (σ a) [] (init   , () , _)
Lᴿ⊇Lᵉᴺ (σ a) [] (accept , tt , zero , () , _)
Lᴿ⊇Lᵉᴺ (σ a) [] (accept , tt , suc n , q      , E   , w , inj₁ (() , _) , _           , _)
Lᴿ⊇Lᵉᴺ (σ a) [] (accept , tt , suc n , init   , E   , w , _             , (refl , tt) , _) = undefined
Lᴿ⊇Lᵉᴺ (σ a) [] (accept , tt , suc n , accept , E   , w , _             , (refl , ()) , _)
Lᴿ⊇Lᵉᴺ (σ a) [] (accept , tt , suc n , error  , E   , w , _             , (refl , ()) , _)
Lᴿ⊇Lᵉᴺ (σ a) [] (accept , tt , suc n , q      , α b , w , inj₁ (() , _) , _           , _)
Lᴿ⊇Lᵉᴺ (σ a) [] (accept , tt , suc n , q      , α b , w , inj₂ (_ , ()) , _           , _)
Lᴿ⊇Lᵉᴺ (σ a) [] (error  , () , _)
Lᴿ⊇Lᵉᴺ (σ a) (.a ∷ []) (accept , tt , 1 , accept , α .a , [] , inj₁ (refl , prf) , (refl , refl) , refl , refl) = refl
Lᴿ⊇Lᵉᴺ (σ a) ( x ∷ [])     _ = undefined
Lᴿ⊇Lᵉᴺ (σ a) ( x ∷ y ∷ xs) _ = undefined
-- others
Lᴿ⊇Lᵉᴺ _ = undefined


-- L(Regex) = L(ε-NFA)
Lᴿ=Lᵉᴺ : ∀ e → Lᴿ e ≈ Lᵉᴺ (regexToε-NFA e)
Lᴿ=Lᵉᴺ e = Lᴿ⊆Lᵉᴺ e , Lᴿ⊇Lᵉᴺ e


{- proving L(ε-NFA) = L(NFA) -}

Lᵉᴺ=Lᴺ : ∀ nfa → Lᵉᴺ nfa ≈ Lᴺ (remove-ε-step nfa)
Lᵉᴺ=Lᴺ = undefined


{- proving L(NFA) = L(DFA) -}

Lᴺ=Lᴰ : ∀ nfa → Lᴺ nfa ≈ Lᴰ (powerset-construction nfa)
Lᴺ=Lᴰ = undefined


{- proving L(DFA) is decidable -}

Dec-Lᴰ : ∀ dfa → Decidable (Lᴰ dfa)
Dec-Lᴰ dfa = λ w → F? (δ₀ w)
 where
  open DFA dfa
  open DFA-Operations dfa


{- proving L(Regex) is decidable -}

Dec-Lᴿ : ∀ e → Decidable (Lᴿ e)
Dec-Lᴿ e = ≈-Decidable
           (≈-sym (≈-trans (Lᴿ=Lᵉᴺ e) (≈-trans (Lᵉᴺ=Lᴺ ε-nfa) (Lᴺ=Lᴰ nfa))))
           (Dec-Lᴰ dfa)
 where
  ε-nfa : ε-NFA
  ε-nfa = regexToε-NFA e
  nfa : NFA
  nfa = regexToNFA e
  dfa : DFA
  dfa = regexToDFA e
