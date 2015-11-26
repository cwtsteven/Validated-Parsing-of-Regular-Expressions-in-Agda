module Proofs (Σ : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Function

open import Util
open import Subset renaming (Ø to ø)
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Parsing Σ

{- 
  proving L(Regex) = L(NFA)
-}

-- L(Regex) ⊆ L(NFA)
Lᴿ⊆Lᵉᴺ : ∀ regex → Lᴿ regex ⊆ Lᵉᴺ (parseToε-NFA regex)
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
Lᴿ⊆Lᵉᴺ (e₁ ∣ e₂) w (inj₁ w∈Lᴿ) = lem₁ w (Lᴿ⊆Lᵉᴺ e₁ w w∈Lᴿ)
 where
  open import Proofs.Union-lemmas Σ e₁ e₂
Lᴿ⊆Lᵉᴺ (e₁ ∣ e₂) w (inj₂ w∈Lᴿ) = lem₄ w (Lᴿ⊆Lᵉᴺ e₂ w w∈Lᴿ)
 where
  open import Proofs.Union-lemmas Σ e₁ e₂
-- concatenation
Lᴿ⊆Lᵉᴺ (e₁ ∙ e₂) w (w₁ , w₂ , w₁∈Lᴿe₁ , w₂∈Lᴿe₂ , w≡w₁w₂) = lem₁ w w₁ w₂ w≡w₁w₂ (Lᴿ⊆Lᵉᴺ e₁ w₁ w₁∈Lᴿe₁) (Lᴿ⊆Lᵉᴺ e₂ w₂ w₂∈Lᴿe₂)
 where
  open import Proofs.Concatenation-lemmas Σ e₁ e₂
-- kleen star
Lᴿ⊆Lᵉᴺ (e * ) w (n , w∈Lᴿeⁿ) = undefined


-- L(Regex) ⊇ L(NFA)
Lᴿ⊇Lᵉᴺ : ∀ regex → Lᴿ regex ⊇ Lᵉᴺ (parseToε-NFA regex)
-- null
Lᴿ⊇Lᵉᴺ Ø w  (_ , () , _)
-- ε
Lᴿ⊇Lᵉᴺ ε [] _ = refl
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , zero  , _ , ())
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E   , w         , inj₁ (() , _) , (refl , tt) ,  initw₁⊢ᵏinit[])
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E   , []        , inj₂ (() , _) , (refl , tt) ,  initw₁⊢ᵏinit[])
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E   , (E ∷ w)   , inj₂ (() , _) , (refl , tt) ,  initw₁⊢ᵏinit[])
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , E   , (α a ∷ w) , _             , (refl , tt) ,  initw₁⊢ᵏinit[]) = ⊥-elim (lem₁ a w n initw₁⊢ᵏinit[])
 where
  open import Proofs.Epsilon-lemmas Σ
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , init  , α a , w         , _             , (refl , ()) ,  initw₁⊢ᵏinit[]) 
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , error , E   , w         , _             , (refl , ()) , errorw₁⊢ᵏinit[])
Lᴿ⊇Lᵉᴺ ε (x ∷ xs) (init  , tt , suc n , error , α a , w         , _             , (refl , tt) , errorw₁⊢ᵏinit[]) = ⊥-elim (lem₂ w n errorw₁⊢ᵏinit[])
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
Lᴿ⊇Lᵉᴺ (σ a) ( x ∷ []) _ = undefined
Lᴿ⊇Lᵉᴺ (σ a) ( x ∷ y ∷ xs) _ = undefined
-- others
Lᴿ⊇Lᵉᴺ _ = undefined

-- L(Regex) = L(NFA)
Lᴿ=Lᵉᴺ : ∀ regex → Lᴿ regex ≈ Lᵉᴺ (parseToε-NFA regex)
Lᴿ=Lᵉᴺ regex = Lᴿ⊆Lᵉᴺ regex , Lᴿ⊇Lᵉᴺ regex


{-
  proving L(ε-NFA) = L(NFA)
-}
Lᵉᴺ=Lᴺ : ∀ nfa → Lᵉᴺ nfa ≈ Lᴺ (remove-ε-setp nfa)
Lᵉᴺ=Lᴺ = undefined

{- 
  proving L(NFA) = L(DFA)
-}
Lᴺ=Lᴰ : ∀ nfa → Lᴺ nfa ≈ Lᴰ (powerset-construction nfa)
Lᴺ=Lᴰ = undefined


Dec-Lᴰ : ∀ dfa → Decidable (Lᴰ dfa)
Dec-Lᴰ dfa = λ w → F? (δ₀ w)
 where
  open DFA dfa
  open DFA-Operations dfa

Dec-Lᴿ : ∀ regex → Decidable (Lᴿ regex)
Dec-Lᴿ regex = ≈-Decidable
               (Lᴰ (parseToDFA regex))
               (Lᴿ regex)
               (≈-sym (≈-trans (Lᴿ=Lᵉᴺ regex) (≈-trans (Lᵉᴺ=Lᴺ (parseToε-NFA regex)) (Lᴺ=Lᴰ (remove-ε-setp (parseToε-NFA regex))))))
               (Dec-Lᴰ (parseToDFA regex))
