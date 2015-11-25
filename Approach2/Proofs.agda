open import Util
module Approach2.Proofs (Σ : Set)(dec : DecEq Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Subset renaming (Ø to ø)
open import Language Σ
open import RegularExpression Σ
open import Approach2.Automata Σ
open import Approach2.Parsing Σ dec

{- 
  proving L(Regex) = L(NFA)
-}

-- L(Regex) ⊆ L(NFA)
Lᴿ⊆Lᴺ : ∀ regex → Lᴿ regex ⊆ Lᴺ (parseToNFA regex)
-- null
Lᴿ⊆Lᴺ Ø _ ()
-- ε
Lᴿ⊆Lᴺ ε []       refl = init , refl , 0 , refl , refl
Lᴿ⊆Lᴺ ε (x ∷ xs) ()
-- singleton
Lᴿ⊆Lᴺ (σ a) []           ()
Lᴿ⊆Lᴺ (σ a) (x ∷ y ∷ xs) ()
Lᴿ⊆Lᴺ (σ a) (.a  ∷ [])   refl = accept , refl , 1 , accept , α a , [] , inj₁ (refl , λ ()) , (refl , undefined) , refl , refl
-- union
Lᴿ⊆Lᴺ _ = undefined
{-
Lᴿ⊆Lᴺ (e₁ ∣ e₂) w (inj₁ w∈Lᴿ) = lem₁ w (Lᴿ⊆Lᴺ e₁ w w∈Lᴿ)
 where
  open import Proofs.Union-lemmas Σ e₁ e₂
Lᴿ⊆Lᴺ (e₁ ∣ e₂) w (inj₂ w∈Lᴿ) = lem₄ w (Lᴿ⊆Lᴺ e₂ w w∈Lᴿ)
 where
  open import Proofs.Union-lemmas Σ e₁ e₂
-- concatenation
Lᴿ⊆Lᴺ (e₁ ∙ e₂) w (w₁ , w₂ , w₁∈Lᴿe₁ , w₂∈Lᴿe₂ , w≡w₁w₂) = lem₁ w w₁ w₂ w≡w₁w₂ (Lᴿ⊆Lᴺ e₁ w₁ w₁∈Lᴿe₁) (Lᴿ⊆Lᴺ e₂ w₂ w₂∈Lᴿe₂)
 where
  open import Proofs.Concatenation-lemmas Σ e₁ e₂
-- kleen star
Lᴿ⊆Lᴺ (e * ) w (n , w∈Lᴿeⁿ) = undefined
-}


-- L(Regex) ⊇ L(NFA)
Lᴿ⊇Lᴺ : ∀ regex → Lᴿ regex ⊇ Lᴺ (parseToNFA regex)
-- null
Lᴿ⊇Lᴺ Ø w  (_ , () , _)
-- ε
Lᴿ⊇Lᴺ ε [] _ = refl
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , refl , zero  , _ , ())
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , refl , suc n , init  , E   , w         , inj₁ (() , _) , (refl , refl) ,  initw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , refl , suc n , init  , E   , []        , inj₂ (() , _) , (refl , refl) ,  initw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , refl , suc n , init  , E   , (E ∷ w)   , inj₂ (() , _) , (refl , refl) ,  initw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , refl , suc n , init  , E   , (α a ∷ w) , _             , (refl , refl) ,  initw₁⊢ᵏinit[]) = undefined --⊥-elim (lem₁ a w n initw₁⊢ᵏinit[])
 where
  open import Proofs.Epsilon-lemmas Σ
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , refl , suc n , init  , α a , w         , _             , (refl , ()) ,  initw₁⊢ᵏinit[]) 
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , refl , suc n , error , E   , w         , _             , (refl , ()) , errorw₁⊢ᵏinit[])
Lᴿ⊇Lᴺ ε (x ∷ xs) (init  , refl , suc n , error , α a , w         , _             , (refl , refl) , errorw₁⊢ᵏinit[]) = undefined --⊥-elim (lem₂ w n errorw₁⊢ᵏinit[])
 where
  open import Proofs.Epsilon-lemmas Σ
Lᴿ⊇Lᴺ ε (x ∷ xs) (error , () , _)
-- singleton
Lᴿ⊇Lᴺ (σ a) [] (init   , () , _)
Lᴿ⊇Lᴺ (σ a) [] (accept , refl , zero , () , _)
Lᴿ⊇Lᴺ (σ a) [] (accept , refl , suc n , q      , E   , w , inj₁ (() , _) , _           , _)
Lᴿ⊇Lᴺ (σ a) [] (accept , refl , suc n , init   , E   , w , _             , (refl , refl) , _) = undefined
Lᴿ⊇Lᴺ (σ a) [] (accept , refl , suc n , accept , E   , w , _             , (refl , ()) , _)
Lᴿ⊇Lᴺ (σ a) [] (accept , refl , suc n , error  , E   , w , _             , (refl , ()) , _)
Lᴿ⊇Lᴺ (σ a) [] (accept , refl , suc n , q      , α b , w , inj₁ (() , _) , _           , _)
Lᴿ⊇Lᴺ (σ a) [] (accept , refl , suc n , q      , α b , w , inj₂ (_ , ()) , _           , _)
Lᴿ⊇Lᴺ (σ a) [] (error  , () , _)
Lᴿ⊇Lᴺ (σ a) _ = undefined
{-
Lᴿ⊇Lᴺ (σ a) (.a ∷ []) (accept , refl , 1 , accept , α .a , [] , inj₁ (refl , prf) , (refl , aa) , refl , refl) = refl
Lᴿ⊇Lᴺ (σ a) ( x ∷ []) _ = undefined
Lᴿ⊇Lᴺ (σ a) ( x ∷ y ∷ xs) _ = undefined
-}
-- others
Lᴿ⊇Lᴺ _ = undefined

-- L(Regex) = L(NFA)
Lᴿ=Lᴺ : ∀ regex → Lᴿ regex ≈ Lᴺ (parseToNFA regex)
Lᴿ=Lᴺ regex = Lᴿ⊆Lᴺ regex , Lᴿ⊇Lᴺ regex


{- 
  proving L(NFA) = L(DFA)
-}

Lᴺ=Lᴰ : ∀ nfa → Lᴺ nfa ≈ Lᴰ (determinise nfa)
Lᴺ=Lᴰ = undefined

--Dec-Lᴿ : ∀ regex → Decidable (Lᴿ regex)
--Dec-Lᴿ regex = ≈-Decidable (Lᴰ (parseToDFA regex)) (Lᴿ regex) (≈-sym (≈-trans (Lᴿ=Lᴺ regex) (Lᴺ=Lᴰ (parseToNFA regex)))) (Dec-Lᴰ (parseToDFA regex))
