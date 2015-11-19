open import Util
module Proofs (Σ : Set)(dec : DecEq Σ) where

open import Data.Unit
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat

open import Data.Product hiding (Σ)

open import Subset.DecidableSubset renaming (Ø to ø)
open import RegularExpression Σ dec
open import Automata Σ dec

open import Parsing Σ dec
open import Determinisation Σ dec

open ≡-Reasoning

postulate a∈Lᴺσa : ∀ x → accept ∈ (NFA.δ (Regex2NFA (σ x))) init x ≡ true

-- L(Regex) = L(NFA)
lem₁⊆ : ∀ regex → Lᴿ regex ⊆ Lᴺ (Regex2NFA regex)
-- null
lem₁⊆ Ø _ ()
-- ε
lem₁⊆ ε []       refl = refl
lem₁⊆ ε (x ∷ xs) ()
-- singleton
lem₁⊆ (σ a) []            ()
lem₁⊆ (σ a) (x ∷ xs)      x∈Lᴿ with dec a x
lem₁⊆ (σ a) (.a ∷ [])     refl | yes refl = lem
 where
  nfa : NFA
  nfa = Regex2NFA (σ a)
  open NFA nfa
  open NFA-Operations nfa
  last : List Bool
  last = Data.List.map (λ b → b ∈ ((δ init a ⋃ ø) ⋂ F)) (error ∷ [])
  lem₁ : accept ∈ δ init a ≡ true
  lem₁ = a∈Lᴺσa a
  lem : (a ∷ []) ∈ Lᴺ nfa ≡ true
  lem = begin
        (a ∷ []) ∈ Lᴺ nfa                                                                 ≡⟨ refl ⟩
        (init , a ∷ []) ⊢* (init , []) ∧ false ∨ ∃q (accept ∷ error ∷ []) (a ∷ []) ≡⟨ cong (λ b → b ∨ ∃q (accept ∷ error ∷ []) (a ∷ [])) (∧-lem₁ ((init , (a ∷ [])) ⊢* (init , []))) ⟩
        (init , a ∷ []) ⊢* (accept , []) ∧ true ∨ ∃q (error ∷ []) (a ∷ []) ≡⟨ cong (λ b → b ∨ ∃q (error ∷ []) (a ∷ [])) (∧-lem₂ ((init , (a ∷ [])) ⊢* (accept , []))) ⟩
        ((init , a ∷ []) ⊢ (init , []) ∧ (init , []) ⊢ᵏ 0 [ accept , [] ] ∨ ∃p (accept ∷ error ∷ []) (init , a ∷ []) 1 (accept , []) ∨ (init , (a ∷ [])) ⊢ᵏ 0 [ accept , [] ]) ∨ ∃q (error ∷ []) (a ∷ []) ≡⟨ refl ⟩
        ((init , a ∷ []) ⊢ (init , []) ∧ false ∨ ∃p (accept ∷ error ∷ []) (init , a ∷ []) 1 (accept , []) ∨ (init , (a ∷ [])) ⊢ᵏ 0 [ accept , [] ]) ∨ ∃q (error ∷ []) (a ∷ []) ≡⟨ cong (λ b → (b ∨ ∃p (accept ∷ error ∷ []) (init , a ∷ []) 1 (accept , []) ∨ (init , (a ∷ [])) ⊢ᵏ 0 [ accept , [] ]) ∨ ∃q (error ∷ []) (a ∷ [])) (∧-lem₁ ((init , a ∷ []) ⊢ (init , [])))  ⟩
        (((init , a ∷ []) ⊢ (accept , []) ∧ (accept , []) ⊢ᵏ 0 [ accept , [] ] ∨ ∃p (error ∷ []) (init , a ∷ []) 1 (accept , [])) ∨ (init , (a ∷ [])) ⊢ᵏ 0 [ accept , [] ]) ∨ ∃q (error ∷ []) (a ∷ []) ≡⟨ refl ⟩
        ((accept ∈ δ init a ∧ true ∨ ∃p (error ∷ []) (init , a ∷ []) 1 (accept , [])) ∨ (init , (a ∷ [])) ⊢ᵏ 0 [ accept , [] ]) ∨ ∃q (error ∷ []) (a ∷ []) ≡⟨ undefined ⟩
        ((true ∧ true ∨ ∃p (error ∷ []) (init , a ∷ []) 1 (accept , [])) ∨ (init , (a ∷ [])) ⊢ᵏ 0 [ accept , [] ]) ∨ ∃q (error ∷ []) (a ∷ []) ≡⟨ refl ⟩
        true
        ∎
        {-begin
        ((a ∷ []) ∈ Lᴺ nfa)                                   ≡⟨ refl ⟩
        or (false ∷ (accept ∈ (δ init a ⋃ ø) ∧ true) ∷ last)  ≡⟨ cong (λ q → or (false ∷ q ∷ last)) (∧-lem₂ (accept ∈ δ init a ⋃ ø)) ⟩
        or (false ∷ (accept ∈ (δ init a ⋃ ø)) ∷ last)         ≡⟨ cong (λ q → or (false ∷ q ∷ last)) (⋃-lem₁ accept (δ init a)) ⟩
        or (false ∷ (accept ∈ δ init a) ∷ last)               ≡⟨ cong (λ q → or (false ∷ q ∷ last)) lem₁ ⟩
        true
        ∎-}
lem₁⊆ (σ a) (.a ∷ y ∷ xs) ()   | yes refl
lem₁⊆ (σ a) (x ∷ xs)      ()   | no  _
-- union
lem₁⊆ (e₁ ∣ e₂) w w∈Lᴿ≡true with Lᴿ e₁ w | inspect (Lᴿ e₁) w | Lᴿ e₂ w | inspect (Lᴿ e₂) w
lem₁⊆ (e₁ ∣ e₂) w refl | true  | [ eq ] | _     | _   = lem (lem₁⊆ e₁ w eq)
 where
  nfa : NFA
  nfa = Regex2NFA (e₁ ∣ e₂)
  nfa₁ : NFA
  nfa₁ = Regex2NFA e₁
  nfa₂ : NFA
  nfa₂ = Regex2NFA e₂
  open NFA nfa
  open NFA-Operations nfa
  open NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; It to It₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
  open NFA nfa₂ renaming (Q to Q₂ ; Q? to Q₂? ; It to It₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
  It₁' : List Q
  It₁' = Data.List.map ∥inj₁ It₁
  It₂' : List Q
  It₂' = Data.List.map ∥inj₂ It₂
  lem : w ∈ Lᴺ nfa₁ ≡ true → w ∈ Lᴺ nfa ≡ true
  lem w∈Lᴺe₁≡true = begin
                    w ∈ Lᴺ nfa                                                                                   ≡⟨ refl ⟩
                    ∃q It w                  ≡⟨ refl ⟩
                    ((init , w) ⊢* (init , []) ∧ init ∈ F) ∨ ∃q (It₁' ++ It₂') w  ≡⟨ refl ⟩
                    ((init , w) ⊢* (init , []) ∧ init ∈ F) ∨ (((init , w) ⊢* ((∥inj₁ q₀₁) , []) ∧ (∥inj₁ q₀₁) ∈ F) ∨ ∃q ((pop It₁') ++ It₂') w)  ≡⟨ undefined ⟩
                    true
                    ∎
                    {-begin
                    w ∈ Lᴺ nfa                                                                                   ≡⟨ refl ⟩
                    or ( Data.List.map (δ₀ w ⋂ F) (init ∷ (It₁' ++ It₂')) )                                       ≡⟨ cong (λ xs → or ( (init ∈ (δ₀ w ⋂ F)) ∷ xs)) (List-lem₃ It₁' It₂' (δ₀ w ⋂ F)) ⟩
                    or ( init ∈ (δ₀ w ⋂ F) ∷ (Data.List.map (δ₀ w ⋂ F) It₁') ++ (Data.List.map (δ₀ w ⋂ F) It₂') )  ≡⟨ refl ⟩
                    or ( init ∈ (δ₀ w ⋂ F) ∷ (Data.List.map (δ₀ w ⋂ F) It₁') ++ (Data.List.map (δ₀ w ⋂ F) It₂') )  ≡⟨ undefined ⟩
                    or ( init ∈ (δ₀ w ⋂ F) ∷ ((∥inj₁ q₀₁) ∈ δ₀ w ⋂ F ∷ Data.List.map (δ₀ w ⋂ F) (pop It₁')) ++ (Data.List.map (δ₀ w ⋂ F) It₂') )  ≡⟨ undefined ⟩
                    true
                    ∎-}
lem₁⊆ (e₁ ∣ e₂) w refl | false | [ _ ]  | true  | [ eq ]  = lem (lem₁⊆ e₂ w eq)
 where
  lem : w ∈ Lᴺ (Regex2NFA e₂) ≡ true → w ∈ Lᴺ (Regex2NFA (e₁ ∣ e₂)) ≡ true
  lem = undefined
lem₁⊆ (e₁ ∣ e₂) w ()   | false | _      | false | _
-- others
lem₁⊆ (e₁ ∙ e₂) = undefined
lem₁⊆ (e * )    = undefined

lem₁⊇ : ∀ regex → Lᴿ regex ⊇ Lᴺ (Regex2NFA regex)
lem₁⊇ Ø w _ = undefined
lem₁⊇ ε [] prf = prf
lem₁⊇ ε (x ∷ xs) _ = undefined
lem₁⊇ _ = undefined

Lᴿ=Lᴺ : ∀ regex → Lᴿ regex ≈ Lᴺ (Regex2NFA regex)
Lᴿ=Lᴺ regex = lem₁⊆ regex , lem₁⊇ regex


-- L(NFA) ≡ L(DFA)
lem₂⊆ : ∀ nfa → Lᴺ nfa ⊆ Lᴰ (NFA2DFA nfa)
lem₂⊆ nfa []       []∈Lᴺ = undefined --[]∈Lᴺ
lem₂⊆ nfa (x ∷ xs) prf   = undefined

lem₂⊇ : ∀ nfa → Lᴺ nfa ⊇ Lᴰ (NFA2DFA nfa)
lem₂⊇ dfa []       []∈Lᴰ = undefined --[]∈Lᴰ
lem₂⊇ dfa (x ∷ xs) prf   = undefined

Lᴺ=Lᴰ : ∀ nfa → Lᴺ nfa ≈ Lᴰ (NFA2DFA nfa)
Lᴺ=Lᴰ nfa = lem₂⊆ nfa , lem₂⊇ nfa
