{-
  This module contains the following proofs:
    ∀e∈RegExp. L(e) ⊆ L(regexToε-NFA e)
    ∀e∈RegExp. L(e) ⊇ L(regexToε-NFA e)

  Steven Cheung 2015.
  Version 07-01-2016
-}
open import Util
module Correctness.RegExpToe-NFA (Σ : Set)(dec : DecEq Σ) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Subset renaming (Ø to ø)
open import Subset.DecidableSubset renaming (Ø to ø ; _∈_ to _∈ᵈ_)
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ dec
open import State


{- ∀e∈RegExp. L(e) ⊆ L(regexToε-NFA e) -}
Lᴿ⊆Lᵉᴺ : ∀ e → Lᴿ e ⊆ Lᵉᴺ (regexToε-NFA e)
-- null
Lᴿ⊆Lᵉᴺ Ø _ ()
-- ε
Lᴿ⊆Lᵉᴺ ε = Lᴿ⊆Lᴺ.lem₁
 where open import Correctness.RegExpToe-NFA.Epsilon-lemmas Σ dec
-- singleton
Lᴿ⊆Lᵉᴺ (σ a) = Lᴿ⊆Lᴺ.lem₁
 where open import Correctness.RegExpToe-NFA.Singleton-lemmas Σ dec a
-- union
Lᴿ⊆Lᵉᴺ (e₁ ∣ e₂) w (inj₁ w∈Lᴿ) = Lᴿ⊆Lᴺ.lem₁ (Lᴿ⊆Lᵉᴺ e₁ w w∈Lᴿ)
 where open import Correctness.RegExpToe-NFA.Union-lemmas Σ dec e₁ e₂
Lᴿ⊆Lᵉᴺ (e₁ ∣ e₂) w (inj₂ w∈Lᴿ) = Lᴿ⊆Lᴺ.lem₄ (Lᴿ⊆Lᵉᴺ e₂ w w∈Lᴿ)
 where open import Correctness.RegExpToe-NFA.Union-lemmas Σ dec e₁ e₂
-- concatenation
Lᴿ⊆Lᵉᴺ (e₁ ∙ e₂) w (u , v , u∈Lᴿe₁ , v∈Lᴿe₂ , w≡uv)
  = Lᴿ⊆Lᴺ.lem₁ w≡uv (Lᴿ⊆Lᵉᴺ e₁ u u∈Lᴿe₁) (Lᴿ⊆Lᵉᴺ e₂ v v∈Lᴿe₂)
 where open import Correctness.RegExpToe-NFA.Concatenation-lemmas Σ dec e₁ e₂
-- kleen star
Lᴿ⊆Lᵉᴺ (e * ) .[] (zero , refl)
  = [] , refl , init , refl , 0 , refl , refl
Lᴿ⊆Lᵉᴺ (e * )  w  (suc n , u , v , u∈Lᴿe , v∈Lᴿeⁿ⁺¹ , w≡uv)
  = lem₁ w u v n w≡uv (Lᴿ⊆Lᵉᴺ e u u∈Lᴿe) v∈Lᴿeⁿ⁺¹
 where
  open import Correctness.RegExpToe-NFA.KleenStar-lemmas Σ dec e
  open Lᴿ⊆Lᴺ
  open ε-NFA nfa
  open ε-NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
  open ε-NFA-Operations nfa
  open ≡-Reasoning
  lem₁ : ∀ w u v n
         → w ≡ u ++ v
         → u ∈ Lᵉᴺ nfa₁
         → v ∈ (Lᴿ e ^ n)
         → w ∈ Lᵉᴺ nfa
  lem₁ w u .[] zero  w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , n , prf₁) refl
    = E ∷ uᵉ , trans (trans w≡uv (List-lem₂ u)) u≡uᵉ , inj q₁ , q₁∈F₁ , suc n , lem₂ uᵉ uᵉ n q₁ [] (sym (List-lem₂ uᵉ)) prf₁
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) with lem₁ v s t n v≡st (Lᴿ⊆Lᵉᴺ e s s∈Lᴿe) t∈Lᴿeⁿ
  lem₁ w u .[] (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) | .[] , refl , ._  , q₂∈F , zero  , (refl , refl)
    = E ∷ uᵉ , trans (trans w≡uv (List-lem₂ u)) u≡uᵉ , inj q₁ , q₁∈F₁ , suc n₁ , lem₂ uᵉ uᵉ n₁ q₁ [] (sym (List-lem₂ uᵉ)) prf₁
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  q₂     , q₂∈F , suc m , prf₂ with inj q₀₁ ∈ᵈ δ (inj q₁) E | inspect (δ (inj q₁) E) (inj q₀₁)
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  init   , q₂∈F , suc m , prf₂ | true  | [ eq ]
    = ⊥-elim (lem₅ vᵉ m [] prf₂)
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  inj q₂ , q₂∈F , suc m , prf₂ | true  | [ eq ] with lem₄ vᵉ m q₂ prf₂
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  inj q₂ , q₂∈F , suc m , prf₂ | true  | [ eq ] | vᵉ₁ , vᵉ≡Evᵉ₁ , prf₃
    = E ∷ uᵉ ++ E ∷ vᵉ₁ , w≡EuEv , inj q₂ , q₂∈F , ⊢*-lem₂ (suc n₁ , suc m , inj q₁ , E ∷ vᵉ₁ , lem₂ (uᵉ ++ E ∷ vᵉ₁) uᵉ n₁ q₁ (E ∷ vᵉ₁) refl prf₁  , (inj q₀₁ , E , vᵉ₁ , refl , (refl , eq) , prf₃))
    where
     w≡EuEv : w ≡ toΣ* (uᵉ ++ E ∷ vᵉ₁)
     w≡EuEv = begin
              w                         ≡⟨ w≡uv ⟩
              u ++ v                    ≡⟨ cong (λ u → u ++ v) u≡uᵉ ⟩
              toΣ* uᵉ ++ v              ≡⟨ cong (λ v → toΣ* uᵉ ++ v) v≡vᵉ ⟩
              toΣ* uᵉ ++ toΣ* vᵉ        ≡⟨ cong (λ v → toΣ* uᵉ ++ toΣ* v) vᵉ≡Evᵉ₁ ⟩
              toΣ* uᵉ ++ toΣ* (E ∷ vᵉ₁) ≡⟨ Σᵉ*-lem₆ {uᵉ} {E ∷ vᵉ₁} ⟩
              toΣ* (uᵉ ++ E ∷ vᵉ₁)
              ∎
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  q₂     , q₂∈F , suc m , prf₂ | false | [ eq ] with q₁ ∈ᵈ F₁ | Q₁? q₀₁ q₀₁
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  q₂     , q₂∈F , suc m , prf₂ | false | [ eq ] | true  | yes refl
    = ⊥-elim (Bool-lem₂ (subst (λ p → p ≡ false) (Bool-lem₁ (q₀₁ ∈ᵈ δ₁ q₁ E)) eq))
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ ,    () , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  q₂     , q₂∈F , suc m , prf₂ | false | [ eq ] | false | yes refl
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  q₂     , q₂∈F , suc m , prf₂ | false | [ eq ] | _     | no  q₀₁≢q₀₁
    = ⊥-elim (q₀₁≢q₀₁ refl)


{- ∀e∈RegExp. L(e) ⊇ L(regexToε-NFA e) -}
Lᴿ⊇Lᵉᴺ : ∀ e → Lᴿ e ⊇ Lᵉᴺ (regexToε-NFA e)
-- null
Lᴿ⊇Lᵉᴺ Ø w  (_ , _ , _ , () , _)
-- ε
Lᴿ⊇Lᵉᴺ ε = Lᴿ⊇Lᴺ.lem₁
 where open import Correctness.RegExpToe-NFA.Epsilon-lemmas Σ dec
-- singleton
Lᴿ⊇Lᵉᴺ (σ a) = Lᴿ⊇Lᴺ.lem₁
 where open import Correctness.RegExpToe-NFA.Singleton-lemmas Σ dec a
-- union
Lᴿ⊇Lᵉᴺ (e₁ ∣ e₂) w w∈Lᴺ with Lᴿ⊇Lᴺ.lem₁ w w∈Lᴺ
 where open import Correctness.RegExpToe-NFA.Union-lemmas Σ dec e₁ e₂
... | inj₁ w∈Lᵉᴺe₁ = inj₁ (Lᴿ⊇Lᵉᴺ e₁ w w∈Lᵉᴺe₁)
... | inj₂ w∈Lᵉᴺe₂ = inj₂ (Lᴿ⊇Lᵉᴺ e₂ w w∈Lᵉᴺe₂)
-- concatenation
Lᴿ⊇Lᵉᴺ (e₁ ∙ e₂) w w∈Lᴺ with Lᴿ⊇Lᴺ.lem₁ w w∈Lᴺ
 where open import Correctness.RegExpToe-NFA.Concatenation-lemmas Σ dec e₁ e₂
... | u , v , u∈Lᵉᴺₑ₁ , v∈Lᵉᴺₑ₂ , w≡uv = u , v , Lᴿ⊇Lᵉᴺ e₁ u u∈Lᵉᴺₑ₁ , Lᴿ⊇Lᵉᴺ e₂ v v∈Lᵉᴺₑ₂ , w≡uv
-- kleen star
Lᴿ⊇Lᵉᴺ (e *) = undefined
