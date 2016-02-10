{-
  This module contains the following proofs:
    ∀e∈RegExp. L(e) ⊆ L(regexToε-NFA e)
    ∀e∈RegExp. L(e) ⊇ L(regexToε-NFA e)

  Steven Cheung 2015.
  Version 10-01-2016
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
open import Induction.Nat

open import Subset renaming (Ø to ø)
open import Subset.DecidableSubset renaming (Ø to ø ; _∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_) hiding (_⊆_ ; _⊇_)
open import Language Σ dec
open import RegularExpression Σ dec
open import Automata Σ dec
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
           → v ∈ Lᴿ e ^ n
           → w ∈ Lᵉᴺ nfa
    lem₁ w u .[] zero  w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , n , prf₁) refl
      = E ∷ uᵉ , trans (trans w≡uv (List-lem₂ u)) u≡uᵉ , inj q₁ , q₁∈F₁ , suc n , lem₂ uᵉ uᵉ n q₁ [] (sym (List-lem₂ uᵉ)) prf₁
    lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) with lem₁ v s t n v≡st (Lᴿ⊆Lᵉᴺ e s s∈Lᴿe) t∈Lᴿeⁿ
    lem₁ w u .[] (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) | .[] , refl , ._  , q₂∈F , zero  , (refl , refl)
      = E ∷ uᵉ , trans (trans w≡uv (List-lem₂ u)) u≡uᵉ , inj q₁ , q₁∈F₁ , suc n₁ , lem₂ uᵉ uᵉ n₁ q₁ [] (sym (List-lem₂ uᵉ)) prf₁
    lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  q₂     , q₂∈F , suc m , prf₂ with inj q₀₁ ∈ᵈ? δ (inj q₁) E | inspect (δ (inj q₁) E) (inj q₀₁)
    lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  init   , q₂∈F , suc m , prf₂ | true  | [ eq ] with lem₄₀ vᵉ (suc m) [] prf₂
    lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  init   , q₂∈F , suc m , prf₂ | true  | [ eq ] | v≡[]
      = E ∷ uᵉ , Σᵉ*-lem₅ w u v uᵉ vᵉ w≡uv u≡uᵉ v≡vᵉ v≡[] , inj q₁ , q₁∈F₁ , suc n₁ , lem₂ uᵉ uᵉ n₁ q₁ [] (sym (List-lem₂ uᵉ)) prf₁
    lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  inj q₂ , q₂∈F , suc m , prf₂ | true  | [ eq ] with lem₄ vᵉ m q₂ prf₂
    lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  inj q₂ , q₂∈F , suc m , prf₂ | true  | [ eq ] | m₂ , vᵉ₁ , v≡vᵉ₁ , prf₃
      = E ∷ uᵉ ++ E ∷ vᵉ₁ , Σᵉ*-lem₃ w u uᵉ v vᵉ vᵉ₁ w≡uv u≡uᵉ v≡vᵉ v≡vᵉ₁ , inj q₂ , q₂∈F
        , ⊢*-lem₂ (suc n₁ , suc m₂ , inj q₁ , E ∷ vᵉ₁
        , lem₂ (uᵉ ++ E ∷ vᵉ₁) uᵉ n₁ q₁ (E ∷ vᵉ₁) refl prf₁
        , (inj q₀₁ , E , vᵉ₁ , refl , (refl , eq) , prf₃))
    lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  q₂     , q₂∈F , suc m , prf₂ | false | [ eq ] with q₁ ∈ᵈ? F₁ | Q₁? q₀₁ q₀₁
    lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  q₂     , q₂∈F , suc m , prf₂ | false | [ eq ] | true  | yes refl
      = ⊥-elim (Bool-lem₂ (subst (λ p → p ≡ false) (Bool-lem₁ (q₀₁ ∈ᵈ? δ₁ q₁ E)) eq))
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
Lᴿ⊇Lᵉᴺ (e *) w prf = lem₁ w prf
  where
    open import Correctness.RegExpToe-NFA.KleenStar-lemmas Σ dec e
    open Lᴿ⊇Lᴺ
    open ε-NFA nfa
    open ε-NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
    open ε-NFA-Operations nfa
    open ε-NFA-Operations nfa₁
      renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢*₂_ to _⊢*₂ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₁ ; ⊢*-lem₂ to ⊢*-lem₂ₑ₁ ; ⊢*-lem₃ to ⊢*-lem₃ₑ₁)
    open ≡-Reasoning

    NoLoop-lem₁ : ∀ w wᵉ n q vᵉ
                  → w ≡ toΣ* wᵉ
                  → inj q ∈ᵈ F
                  → (prf : (inj q₀₁ , wᵉ) ⊢ᵏ n ─ (inj q , vᵉ))
                  → NoLoop q₀₁ wᵉ n q vᵉ prf
                  → toΣ* (find-uᵉ q₀₁ wᵉ n q vᵉ prf) ∈ Lᵉᴺ nfa₁
    NoLoop-lem₁ w wᵉ n q vᵉ w≡wᵉ q∈F prf NoLoop-prf
      = uᵉ , refl , q , q∈F , n , lem₆ q₀₁ wᵉ n q vᵉ prf NoLoop-prf
      where
        uᵉ : Σᵉ*
        uᵉ = find-uᵉ q₀₁ wᵉ n q vᵉ prf


    HasLoop-lem₁ : ∀ n w wᵉ q
                   → w ≡ toΣ* wᵉ
                   → inj q ∈ᵈ F
                   → (prf : (inj q₀₁ , wᵉ) ⊢ᵏ n ─ (inj q , []))
                   → HasLoop q₀₁ wᵉ n q [] prf
                   → Σ[ n₁ ∈ ℕ ] w ∈ Lᴿ e ^ n₁
    HasLoop-lem₁ = <-rec _ helper
      where
        helper : ∀ n
                 → (∀ m₁
                   → m₁ <′ n
                   → ∀ w wᵉ q
                     → w ≡ toΣ* wᵉ
                     → inj q ∈ᵈ F
                     → (prf : (inj q₀₁ , wᵉ) ⊢ᵏ m₁ ─ (inj q , []))
                     → HasLoop q₀₁ wᵉ m₁ q [] prf
                     → Σ[ n₁ ∈ ℕ ] w ∈ Lᴿ e ^ n₁)
                 → ∀ w wᵉ q
                   → w ≡ toΣ* wᵉ
                   → inj q ∈ᵈ F
                   → (prf : (inj q₀₁ , wᵉ) ⊢ᵏ n ─ (inj q , []))
                   → HasLoop q₀₁ wᵉ n q [] prf
                   → Σ[ n₁ ∈ ℕ ] w ∈ Lᴿ e ^ n₁
        helper n rec w wᵉ q w≡wᵉ q∈F prf (n₁ , m₁ , p , vᵉ , prf₁ , NoLoop-prf₁ , p∈F , prf₃ , w≡uv , m₁<n) with lem₅ q₀₁ vᵉ m₁ q [] prf₃
        helper n rec w wᵉ q w≡wᵉ q∈F prf (n₁ , m₁ , p , vᵉ , prf₁ , NoLoop-prf₁ , p∈F , prf₃ , w≡uv , m₁<n) | inj₁ NoLoop-prf₃
          = 2 , toΣ* uᵉ , toΣ* vᵉ , u∈Lᴿe , v∈Lᴿe¹ , trans w≡wᵉ (Σᵉ*-lem₄ wᵉ uᵉ vᵉ w≡uv) 
          where
            uᵉ : Σᵉ*
            uᵉ = find-uᵉ q₀₁ wᵉ n₁ p (E ∷ vᵉ) prf₁
            find-u≡v : find-uᵉ q₀₁ vᵉ m₁ q [] prf₃ ≡ vᵉ
            find-u≡v = sym (find-uᵉ-lem₁ q₀₁ vᵉ m₁ q prf₃ NoLoop-prf₃)
            u∈Lᴿe : toΣ* uᵉ ∈ Lᴿ e
            u∈Lᴿe = Lᴿ⊇Lᵉᴺ e (toΣ* uᵉ) (NoLoop-lem₁ w wᵉ n₁ p (E ∷ vᵉ) w≡wᵉ p∈F prf₁ NoLoop-prf₁)
            v∈Lᵉᴺnfa₁ : toΣ* vᵉ ∈ Lᵉᴺ nfa₁
            v∈Lᵉᴺnfa₁ = subst (λ v → v ∈ Lᵉᴺ nfa₁) (cong toΣ* find-u≡v) (NoLoop-lem₁ (toΣ* vᵉ) vᵉ m₁ q [] refl q∈F prf₃ NoLoop-prf₃)
            v∈Lᴿe¹ : toΣ* vᵉ ∈ Lᴿ e ^ 1
            v∈Lᴿe¹ = toΣ* vᵉ , [] , Lᴿ⊇Lᵉᴺ e (toΣ* vᵉ) v∈Lᵉᴺnfa₁ , refl , sym (List-lem₂ (toΣ* vᵉ))
        helper n rec w wᵉ q w≡wᵉ q∈F prf (n₁ , m₁ , p , vᵉ , prf₁ , NoLoop-prf₁ , p∈F , prf₃ , w≡uv , m₁<n) | inj₂ HasLoop-prf₃ with rec m₁ m₁<n (toΣ* vᵉ) vᵉ q refl q∈F prf₃ HasLoop-prf₃
        helper n rec w wᵉ q w≡wᵉ q∈F prf (n₁ , m₁ , p , vᵉ , prf₁ , NoLoop-prf₁ , p∈F , prf₃ , w≡uv , m₁<n) | inj₂ HasLoop-prf₃ | n₂ , vᵉ∈Lᴿⁿ²
          = suc n₂ , toΣ* uᵉ , toΣ* vᵉ , u∈Lᴿe , vᵉ∈Lᴿⁿ² , trans w≡wᵉ (Σᵉ*-lem₄ wᵉ uᵉ vᵉ w≡uv)
          where
            uᵉ : Σᵉ*
            uᵉ = find-uᵉ q₀₁ wᵉ n₁ p (E ∷ vᵉ) prf₁
            u∈Lᴿe : toΣ* uᵉ ∈ Lᴿ e
            u∈Lᴿe = Lᴿ⊇Lᵉᴺ e (toΣ* uᵉ) (NoLoop-lem₁ w wᵉ n₁ p (E ∷ vᵉ) w≡wᵉ p∈F prf₁ NoLoop-prf₁)
      

    lem₄ : ∀ w wᵉ q n
           → w ≡ toΣ* wᵉ
           → inj q ∈ᵈ F
           → (inj q₀₁ , wᵉ) ⊢ᵏ n ─ (inj q , [])
           → Σ[ n₁ ∈ ℕ ] w ∈ Lᴿ e ^ n₁
    lem₄ w wᵉ q n w≡wᵉ q∈F prf with lem₅ q₀₁ wᵉ n q [] prf
    ... | inj₁ prf₁ = suc zero , w , [] , Lᴿ⊇Lᵉᴺ e w w∈Lᵉᴺnfa₁ , refl , sym (List-lem₂ w)
        where
          find-u≡w : toΣ* (find-uᵉ q₀₁ wᵉ n q [] prf) ≡ w
          find-u≡w = trans (sym (cong toΣ* (find-uᵉ-lem₁ q₀₁ wᵉ n q prf prf₁))) (sym w≡wᵉ)
          w∈Lᵉᴺnfa₁ : w ∈ Lᵉᴺ nfa₁
          w∈Lᵉᴺnfa₁ = subst (λ w → w ∈ Lᵉᴺ nfa₁) find-u≡w (NoLoop-lem₁ w wᵉ n q [] w≡wᵉ q∈F prf prf₁)
    ... | inj₂ prf₁ = HasLoop-lem₁ n w wᵉ q w≡wᵉ q∈F prf prf₁
  

    lem₃ : ∀ wᵉ n q₁
           → (q₀ , wᵉ)  ⊢ᵏ suc n ─ (inj q₁ , [])
           → Σ[ n₁ ∈ ℕ ] Σ[ uᵉ ∈ Σᵉ* ] (toΣ* wᵉ ≡ toΣ* uᵉ × (inj q₀₁ , uᵉ) ⊢ᵏ n₁ ─ (inj q₁ , []))
    lem₃ ._ zero    q₁  (inj .q₁  , α _ , .[] , refl , (refl ,   ()) , (refl , refl))
    lem₃ ._ zero    q₁  (inj .q₁  , E   , .[] , refl , (refl , prf₁) , (refl , refl)) with Q₁? q₁ q₀₁
    lem₃ ._ zero   .q₀₁ (inj .q₀₁ , E   , .[] , refl , (refl , prf₁) , (refl , refl)) | yes refl  = zero , [] , (refl , (refl , refl))
    lem₃ ._ zero    q₁  (inj .q₁  , E   , .[] , refl , (refl ,   ()) , (refl , refl)) | no  p≢q₀₁
    lem₃ ._ (suc n) q₁  (init     , α _ ,  uᵉ , refl , (refl ,   ()) , prf₂)
    lem₃ ._ (suc n) q₁  (init     , E   ,  uᵉ , refl , (refl , prf₁) , prf₂) = lem₃ uᵉ n q₁ prf₂
    lem₃ ._ (suc n) q₁  (inj  p   , α _ ,  uᵉ , refl , (refl ,   ()) , prf₂)
    lem₃ ._ (suc n) q₁  (inj  p   , E   ,  uᵉ , refl , (refl , prf₁) , prf₂) with Q₁? p q₀₁
    lem₃ ._ (suc n) q₁  (inj .q₀₁ , E   ,  uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  = suc n , uᵉ , refl , prf₂
    lem₃ ._ (suc n) q₁  (inj  p   , E   ,  uᵉ , refl , (refl ,   ()) , prf₂) | no  p≢q₀₁


    lem₂ : ∀ w wᵉ q n
           → w ≡ toΣ* wᵉ
           → inj q ∈ᵈ F
           → (init , wᵉ) ⊢ᵏ suc n ─ (inj q , [])
           → Σ[ n₁ ∈ ℕ ] w ∈ Lᴿ e ^ n₁
    lem₂ w wᵉ q n w≡wᵉ q∈F prf with lem₃ wᵉ n q prf
    ... | n₁ , wᵉ₁ , w≡wᵉ₁ , prf₁ with lem₄ (toΣ* wᵉ₁) wᵉ₁ q n₁ refl q∈F prf₁
    ...   | n₂ , w₁∈Lᴿeⁿ¹ = n₂ , subst (λ w → w ∈ ((Lᴿ e) ^ n₂)) (sym (trans w≡wᵉ w≡wᵉ₁)) w₁∈Lᴿeⁿ¹


    lem₁ : ∀ w
           → w ∈ Lᵉᴺ nfa
           → w ∈ Lᴿ (e *)
    lem₁ .[] (.[] , refl , .init  , q∈F , zero  , (refl , refl)) = zero , refl
    lem₁  w  ( wᵉ , w≡wᵉ ,  init  , q∈F , suc n , prf) with lem₄₀ wᵉ (suc n) [] prf
    lem₁ ._  ( wᵉ , refl ,  init  , q∈F , suc n , prf) | w≡[] = zero , sym w≡[]
    lem₁  w  ( wᵉ , w≡wᵉ ,  inj q , q∈F , suc n , prf) = lem₂ w wᵉ q n w≡wᵉ q∈F prf
  
