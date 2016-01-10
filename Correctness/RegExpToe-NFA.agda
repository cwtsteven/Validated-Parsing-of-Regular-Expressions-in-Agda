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
         → v ∈ Lᴿ e ^ n
         → w ∈ Lᵉᴺ nfa
  lem₁ w u .[] zero  w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , n , prf₁) refl
    = E ∷ uᵉ , trans (trans w≡uv (List-lem₂ u)) u≡uᵉ , inj q₁ , q₁∈F₁ , suc n , lem₂ uᵉ uᵉ n q₁ [] (sym (List-lem₂ uᵉ)) prf₁
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) with lem₁ v s t n v≡st (Lᴿ⊆Lᵉᴺ e s s∈Lᴿe) t∈Lᴿeⁿ
  lem₁ w u .[] (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) | .[] , refl , ._  , q₂∈F , zero  , (refl , refl)
    = E ∷ uᵉ , trans (trans w≡uv (List-lem₂ u)) u≡uᵉ , inj q₁ , q₁∈F₁ , suc n₁ , lem₂ uᵉ uᵉ n₁ q₁ [] (sym (List-lem₂ uᵉ)) prf₁
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  q₂     , q₂∈F , suc m , prf₂ with inj q₀₁ ∈ᵈ δ (inj q₁) E | inspect (δ (inj q₁) E) (inj q₀₁)
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  init   , q₂∈F , suc m , prf₂ | true  | [ eq ]
    = ⊥-elim (¬lem₁ vᵉ m [] prf₂)
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  inj q₂ , q₂∈F , suc m , prf₂ | true  | [ eq ] with lem₄ vᵉ m q₂ prf₂
  lem₁ w u  v  (suc n) w≡uv (uᵉ , u≡uᵉ , q₁ , q₁∈F₁ , (n₁ , prf₁)) (s , t , s∈Lᴿe , t∈Lᴿeⁿ , v≡st) |  vᵉ , v≡vᵉ ,  inj q₂ , q₂∈F , suc m , prf₂ | true  | [ eq ] | vᵉ₁ , vᵉ≡Evᵉ₁ , prf₃
    = E ∷ uᵉ ++ E ∷ vᵉ₁ , Σᵉ*-lem₃ w u uᵉ v vᵉ vᵉ₁ w≡uv u≡uᵉ v≡vᵉ vᵉ≡Evᵉ₁ , inj q₂ , q₂∈F , ⊢*-lem₂ (suc n₁ , suc m , inj q₁ , E ∷ vᵉ₁ , lem₂ (uᵉ ++ E ∷ vᵉ₁) uᵉ n₁ q₁ (E ∷ vᵉ₁) refl prf₁  , (inj q₀₁ , E , vᵉ₁ , refl , (refl , eq) , prf₃))
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

  find-uᵉ : ∀ q wᵉ n q' vᵉ
            → (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , vᵉ)
            → Σᵉ*
  find-uᵉ q  wᵉ zero    .q  .wᵉ (refl , refl) = []
  find-uᵉ q ._  (suc n)  q'  vᵉ (init  , α _ , uᵉ , refl , (refl , ()) , prf₂)
  find-uᵉ q ._  (suc n)  q'  vᵉ (init  , E   , uᵉ , refl , (refl , ()) , prf₂)
  find-uᵉ q ._  (suc n)  q'  vᵉ (inj p , a   , uᵉ , refl , (refl ,  _) , prf₂) = a ∷ find-uᵉ p uᵉ n q' vᵉ prf₂

  NoLoop : ∀ q wᵉ n q' wᵉ'
           → (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , wᵉ')
           → Set
  NoLoop q ._ zero    .q  wᵉ' (refl , refl) = ⊤
  NoLoop q ._ (suc n)  q' wᵉ' (init     , α _ , _  , refl , (refl ,   ()) , prf₂)
  NoLoop q ._ (suc n)  q' wᵉ' (init     , E   , _  , refl , (refl ,   ()) , prf₂)
  NoLoop q ._ (suc n)  q' wᵉ' (inj  p   , α _ , uᵉ , refl , (refl , prf₁) , prf₂) = NoLoop p uᵉ n q' wᵉ' prf₂
  NoLoop q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) = (p ≢ q₀₁ ⊎ q ∉ᵍ F₁) × NoLoop p uᵉ n q' wᵉ' prf₂


  HasLoop : ∀ q wᵉ n q' wᵉ'
            → (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , wᵉ')
            → Set
  HasLoop q wᵉ n q' wᵉ' prf = Σ[ n₁ ∈ ℕ ] Σ[ m₁ ∈ ℕ ] Σ[ p ∈ Q₁ ] Σ[ vᵉ ∈ Σᵉ* ] Σ[ prf₁ ∈ (inj q , wᵉ) ⊢ᵏ n₁ ─ (inj p , E ∷ vᵉ) ]
                             ( NoLoop q wᵉ n₁ p (E ∷ vᵉ) prf₁ × p ∈ᵍ F₁ × (inj q₀₁ , vᵉ) ⊢ᵏ m₁ ─ (inj q' , wᵉ') × wᵉ ≡ find-uᵉ q wᵉ n₁ p (E ∷ vᵉ) prf₁ ++ (E ∷ vᵉ) × m₁ < n )
                             

  find-uᵉ-lem₁ : ∀ q wᵉ n q'
                 → (prf : (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , []))
                 → NoLoop q wᵉ n q' [] prf
                 → wᵉ ≡ find-uᵉ q wᵉ n q' [] prf
  find-uᵉ-lem₁ q .[] zero    .q  (refl  , refl) tt = refl
  find-uᵉ-lem₁ q ._  (suc n)  q' (init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂) prf₃
  find-uᵉ-lem₁ q ._  (suc n)  q' (init  , E   , uᵉ , refl , (refl ,   ()) , prf₂) prf₃
  find-uᵉ-lem₁ q ._  (suc n)  q' (inj p , α a , uᵉ , refl , (refl , prf₁) , prf₂) prf₃       = cong (λ uᵉ → α a ∷ uᵉ) (find-uᵉ-lem₁ p uᵉ n q' prf₂ prf₃)
  find-uᵉ-lem₁ q ._  (suc n)  q' (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (_ , prf₃) = cong (λ uᵉ → E   ∷ uᵉ) (find-uᵉ-lem₁ p uᵉ n q' prf₂ prf₃)
  
  lem₆ : ∀ q wᵉ n q' vᵉ
         → (prf : (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , vᵉ))
         → NoLoop q wᵉ n q' vᵉ prf
         → (q , find-uᵉ q wᵉ n q' vᵉ prf) ⊢ᵏₑ₁ n ─ (q' , [])
  lem₆ q .vᵉ zero    .q  vᵉ (refl  , refl) tt = refl , refl
  lem₆ q ._  (suc n)  q' vᵉ (init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂) prf₃
  lem₆ q ._  (suc n)  q' vᵉ (init  , E   , uᵉ , refl , (refl ,   ()) , prf₂) prf₃
  lem₆ q ._  (suc n)  q' vᵉ (inj p , α a , uᵉ , refl , (refl , prf₁) , prf₂) prf₃       = p , α a , find-uᵉ p uᵉ n q' vᵉ prf₂ , refl , (refl , prf₁) , lem₆ p uᵉ n q' vᵉ prf₂ prf₃
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₁ p≢q₀₁ , prf₃) with Q₁? p q₀₁ | q ∈ᵈ F₁ | inspect F₁ q | p ∈ᵈ δ₁ q E | inspect (δ₁ q E) p
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₁ p≢q₀₁ , prf₃) | yes p≡q₀₁ | _     | _      | _     | _       = ⊥-elim (p≢q₀₁ p≡q₀₁)
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₁ p≢q₀₁ , prf₃) | no  _     | q∈?F₁ | [ eq ] | true  | [ eq₁ ] = p , E , find-uᵉ p uᵉ n q' vᵉ prf₂ , refl , (refl , eq₁) , lem₆ p uᵉ n q' vᵉ prf₂ prf₃
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₁ p≢q₀₁ , prf₃) | no  _     | q∈?F₁ | [ eq ] | false | [ eq₁ ] = ⊥-elim (Bool-lem₈ {q∈?F₁} prf₁)
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₂ q∉F   , prf₃) with Q₁? p q₀₁ | q ∈ᵈ F₁ | inspect F₁ q | p ∈ᵈ δ₁ q E | inspect (δ₁ q E) p
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₂ q∉F   , prf₃) | _         | true  | [ eq ] | _     | _       = ⊥-elim (q∉F refl)
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl , prf₁) , prf₂) (inj₂ q∉F   , prf₃) | _         | false | [ eq ] | true  | [ eq₁ ] = p , E , find-uᵉ p uᵉ n q' vᵉ prf₂ , refl , (refl , eq₁) , lem₆ p uᵉ n q' vᵉ prf₂ prf₃
  lem₆ q ._  (suc n)  q' vᵉ (inj p , E   , uᵉ , refl , (refl ,   ()) , prf₂) (inj₂ q∉F   , prf₃) | _         | false | [ eq ] | false | [ eq₁ ]
  

  lem₅ : ∀ q wᵉ n q' wᵉ'
         → (prf : (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , wᵉ'))
         → (NoLoop q wᵉ n q' wᵉ' prf) ⊎ (HasLoop q wᵉ n q' wᵉ' prf)
  lem₅ q ._ zero    .q  wᵉ' (refl  , refl) = inj₁ tt
  lem₅ q ._ (suc n)  q' wᵉ' (init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂)
  lem₅ q ._ (suc n)  q' wᵉ' (init  , E   , uᵉ , refl , (refl ,   ()) , prf₂)
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , α a , uᵉ , refl , (refl , prf₁) , prf₂) with lem₅ p uᵉ n q' wᵉ' prf₂
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , α a , uᵉ , refl , (refl , prf₁) , prf₂) | inj₁ prf₃ = inj₁ prf₃
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , α a , uᵉ , refl , (refl , prf₁) , prf₂) | inj₂ (n₁ , m₁ , p₁ , u₁ , prf₃ , NoLoop-prf₃ , p₁∈F , prf₅ , w≡uv , m₁<n)
    = inj₂ (suc n₁ , m₁ , p₁ , u₁ , (inj p , α a , uᵉ , refl , (refl , prf₁) , prf₃) , NoLoop-prf₃ , p₁∈F , prf₅ , cong (λ u → α a ∷ u) w≡uv , {!!})
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) with Q₁? p q₀₁ | q ∈ᵈ F₁ | inspect F₁ q | p ∈ᵈ δ₁ q E | inspect (δ₁ q E) p
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | true  | [ eq ] | p∈?δqE | [ eq₁ ] with Q₁? q₀₁ q₀₁
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | true  | [ eq ] | p∈?δqE | [ eq₁ ] | yes refl = inj₂ (zero , n , q , uᵉ , (refl , refl) , tt , eq , prf₂ , refl , {!!})
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | true  | [ eq ] | p∈?δqE | [ eq₁ ] | no  p≢p  = ⊥-elim (p≢p refl)
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | false | [ eq ] | true   | [ eq₁ ] with lem₅ q₀₁ uᵉ n q' wᵉ' prf₂
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | false | [ eq ] | true   | [ eq₁ ] | inj₁ prf₃ = inj₁ (inj₂ (λ ()) , prf₃)
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl  | false | [ eq ] | true   | [ eq₁ ] | inj₂ (n₁ , m₁ , p₁ , u₁ , prf₃ , NoLoop-prf₃ , q₀₁∈F , prf₅ , w≡uv , m₁<n)
    = inj₂ (suc n₁ , m₁ , p₁ , u₁ ,(inj q₀₁ , E , uᵉ , refl , (refl , Bool-lem₆ (q₀₁ ∈ᵈ δ₁ q E) (q ∈ᵈ F₁ ∧ decEqToBool Q₁? q₀₁ q₀₁) eq₁) , prf₃) , (inj₂ (∈ᵍ-lem₂ {Q₁} {q} {F₁} eq) , NoLoop-prf₃) , q₀₁∈F , prf₅ , cong (λ u → E ∷ u) w≡uv , {!!})
  lem₅ q ._ (suc n)  q' wᵉ' (inj .q₀₁ , E   , uᵉ , refl , (refl ,   ()) , prf₂) | yes refl  | false | [ eq ] | false  | [ eq₁ ]
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) | no  p≢q₀₁ | q∈?F₁ | [ eq ] | true   | [ eq₁ ] with lem₅ p uᵉ n q' wᵉ' prf₂
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) | no  p≢q₀₁ | q∈?F₁ | [ eq ] | true   | [ eq₁ ] | inj₁ prf₃ = inj₁ (inj₁ p≢q₀₁ , prf₃)
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) | no  p≢q₀₁ | q∈?F₁ | [ eq ] | true   | [ eq₁ ] | inj₂ (n₁ , m₁ , p₁ , u₁ , prf₃ , NoLoop-prf₃ , p₁∈F , prf₅ , w≡uv , m₁<n)
    = inj₂ (suc n₁ , m₁ , p₁ , u₁ ,(inj p , E , uᵉ , refl , (refl , Bool-lem₆ (p ∈ᵈ δ₁ q E) (q ∈ᵈ F₁ ∧ decEqToBool Q₁? p q₀₁) eq₁) , prf₃) , (inj₁ p≢q₀₁ , NoLoop-prf₃) , p₁∈F , prf₅ , cong (λ u → E ∷ u) w≡uv , {!!})
  lem₅ q ._ (suc n)  q' wᵉ' (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) | no  p≢q₀₁ | q∈?F₁ | [ eq ] | false  | [ eq₁ ] = ⊥-elim (Bool-lem₈ {q∈?F₁} prf₁)

  NoLoop-lem₁ : ∀ w wᵉ n q vᵉ
                → w ≡ toΣ* wᵉ
                → inj q ∈ᵍ F
                → (prf : (inj q₀₁ , wᵉ) ⊢ᵏ n ─ (inj q , vᵉ))
                → NoLoop q₀₁ wᵉ n q vᵉ prf
                → toΣ* (find-uᵉ q₀₁ wᵉ n q vᵉ prf) ∈ Lᵉᴺ nfa₁
  NoLoop-lem₁ w wᵉ n q vᵉ w≡wᵉ q∈F prf NoLoop-prf = uᵉ , refl , q , q∈F , n , lem₆ q₀₁ wᵉ n q vᵉ prf NoLoop-prf
   where
    uᵉ : Σᵉ*
    uᵉ = find-uᵉ q₀₁ wᵉ n q vᵉ prf

  HasLoop-lem₁ : ∀ w wᵉ n q
                 → w ≡ toΣ* wᵉ
                 → inj q ∈ᵍ F
                 → (prf : (inj q₀₁ , wᵉ) ⊢ᵏ n ─ (inj q , []))
                 → HasLoop q₀₁ wᵉ n q [] prf
                 → Σ[ n₁ ∈ ℕ ] w ∈ Lᴿ e ^ n₁
  HasLoop-lem₁ w wᵉ n q w≡wᵉ q∈F prf (n₁ , m₁ , p , vᵉ , prf₁ , NoLoop-prf₁ , p∈F , prf₃ , w≡uv , m₁<n) with lem₅ q₀₁ vᵉ m₁ q [] prf₃
  HasLoop-lem₁ w wᵉ n q w≡wᵉ q∈F prf (n₁ , m₁ , p , vᵉ , prf₁ , NoLoop-prf₁ , p∈F , prf₃ , w≡uv , m₁<n) | inj₁ NoLoop-prf₃
    = 2 , toΣ* uᵉ , toΣ* vᵉ , u∈Lᴿe , v∈Lᴿe¹ , trans w≡wᵉ (Σᵉ*-lem₄ wᵉ uᵉ vᵉ w≡uv) --
    where
     uᵉ : Σᵉ*
     uᵉ = find-uᵉ q₀₁ wᵉ n₁ p (E ∷ vᵉ) prf₁
     find-u≡v : find-uᵉ q₀₁ vᵉ m₁ q [] prf₃ ≡ vᵉ
     find-u≡v = sym (find-uᵉ-lem₁ q₀₁ vᵉ m₁ q prf₃ NoLoop-prf₃)
     u∈Lᴿe : toΣ* uᵉ ∈ Lᴿ e
     u∈Lᴿe = Lᴿ⊇Lᵉᴺ e (toΣ* uᵉ) (NoLoop-lem₁ w wᵉ n₁ p (E ∷ vᵉ) w≡wᵉ p∈F prf₁ NoLoop-prf₁)
     v∈Lᴿe¹ : toΣ* vᵉ ∈ Lᴿ e ^ 1
     v∈Lᴿe¹ = toΣ* vᵉ , [] , Lᴿ⊇Lᵉᴺ e (toΣ* vᵉ) (subst (λ v → v ∈ Lᵉᴺ nfa₁) (cong toΣ* find-u≡v) (NoLoop-lem₁ (toΣ* vᵉ) vᵉ m₁ q [] refl q∈F prf₃ NoLoop-prf₃)) , refl , sym (List-lem₂ (toΣ* vᵉ))
  HasLoop-lem₁ w wᵉ n q w≡wᵉ q∈F prf (n₁ , m₁ , p , vᵉ , prf₁ , NoLoop-prf₁ , p∈F , prf₃ , w≡uv , m₁<n) | inj₂ HasLoop-prf₃ = undefined --with HasLoop-lem₁ (toΣ* vᵉ) vᵉ m₁ q refl q∈F prf₃ HasLoop-prf₃
  --HasLoop-lem₁ w wᵉ n q w≡wᵉ q∈F prf (n₁ , m₁ , p , vᵉ , prf₁ , NoLoop-prf₁ , p∈F , prf₃ , w≡uv , m₁<n) | inj₂ HasLoop-prf₃ | n₂ , vᵉ∈Lᴿⁿ² = ?
  

  lem₄ : ∀ w wᵉ q n
         → w ≡ toΣ* wᵉ
         → inj q ∈ᵍ F
         → (inj q₀₁ , wᵉ) ⊢ᵏ n ─ (inj q , [])
         → Σ[ n₁ ∈ ℕ ] w ∈ Lᴿ e ^ n₁
  lem₄ w wᵉ q n w≡wᵉ q∈F prf with lem₅ q₀₁ wᵉ n q [] prf
  ... | inj₁ prf₁ = suc zero , w , [] , Lᴿ⊇Lᵉᴺ e w (subst (λ w → w ∈ Lᵉᴺ nfa₁) find-u≡w (NoLoop-lem₁ w wᵉ n q [] w≡wᵉ q∈F prf prf₁)) , refl , sym (List-lem₂ w)
      where
       find-u≡w : toΣ* (find-uᵉ q₀₁ wᵉ n q [] prf) ≡ w
       find-u≡w = trans (sym (cong toΣ* (find-uᵉ-lem₁ q₀₁ wᵉ n q prf prf₁))) (sym w≡wᵉ)
  ... | inj₂ prf₁ = HasLoop-lem₁ w wᵉ n q w≡wᵉ q∈F prf prf₁
  

  lem₃ : ∀ wᵉ n q
         → (init , wᵉ) ⊢ᵏ suc n ─ (inj q , [])
         → Σ[ uᵉ ∈ Σᵉ* ] ( wᵉ ≡ E ∷ uᵉ × (inj q₀₁ , uᵉ) ⊢ᵏ n ─ (inj q , []) )
  lem₃ ._ n q (init , α _ , uᵉ , refl , (refl ,    ()) , prf₂)
  lem₃ ._ n q (init , E   , uᵉ , refl , (refl ,    ()) , prf₂)
  lem₃ ._ n q (inj  p   , α _ , uᵉ , refl , (refl ,   ()) , prf₂)
  lem₃ ._ n q (inj  p   , E   , uᵉ , refl , (refl , prf₁) , prf₂) with Q₁? p q₀₁
  lem₃ ._ n q (inj .q₀₁ , E   , uᵉ , refl , (refl , prf₁) , prf₂) | yes refl = uᵉ , refl , prf₂
  lem₃ ._ n q (inj  p   , E   , uᵉ , refl , (refl ,   ()) , prf₂) | no  p≢q₀₁


  lem₂ : ∀ w wᵉ q n
         → w ≡ toΣ* wᵉ
         → inj q ∈ᵍ F
         → (init , wᵉ) ⊢ᵏ suc n ─ (inj q , [])
         → Σ[ n₁ ∈ ℕ ] w ∈ Lᴿ e ^ n₁
  lem₂ w wᵉ q n w≡wᵉ q∈F prf with lem₃ wᵉ n q prf
  ... | wᵉ₁ , wᵉ≡Ewᵉ₁ , prf₁ with lem₄ (toΣ* wᵉ₁) wᵉ₁ q n refl q∈F prf₁
  ...   | n₁ , w₁∈Lᴿeⁿ¹ = n₁ , subst (λ w → w ∈ ((Lᴿ e) ^ n₁)) (sym (trans w≡wᵉ (cong toΣ* wᵉ≡Ewᵉ₁))) w₁∈Lᴿeⁿ¹


  lem₁ : ∀ w
         → w ∈ Lᵉᴺ nfa
         → w ∈ Lᴿ (e *)
  lem₁ .[] (.[] , refl , .init  , q∈F , zero  , (refl , refl)) = zero , refl
  lem₁  w  ( wᵉ , w≡wᵉ ,  init  , q∈F , suc n , prf)           = ⊥-elim (¬lem₁ wᵉ n [] prf)
  lem₁  w  ( wᵉ , w≡wᵉ ,  inj q , q∈F , suc n , prf)           = lem₂ w wᵉ q n w≡wᵉ q∈F prf
