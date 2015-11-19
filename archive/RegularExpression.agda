open import Util
module RegularExpression (Σ : Set)(dec : DecEq Σ)  where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool
open import Data.Nat
open import Subset.DecidableSubset renaming (Ø to ø)

Σ* : Set
Σ* = List Σ

infix 10 _∣_
infix 11 _∙_
infix 12 _*
data RegExp : Set where
 Ø   : RegExp
 ε   : RegExp
 σ   : Σ → RegExp
 _∣_ : RegExp → RegExp → RegExp
 _∙_ : RegExp → RegExp → RegExp
 _*  : RegExp → RegExp


mutual
 Lᴿ : RegExp → DecSubset Σ*
 Lᴿ Ø = ø
 Lᴿ ε []       = true
 Lᴿ ε (x ∷ xs) = false
 Lᴿ (σ a) [] = false
 Lᴿ (σ a) (x ∷ xs) with dec a x
 Lᴿ (σ a) (.a ∷ [])     | yes refl = true
 Lᴿ (σ a) (.a ∷ y ∷ xs) | yes refl = false
 Lᴿ (σ a) (x ∷ xs)      | no  _    = false
 Lᴿ (e₁ ∣ e₂) = Lᴿ e₁ ⋃ Lᴿ e₂
 Lᴿ (e₁ ∙ e₂) w = ∃e₁e₂w₁w₂ e₁ e₂ [] w
 --Lᴿ (e *) w = ∃n (length w) e w
 Lᴿ (e *) [] = true
 Lᴿ (e * ) (x ∷ xs) = ∃e₁e₂w₁w₂ e (e *) (x ∷ []) xs
{-
 infix 13 _^_
 _^_ : RegExp → ℕ → RegExp
 e ^ zero    = ε
 e ^ (suc n) = e ∙ e ^ n

 ∃n : (n : ℕ)(e : RegExp) → DecSubset Σ*
 ∃n zero    e = λ w → w ∈ Lᴿ ε
 ∃n (suc n) e = Lᴿ (e ^ (suc n)) ⋃ ∃n n e
-}
 ∃e₁e₂w₁w₂ : (e₁ e₂ : RegExp)(w₁ w₂ : Σ*) → Bool
 ∃e₁e₂w₁w₂ e₁ e₂ w₁ w₂ with (Lᴿ e₁ w₁) ∧ (Lᴿ e₂ w₂)
 ∃e₁e₂w₁w₂ e₁ e₂ w₁ w₂       | true  = true
 ∃e₁e₂w₁w₂ e₁ e₂ w₁ []       | false = false
 ∃e₁e₂w₁w₂ e₁ e₂ w₁ (x ∷ xs) | false = ∃e₁e₂w₁w₂ e₁ e₂ (w₁ ∷ʳ x) xs
