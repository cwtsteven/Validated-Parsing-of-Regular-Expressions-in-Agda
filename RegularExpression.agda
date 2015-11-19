open import Util

module RegularExpression (Σ : Set) (dec : DecEq Σ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Subset renaming (Ø to ø)

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
 

infix 11 _•_
_•_ : Subset Σ* → Subset Σ* → Subset Σ*
A • B = λ w → Σ[ w₁ ∈ Σ* ] Σ[ w₂ ∈ Σ* ] (w₁ ∈ A × w₂ ∈ B × w ≡ w₁ ++ w₂)


infix 6 _^_
_^_ : Subset Σ* → ℕ → Subset Σ*
_^_ A zero  = λ w → w ≡ []
_^_ A (suc n) = A • (A ^ n)


_⋆ : Subset Σ* → Subset Σ*
A ⋆ = λ w → Σ[ n ∈ ℕ ] w ∈ (A ^ n) 


Lᴿ : RegExp → Subset Σ*
Lᴿ Ø         = ø
Lᴿ ε         = λ w → w ≡ []
Lᴿ (σ a)     = λ w → w ≡ a ∷ []
Lᴿ (e₁ ∣ e₂) = Lᴿ e₁ ⋃ Lᴿ e₂
Lᴿ (e₁ ∙ e₂) = Lᴿ e₁ • Lᴿ e₂
Lᴿ (e *)     = (Lᴿ e) ⋆

{-
mutual
 Dec-Lᴿ : ∀ regex w → Dec (w ∈ Lᴿ regex)
 Dec-Lᴿ Ø     w        = no (λ ())
 Dec-Lᴿ ε     []       = yes refl
 Dec-Lᴿ ε     (x ∷ xs) = no (λ ())
 Dec-Lᴿ (σ a) []       = no (λ ())
 Dec-Lᴿ (σ a) ( x ∷ []) with dec x a
 Dec-Lᴿ (σ a) (.a ∷ []) | yes refl = yes refl
 Dec-Lᴿ (σ a) ( x ∷ []) | no  ¬a≡x = no (lem₁ {x} {a} ¬a≡x) 
  where
   lem₂ : {a b : Σ} → a ∷ [] ≡ b ∷ [] → a ≡ b
   lem₂ refl = refl
   lem₁ : {a b : Σ} → a ≢ b → a ∷ [] ≢ b ∷ []
   lem₁ a≢b a[]≡b[] = a≢b (lem₂ a[]≡b[])
 Dec-Lᴿ (σ a) ( x ∷ y ∷ xs) = no (λ ())
 Dec-Lᴿ (e₁ ∣ e₂) w with Dec-Lᴿ e₁ w | Dec-Lᴿ e₂ w
 ... | yes w∈Lᴿe₁ | _          = yes (inj₁ w∈Lᴿe₁)
 ... | _          | yes w∈Lᴿe₂ = yes (inj₂ w∈Lᴿe₂)
 ... | no  w∉Lᴿe₁ | no  w∉Lᴿe₂ = no lem₁
  where
   lem₁ : ¬ (w ∈ Lᴿ (e₁ ∣ e₂))
   lem₁ (inj₁ w∈Lᴿe₁) = w∉Lᴿe₁ w∈Lᴿe₁
   lem₁ (inj₂ w∈Lᴿe₂) = w∉Lᴿe₂ w∈Lᴿe₂
 Dec-Lᴿ (e₁ ∙ e₂) w = Dec-Lᴿe₁∙e₂ e₁ e₂ w [] w refl
 Dec-Lᴿ (e *) w     = undefined


 Dec-Lᴿe₁∙e₂ : (e₁ e₂ : RegExp)(w w₁ w₂ : Σ*) → w ≡ w₁ ++ w₂ → Dec (w ∈ Lᴿ (e₁ ∙ e₂))
 Dec-Lᴿe₁∙e₂ e₁ e₂ w w₁ w₂ prf with Dec-Lᴿ e₁ w₁ | Dec-Lᴿ e₂ w₂
 Dec-Lᴿe₁∙e₂ e₁ e₂ w  w₁ w₂       prf | yes (w₁∈Lᴿe₁) | yes (w₂∈Lᴿe₂) = yes (w₁ , w₂ , w₁∈Lᴿe₁ , w₂∈Lᴿe₂ , prf)
 Dec-Lᴿe₁∙e₂ e₁ e₂ w  w₁ []       prf | no  (w₁∉Lᴿe₁) | _             = no lem₁
  where
   lem₁ : ¬ (w ∈ Lᴿ (e₁ ∙ e₂))
   lem₁ (w₁' , w₂' , w₁∈Lᴿe₁ , w₂∈Lᴿe₂ , prf) = undefined -- w₁∉Lᴿe₁ w₁∈Lᴿe₁
 Dec-Lᴿe₁∙e₂ e₁ e₂ w  w₁ []       prf | _             | no  (w₂∉Lᴿe₂) = no lem₁
  where
   lem₁ : ¬ (w ∈ Lᴿ (e₁ ∙ e₂))
   lem₁ (w₁ , w₂ , w₁∈Lᴿe₁ , w₂∈Lᴿe₂ , prf) = undefined --w₂∉Lᴿe₂ w₂∈Lᴿe₂
 Dec-Lᴿe₁∙e₂ e₁ e₂ w  w₁ (x ∷ xs) prf | _             | _           = Dec-Lᴿe₁∙e₂ e₁ e₂ w (w₁ ∷ʳ x) xs (trans prf (List-lem₁ x w₁ xs))

-}
