module RegularExpression (Σ : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (Σ)
open import Data.Nat

open import Util
open import Subset hiding (⟦_⟧) renaming (Ø to ø)
open import Language Σ

infix 11 _∣_
infix 12 _∙_
infix 13 _*
data RegExp : Set where
 Ø   : RegExp 
 ε   : RegExp 
 σ   : Σ → RegExp
 _∣_ : RegExp → RegExp → RegExp
 _∙_ : RegExp → RegExp → RegExp
 _*  : RegExp → RegExp
 
infix 12 _•_
-- set of concatenation of words
_•_ : Language → Language → Language
L₁ • L₂ = λ w → Σ[ w₁ ∈ Σ* ] Σ[ w₂ ∈ Σ* ] (w₁ ∈ L₁ × w₂ ∈ L₂ × w ≡ w₁ ++ w₂)

infix 6 _^_
_^_ : Language → ℕ → Language
_^_ L zero    = ⟦ε⟧
_^_ L (suc n) = L • (L ^ n)

infix 13 _⋆
-- set of closure
_⋆ : Language → Language
L ⋆ = λ w → Σ[ n ∈ ℕ ] w ∈ (L ^ n) 

-- Language denoted by regular expression
Lᴿ : RegExp → Language
Lᴿ Ø         = ø
Lᴿ ε         = ⟦ε⟧
Lᴿ (σ a)     = ⟦ a ⟧
Lᴿ (e₁ ∣ e₂) = Lᴿ e₁ ⋃ Lᴿ e₂
Lᴿ (e₁ ∙ e₂) = Lᴿ e₁ • Lᴿ e₂
Lᴿ (e *)     = (Lᴿ e) ⋆
