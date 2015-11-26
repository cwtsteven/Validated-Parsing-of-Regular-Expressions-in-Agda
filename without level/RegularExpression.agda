module RegularExpression (Σ : Set) where

open import Language Σ renaming (Ø to ø)

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

-- Language denoted by regular expression
Lᴿ : RegExp → Languages
Lᴿ Ø         = ø
Lᴿ ε         = ⟦ε⟧
Lᴿ (σ a)     = ⟦ a ⟧
Lᴿ (e₁ ∣ e₂) = Lᴿ e₁ ⋃ Lᴿ e₂
Lᴿ (e₁ ∙ e₂) = Lᴿ e₁ • Lᴿ e₂
Lᴿ (e *)     = (Lᴿ e) ⋆
