module Language (Σ : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (Σ)
open import Data.Nat

open import Util
open import Subset renaming (Ø to ø ; ⟦_⟧ to ⟦_⟧₁ ; _⋃_ to _⊎_)

open ≡-Reasoning

-- set of words over Σ
Σ* : Set
Σ* = List Σ

-- Language as a subset of Σ*
Languages : Set₁
Languages = Powerset Σ*

-- null set
Ø : Languages
Ø = ø

-- set of empty word
⟦ε⟧ : Languages
⟦ε⟧ = ⟦ [] ⟧₁

-- set of single alphabet
⟦_⟧ : Σ → Languages
⟦ a ⟧ = ⟦ a ∷ [] ⟧₁

infix 11 _⋃_
-- union
_⋃_ : Languages → Languages → Languages
as ⋃ bs = as ⊎ bs

infix 12 _•_
-- set of concatenation of words
_•_ : Languages → Languages → Languages
L₁ • L₂ = λ w → Σ[ w₁ ∈ Σ* ] Σ[ w₂ ∈ Σ* ] (w₁ ∈ L₁ × w₂ ∈ L₂ × w ≡ w₁ ++ w₂)

infix 6 _^_
_^_ : Languages → ℕ → Languages
_^_ L zero    = ⟦ε⟧
_^_ L (suc n) = L • (L ^ n)

infix 13 _⋆
-- set of closure
_⋆ : Languages → Languages
L ⋆ = λ w → Σ[ n ∈ ℕ ] w ∈ (L ^ n) 

-- set of alphabet with ε
data Σᵉ : Set where
 E : Σᵉ
 α : Σ → Σᵉ

-- set of words over Σᵉ
Σᵉ* : Set
Σᵉ* = List Σᵉ

-- transform a word over Σ to a word over Σᵉ
toΣᵉ* : Σ* → Σᵉ*
toΣᵉ* = Data.List.map α


Σᵉ*-lem₁ : ∀ w w₁ w₂ w' w₁' w₂' → toΣᵉ* w ≡ w' → toΣᵉ* w₁ ≡ w₁' → toΣᵉ* w₂ ≡ w₂' → w ≡ w₁ ++ w₂ → w' ≡ w₁' ++ w₂'
Σᵉ*-lem₁ w w₁ w₂ w' w₁' w₂' w≡w' w₁≡w₁' w₂≡w₂' w≡w₁w₂ = begin
                                                        w'                   ≡⟨ sym w≡w' ⟩
                                                        toΣᵉ* w              ≡⟨ cong toΣᵉ* w≡w₁w₂ ⟩
                                                        toΣᵉ* (w₁ ++ w₂)     ≡⟨ List-lem₃ α w₁ w₂  ⟩
                                                        toΣᵉ* w₁ ++ toΣᵉ* w₂ ≡⟨ cong (λ w → w ++ toΣᵉ* w₂) w₁≡w₁' ⟩
                                                        w₁' ++ toΣᵉ* w₂      ≡⟨ cong (λ w → w₁' ++ w) w₂≡w₂' ⟩
                                                        w₁' ++ w₂'
                                                        ∎

{-
DecEq-Σᵉ : DecEq Σᵉ
DecEq-Σᵉ E     E      = yes refl
DecEq-Σᵉ E     (α  _) = no (λ ())
DecEq-Σᵉ (α a) E      = no (λ ())
DecEq-Σᵉ (α a) (α  b) with dec a b
DecEq-Σᵉ (α a) (α .a) | yes refl = yes refl
DecEq-Σᵉ (α a) (α  b) | no ¬a≡b  = no  (λ p → ¬σa≡σb ¬a≡b p)
 where
  lem : {a b : Σ} → α a ≡ α b → a ≡ b
  lem refl = refl
  ¬σa≡σb : ¬ (a ≡ b) → ¬ (α a ≡ α b)
  ¬σa≡σb ¬a≡b σa≡σb = ¬a≡b (lem σa≡σb)
-}
