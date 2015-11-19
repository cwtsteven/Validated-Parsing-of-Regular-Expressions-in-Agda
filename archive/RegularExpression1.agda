{-
  Some parts in the Concatenation and Kleen star cases are written with the help from:
  https://bitbucket.org/jozefg/regex/src/d38d72b9d507?at=master
-}

module RegularExpression1 where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary
open import Data.Bool

open import Split
open import Util


infix 10 _∣_
infix 11 _∙_
infix 12 _*
data RegExp (Σ : Set) : Set where
 Ø   : RegExp Σ
 ε   : RegExp Σ
 σ   : Σ → RegExp Σ
 _∣_ : RegExp Σ → RegExp Σ → RegExp Σ
 _∙_ : RegExp Σ → RegExp Σ → RegExp Σ
 _*  : RegExp Σ → RegExp Σ
 

module RegExp-Properties (Σ : Set) where
         
 infix 0 _⇨_
 data _⇨_ : RegExp Σ → Σ* → Set where
  empty    : ε ⇨ []
  alphabet : ∀ a → (σ a) ⇨ a ∷ []
  unionˡ   : ∀ {e₁ e₂ w} → e₁ ⇨ w → e₁ ∣ e₂ ⇨ w
  unionʳ   : ∀ {e₁ e₂ w} → e₂ ⇨ w → e₁ ∣ e₂ ⇨ w
  con      : ∀ {e₁ e₂ w w₁ w₂} → Split w w₁ w₂ → e₁ ⇨ w₁ → e₂ ⇨ w₂ → e₁ ∙ e₂ ⇨ w
  kleenᵉ   : ∀ {e} → e * ⇨ []
  kleen    : ∀ {e w w₁ w₂} → Split w w₁ w₂ → e ⇨ w₁ → e * ⇨ w₂ → e * ⇨ w

 data ∙-Derive (e₁ e₂ : RegExp Σ)(w₁ w₂ : Σ*) : Set where
  ∙-derive : e₁ ⇨ w₁ → e₂ ⇨ w₂ → ∙-Derive e₁ e₂ w₁ w₂

 ∙-fst : ∀ {e₁ e₂ w₁ w₂} → ∙-Derive e₁ e₂ w₁ w₂ → e₁ ⇨ w₁
 ∙-fst (∙-derive e₁⇨w₁ _) = e₁⇨w₁

 ∙-snd : ∀ {e₁ e₂ w₁ w₂} → ∙-Derive e₁ e₂ w₁ w₂ → e₂ ⇨ w₂
 ∙-snd (∙-derive _ e₂⇨w₂) = e₂⇨w₂

 data *-Derive (e : RegExp Σ)(w₁ w₂ : Σ*) : Set where
  *-derive : e ⇨ w₁ → e * ⇨ w₂ → *-Derive e w₁ w₂

 *-fst : ∀ {e w₁ w₂} → *-Derive e w₁ w₂ → e ⇨ w₁
 *-fst (*-derive e⇨w₁ _) = e⇨w₁
 
 *-snd : ∀ {e w₁ w₂} → *-Derive e w₁ w₂ → e * ⇨ w₂
 *-snd (*-derive _ e*⇨w₂) = e*⇨w₂ 

 mutual
  {-# NO_TERMINATION_CHECK #-}
  ∙-Derive? : (e₁ e₂ : RegExp Σ)(w : Σ*){eq? : DecEq Σ}(w₁ w₂ : Σ*)(sp : Split w w₁ w₂) → Dec (∙-Derive e₁ e₂ w₁ w₂)
  ∙-Derive? e₁ e₂ s {eq?} w₁ w₂ sp with (e₁ ⇨? w₁) {eq?} | (e₂ ⇨? w₂) {eq?}
  ... | yes e₁⇨w₁ | yes e₂⇨w₂ = yes (∙-derive e₁⇨w₁ e₂⇨w₂)
  ... | _         | no ¬e₂⇨w₂ = no (λ p → ¬e₂⇨w₂ (∙-snd p))
  ... | no ¬e₁⇨w₁ | _         = no (λ p → ¬e₁⇨w₁ (∙-fst p))

  *-Derive? : (e : RegExp Σ)(w : Σ*){eq? : DecEq Σ}(w₁ w₂ : Σ*)(sp : Split w w₁ w₂) → Dec (*-Derive e w₁ w₂)
  *-Derive? e w {eq?} w₁ w₂ sp with (e ⇨? w₁) {eq?} | (e * ⇨? w₂) {eq?}
  ... | yes e⇨w₁ | yes e*⇨w₂ = yes (*-derive e⇨w₁ e*⇨w₂)
  ... | _        | no ¬e*⇨w₂ = no (λ p → ¬e*⇨w₂ (*-snd p))
  ... | no ¬e⇨w₁ | _         = no (λ p → ¬e⇨w₁ (*-fst p))

  infix 0 _⇨?_
  _⇨?_ : ∀ e w → {dec : DecEq Σ} → Dec (e ⇨ w)
  -- null set
  Ø ⇨? _        = no (λ ())
  -- ε
  ε ⇨? []       = yes empty
  ε ⇨? (x ∷ xs) = no (λ ())
  -- single alphabet
  σ a ⇨? []     = no (λ ())
  (σ a ⇨? x ∷ xs) {eq?} with eq? a x
  (σ a ⇨? .a ∷ []) {eq?}      | yes refl = yes (alphabet a)
  (σ a ⇨? .a ∷ x' ∷ xs) {eq?} | yes refl = no (λ ())
  (σ a ⇨?  x ∷ xs) {eq?}      | no a≢b   = no (λ p → ¬σa⇨w a≢b p)
    where
      ¬σa⇨w : {a b : Σ}{w : Σ*} → ¬ (a ≡ b) → ¬ (σ a ⇨ (b ∷ w))
      ¬σa⇨w ¬a≡b (alphabet a) = ¬a≡b refl
  -- union
  (e₁ ∣ e₂ ⇨? w) {eq?} with (e₁ ⇨? w) {eq?} | (e₂ ⇨? w) {eq?}
  ... | yes e₁⇨w  | _        = yes (unionˡ e₁⇨w)
  ... | _         | yes e₂⇨w = yes (unionʳ e₂⇨w)
  ... | no  ¬e₁⇨w | no ¬e₂⇨w = no ¬e₁∣e₂⇨w
    where
      ¬e₁∣e₂⇨w : ¬ (e₁ ∣ e₂ ⇨ w)
      ¬e₁∣e₂⇨w (unionˡ e₁⇨w) = ¬e₁⇨w e₁⇨w
      ¬e₁∣e₂⇨w (unionʳ e₂⇨w) = ¬e₂⇨w e₂⇨w
  -- concatenation
  (e₁ ∙ e₂ ⇨? w) {eq?} with decHasSplit w (∙-Derive? e₁ e₂ w {eq?})
  ... | yes (exists w₁ w₂ sp (∙-derive e₁⇨w₁ e₂⇨w₂)) = yes (con sp e₁⇨w₁ e₂⇨w₂)
  ... | no ¬p                                         = no ¬e₁∙e₂⇨w
    where
      ¬e₁∙e₂⇨w : ¬ (e₁ ∙ e₂ ⇨ w)
      ¬e₁∙e₂⇨w (con {.e₁} {.e₂} {.w} {w₁} {w₂} sp e₁⇨w₁' e₂⇨w₂') = ¬p (exists w₁ w₂ sp (∙-derive e₁⇨w₁' e₂⇨w₂'))
  -- kleen star
  e * ⇨? []       = yes kleenᵉ
  (e * ⇨? (x ∷ xs)) {eq?} with decHasSplit (x ∷ xs) (*-Derive? e (x ∷ xs) {eq?})
  ... | yes (exists w₁ w₂ sp (*-derive e⇨w₁ e*⇨w₂)) = yes (kleen sp e⇨w₁ e*⇨w₂)
  ... | no ¬p                                        = no ¬e*⇨w
    where
      ¬e*⇨w : ¬ (e * ⇨ (x ∷ xs))
      ¬e*⇨w (kleen {.e} {.(x ∷ xs)} {w₁} {w₂} sp e⇨w₁' e*⇨w₂') = ¬p (exists w₁ w₂ sp (*-derive e⇨w₁' e*⇨w₂'))

 language-Reg : {eq? : DecEq Σ} → RegExp Σ → DecSubset Σ*
 language-Reg {eq?} e w with (e ⇨? w) {eq?}
 ... | yes _ = true
 ... | no _  = false
