{-
  from : https://bitbucket.org/jozefg/regex/src/d38d72b9d5078a527b38c37a275e244053dec451/Split.agda?at=master&fileviewer=file-view-default
-}

module Split where

open import Data.List                             using (List ; _∷_ ; [] ; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary                      using (Dec; yes; no)
open import Data.Empty                            using (⊥)

data Split {A : Set} : List A → List A → List A → Set where
  nil  : (s : List A) → Split s [] s
  cons : (c : A)(s : List A){s1 s2 : List A}
       → Split s s1 s2
       → Split (c ∷ s) (c ∷ s1) s2

module SplitCorrect where
  sound : {A : Set}(l l₁ l₂ : List A) → Split l l₁ l₂ → l ≡ (l₁ ++ l₂)
  sound l .[] .l (nil .l) = refl
  sound .(c ∷ s) (.c ∷ s₁) s2 (cons c s sp) rewrite sound _ _ _ sp = refl

  complete : {A : Set}(l l₁ l₂ : List A) → l ≡ (l₁ ++ l₂) → Split l l₁ l₂
  complete l [] .l refl = nil l
  complete ._ (x ∷ l₁) l₂ refl = cons x (l₁ ++ l₂) (complete _ _ _ refl)

module SplitDec where
  SplitProp : {A : Set} → List A → Set₁
  SplitProp s = (s₁ s₂ : List _) → Split s s₁ s₂ → Set

  SplitDec : {A : Set}{s : List A} → SplitProp s → Set
  SplitDec {s = s} P = (s₁ s₂ : List _)(sp : Split s s₁ s₂) → Dec (P s₁ s₂ sp)

  data HasSplit {A : Set}(s : List A)(P : SplitProp s) : Set where
    exists : (s₁ s₂ : List A)(sp : Split s s₁ s₂)
           → P s₁ s₂ sp
           → HasSplit s P
  private
    ShiftOver : {A : Set}(s : List A)(c : A) → SplitProp (c ∷ s) → SplitProp s
    ShiftOver s c P s₁ s₂ sp = P (c ∷ s₁) s₂ (cons c s sp)

    shiftOverDec : {A : Set}{s : List A}(c : A){P : SplitProp (c ∷ s)}
                 → (SplitDec P) → (SplitDec (ShiftOver s c P))
    shiftOverDec c dec s₁ s₂ sp = dec (c ∷ s₁) s₂ (cons c _ sp)

  decHasSplit : {A : Set}(s : List A){P : SplitProp s}
              → (SplitDec P) → Dec (HasSplit s P)
  decHasSplit [] decP with decP [] [] (nil [])
  decHasSplit [] decP | yes p = yes (exists [] [] (nil []) p)
  decHasSplit [] decP | no ¬p = no contra
    where contra : HasSplit [] _ → ⊥
          contra (exists .[] .[] (nil .[]) x) = ¬p x
  decHasSplit (x ∷ s) decP with decHasSplit s (shiftOverDec x decP) | decP _ _ (nil (x ∷ s))
  decHasSplit (x ∷ s) decP | yes p | yes p₁ = yes (exists [] (x ∷ s) (nil (x ∷ s)) p₁)
  decHasSplit (x ∷ s) decP | yes (exists s₁ s₂ sp x₁) | no ¬p = yes (exists (x ∷ s₁) s₂ (cons x s sp) x₁)
  decHasSplit (x ∷ s) decP | no ¬p | yes p = yes (exists [] (x ∷ s) (nil (x ∷ s)) p)
  decHasSplit (x ∷ s) decP | no ¬p | no ¬p₁ = no contra
    where contra : HasSplit (x ∷ s) _ → ⊥
          contra (exists .[] .(x ∷ s) (nil ._) x₁) = ¬p₁ x₁
          contra (exists (.x ∷ s₁) s₂ (cons .x .s sp) x₁) = ¬p (exists s₁ s₂ sp x₁)

open SplitDec public
