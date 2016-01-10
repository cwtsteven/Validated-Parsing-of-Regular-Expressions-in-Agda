{-
  This module contains some miscellaneous definitions and proofs that will be used.

  Steven Cheung 2015.
  Version 9-12-2015
-}
module Util where

open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Nat

open ≡-Reasoning

--postulate undefined : ∀ {α} → {A : Set α} → A


-- Decidable Equality
DecEq : ∀ {ℓ} → (A : Set ℓ) → Set ℓ
DecEq A = (x y : A) → Dec (x ≡ y)

decEqToBool : {A : Set} → DecEq A → (x y : A) → Bool
decEqToBool dec x  y with dec x y
decEqToBool dec x .x | yes refl = true
decEqToBool dec x  y | no  x≢y  = false


-- Logic
infix 0 _⇔_
_⇔_ : ∀ {α} → Set α → Set α → Set α
P ⇔ Q = (P → Q) × (Q → P)


-- List lemma
tail : {A : Set} → List A → List A
tail []       = []
tail (x ∷ xs) = xs

List-lem₁ : {A : Set}{x y : A}{xs ys : List A}
            → x ≢ y
            → x ∷ xs ≢ y ∷ ys
List-lem₁ x≢y refl = x≢y refl


List-lem₂ : {A : Set}(xs : List A)
            → xs ++ [] ≡ xs
List-lem₂ []       = refl
List-lem₂ (x ∷ xs) = cong (λ xs → x ∷ xs) (List-lem₂ xs)

List-lem₃ : {A : Set}(xs ys zs : List A)
            → (xs ++ ys) ++ zs ≡  xs ++ ys ++ zs
List-lem₃ []       ys zs = refl
List-lem₃ (x ∷ xs) ys zs = cong (λ xs → x ∷ xs) (List-lem₃ xs ys zs)

List-lem₄ : {A : Set}(ws us vs xs ys : List A)
            → ws ≡ us ++ vs
            → us ≡ xs ++ ys
            → ws ≡ xs ++ ys ++ vs
List-lem₄ ._ ._ vs xs ys refl refl = List-lem₃ xs ys vs



-- ℕ-lemmas
ℕ-lem₁ : ∀ n
         → n ≡ n + zero
ℕ-lem₁ zero    = refl
ℕ-lem₁ (suc n) = cong suc (ℕ-lem₁ n)



-- Bool-lemmas
Bool-lem₁ : ∀ p
            → p ∨ true ≡ true
Bool-lem₁ true  = refl
Bool-lem₁ false = refl

Bool-lem₂ : true ≢ false
Bool-lem₂ ()

Bool-lem₃ : ∀ p
            → p ∨ false ≡ p
Bool-lem₃ true  = refl
Bool-lem₃ false = refl

Bool-lem₄ : ∀ {p}
            → p ∨ false ≡ true
            → p ≡ true
Bool-lem₄ {p} prf = trans (sym (Bool-lem₃ p)) prf

Bool-lem₅ : ∀ p q
            → q ≡ true
            → p ∨ q ∧ true ≡ true
Bool-lem₅ true  .true refl = refl
Bool-lem₅ false .true refl = refl

Bool-lem₆ : ∀ p q
            → p ≡ true
            → p ∨ q ≡ true
Bool-lem₆ .true q refl = refl

Bool-lem₇ : ∀ p
            → p ∧ false ≡ false
Bool-lem₇ true  = refl
Bool-lem₇ false = refl

Bool-lem₈ : ∀ {p}
            → ¬ (p ∧ false ≡ true)
Bool-lem₈ {true}  ()
Bool-lem₈ {false} () 
