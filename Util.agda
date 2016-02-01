{-
  This module contains some miscellaneous definitions and proofs that will be used.

  Steven Cheung 2015.
  Version 10-01-2016
-}
module Util where

open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat

open ≡-Reasoning

postulate undefined : ∀ {α} → {A : Set α} → A

-- Logic
infix 0 _⇔_
_⇔_ : ∀ {α ℓ} → Set α → Set ℓ → Set (ℓ Level.⊔ α)
P ⇔ Q = (P → Q) × (Q → P)

-- Function
Injective : {A B : Set}(f : A → B) → Set
Injective f = ∀ x y → f x ≡ f y → x ≡ y

Inj-lem₁ : {A B : Set}(f : A → B) → Injective f → ∀ x y → f x ≢ f y → x ≢ y
Inj-lem₁ f f-inj x y fx≢fy x≡y = fx≢fy (cong f x≡y)


-- Decidable Equality
DecEq : (A : Set) → Set
DecEq A = (x y : A) → Dec (x ≡ y)

decEqToBool : {A : Set} → DecEq A → (x y : A) → Bool
decEqToBool dec x  y with dec x y
decEqToBool dec x .x | yes refl = true
decEqToBool dec x  y | no  x≢y  = false

decEq-lem₂ : {A B : Set} → (f : B → A) → Injective f → DecEq A → DecEq B
decEq-lem₂ f f-inj decA b₁ b₂ with decA (f b₁) (f b₂)
decEq-lem₂ f f-inj decA b₁ b₂ | yes prf = yes (f-inj b₁ b₂ prf)
decEq-lem₂ f f-inj decA b₁ b₂ | no  prf = no  (Inj-lem₁ f f-inj b₁ b₂ prf)

decEq-lem₁ : {A : Set} → (dec : DecEq A) → ∀ a → decEqToBool dec a a ≡ true
decEq-lem₁ dec a with dec a a
... | yes refl = refl
... | no  a≢a  = ⊥-elim (a≢a refl)



-- List lemmas
tail : {A : Set} → List A → List A
tail []       = []
tail (x ∷ xs) = xs


DecEq-List : {A : Set} → DecEq A → DecEq (List A)
DecEq-List dec []         []       = yes refl
DecEq-List dec ( x ∷  xs) []       = no (λ ())
DecEq-List dec []         (y ∷ ys) = no (λ ())
DecEq-List dec ( x ∷  xs) (y ∷ ys) with dec x y
DecEq-List dec (.y ∷  xs) (y ∷ ys) | yes refl with DecEq-List dec xs ys
DecEq-List dec (.y ∷ .ys) (y ∷ ys) | yes refl | yes refl  = yes refl
DecEq-List dec (.y ∷  xs) (y ∷ ys) | yes refl | no  xs≢ys = no  (λ yxs≡yys → xs≢ys (cong tail yxs≡yys))
DecEq-List dec ( x ∷  xs) (y ∷ ys) | no  x≢y  = no (λ xxs≡yys → x≢y (lem₁ xxs≡yys))
  where
    lem₁ : {A : Set}{x y : A}{xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
    lem₁ {x} {._} {xs} {._} refl = refl


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
infix 6 _-_
_-_ : (n m : ℕ) → {{m<n : m ≤ n}} → ℕ
(n     - zero)  {{_}}  = n
(zero  - suc n) {{()}}
(suc n - suc m) {{s≤s m≤n}} = (n - m) {{m≤n}}

_^_ : ℕ → ℕ → ℕ
n ^ zero    = suc zero
n ^ (suc m) = n * (n ^ m)

ℕ-lem₁ : ∀ n
         → n ≡ n + zero
ℕ-lem₁ zero    = refl
ℕ-lem₁ (suc n) = cong suc (ℕ-lem₁ n)


ℕ-lem₂ : ∀ n m
         → n > m
         → ¬ n ≤ m
ℕ-lem₂ zero    m        () n≤m
ℕ-lem₂ (suc n) zero    n>m ()
ℕ-lem₂ (suc n) (suc m) (s≤s sm≤n) (s≤s n≤m) = ℕ-lem₂ n m sm≤n n≤m

ℕ-lem₃ : ∀ n m
         → (n≤m : m ≤ n)
         → (n≤sm : suc m ≤ n)
         → suc (n - suc m) ≡ n - m
ℕ-lem₃ zero    zero    _    ()
ℕ-lem₃ (suc n) zero    z≤sn (s≤s z≤n) = cong suc refl
ℕ-lem₃ zero    (suc m) ()   sm≤n
ℕ-lem₃ (suc n) (suc m) (s≤s m≤n) (s≤s sm≤n) = ℕ-lem₃ n m m≤n sm≤n

ℕ-lem₄ : ∀ n m
         → suc n ≤ m
         → n ≤ m
ℕ-lem₄ zero    m sn≤m = z≤n
ℕ-lem₄ (suc n) zero    ()
ℕ-lem₄ (suc n) (suc m) (s≤s n≤m) = s≤s (ℕ-lem₄ n m n≤m)

ℕ-lem₅ : ∀ n m
         → n ≤′ m
         → suc n ≤′ suc m
ℕ-lem₅ zero    zero    ≤′-refl = ≤′-refl
ℕ-lem₅ zero    (suc m) (≤′-step n≤m) = ≤′-step (ℕ-lem₅ zero m n≤m)
ℕ-lem₅ (suc n) zero ()
ℕ-lem₅ (suc n) (suc .n) ≤′-refl = ≤′-refl
ℕ-lem₅ (suc n) (suc m) (≤′-step n≤m) = ≤′-step (ℕ-lem₅ (suc n) m n≤m)

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

Bool-lem₉ : ∀ {p}
            → p ≡ false
            → p ≢ true
Bool-lem₉ {.false} refl ()

Bool-lem₁₀ : ∀ p q
             → p ≡ true
             → q ∨ p ≡ true
Bool-lem₁₀ .true false refl = refl
Bool-lem₁₀ .true true  refl = refl

Bool-lem₁₁ : ∀ p q r
             → p ≡ true
             → q ≡ true
             → p ∧ q ∨ r ≡ true
Bool-lem₁₁ .true .true _ refl refl = refl

Bool-lem₁₂ : false ≢ true
Bool-lem₁₂ ()
