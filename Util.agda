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

--postulate undefined : ∀ {α} → {A : Set α} → A


-- Logic
infix 0 _⇔_
_⇔_ : ∀ {α ℓ} → Set α → Set ℓ → Set (ℓ Level.⊔ α)
P ⇔ Q = (P → Q) × (Q → P)

¬∃≡∀¬ : {A : Set}{P : A → Set} → ¬ ( Σ[ a ∈ A ] P a ) → ∀ a → ¬ P a
¬∃≡∀¬ ¬ex a Pa = ¬ex (a , Pa)

postulate ¬∀≡∃¬ : {A : Set}{P : A → Set} → ¬ (∀ a → P a) → Σ[ a ∈ A ] ¬ P a



-- Decidable Equality
DecEq : (A : Set) → Set
DecEq A = (x y : A) → Dec (x ≡ y)

decEqToBool : {A : Set} → DecEq A → (x y : A) → Bool
decEqToBool dec x  y with dec x y
decEqToBool dec x .x | yes refl = true
decEqToBool dec x  y | no  x≢y  = false

decEq-lem₁ : {A : Set} → (dec : DecEq A) → ∀ a → decEqToBool dec a a ≡ true
decEq-lem₁ dec a with dec a a
... | yes refl = refl
... | no  a≢a  = ⊥-elim (a≢a refl)

-- Injective function
Injective : {A B : Set}(f : A → B) → Set
Injective f = ∀ {a b} → f a ≡ f b → a ≡ b

Injective-lem₁ : {A B : Set}{f : A → B} → Injective f → ∀ {a b} → a ≢ b → f a ≢ f b
Injective-lem₁ f-inj a≢b fa≡fb = a≢b (f-inj fa≡fb)



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
DecEq-List dec (.y ∷ .ys) (y ∷ ys) | yes refl | yes refl
  = yes refl
DecEq-List dec (.y ∷  xs) (y ∷ ys) | yes refl | no  xs≢ys
  = no  (λ yxs≡yys → xs≢ys (cong tail yxs≡yys))
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


ℕ-lem₁ : ∀ n
         → n ≡ n + zero
ℕ-lem₁ zero    = refl
ℕ-lem₁ (suc n) = cong suc (ℕ-lem₁ n)

ℕ-lem₂ : ∀ n m
         → suc n <′ m
         → n <′ m
ℕ-lem₂ zero zero ()
ℕ-lem₂ zero (suc .1) ≤′-refl = ≤′-step ≤′-refl
ℕ-lem₂ zero (suc m) (≤′-step sn<m) = ≤′-step (ℕ-lem₂ zero m sn<m)
ℕ-lem₂ (suc n) zero ()
ℕ-lem₂ (suc n) (suc .(suc (suc n))) ≤′-refl = ≤′-step ≤′-refl
ℕ-lem₂ (suc n) (suc m) (≤′-step sn<m) = ≤′-step (ℕ-lem₂ (suc n) m sn<m)

ℕ-lem₃ : ∀ k
         → zero ≥ k
         → k ≡ zero
ℕ-lem₃ zero z≥k = refl
ℕ-lem₃ (suc k) ()

ℕ-lem₄ : ∀ j k
         → suc j ≥ k
         → suc j ∸ k ≡ zero
         → suc j ≡ k
ℕ-lem₄ zero zero sj≥k prf = prf
ℕ-lem₄ zero (suc k) (s≤s sj≥k) prf = cong suc (sym (ℕ-lem₃ k sj≥k))
ℕ-lem₄ (suc j) zero sj≥k prf = prf
ℕ-lem₄ (suc j) (suc k) (s≤s sj≥k) prf = cong suc (ℕ-lem₄ j k sj≥k prf)


ℕ-lem₅ : ∀ j k
         → j ≥ k
         → k + (j ∸ k) ≡ j
ℕ-lem₅ zero zero j≥k = refl
ℕ-lem₅ zero (suc k) ()
ℕ-lem₅ (suc j) zero j≥k = refl
ℕ-lem₅ (suc j) (suc k) (s≤s j≥k) = cong suc (ℕ-lem₅ j k j≥k)

ℕ-lem₆ : ∀ j k n
         → j ≥ k
         → j ∸ k ≡ n
         → j ≡ k + n
ℕ-lem₆ zero .0 n z≤n x = x
ℕ-lem₆ (suc j) zero    n j≥k x = x
ℕ-lem₆ (suc j) (suc k) n (s≤s j≥k) x = cong suc (ℕ-lem₆ j k n j≥k x)

ℕ-lem₇ : ∀ j k
         → j ≥ k
         → j ∸ k ≡ zero
         → j ≡ k
ℕ-lem₇ zero zero j≥k prf = refl
ℕ-lem₇ zero (suc k) () prf
ℕ-lem₇ (suc j) zero j≥k ()
ℕ-lem₇ (suc j) (suc k) (s≤s j≥k) prf = cong suc (ℕ-lem₇ j k j≥k prf)     

ℕ-lem₈ : ∀ j k n
         → j ≥ k
         → j ∸ k ≡ suc n
         → j > k
ℕ-lem₈ zero zero n j≥k ()
ℕ-lem₈ zero (suc k) n j≥k ()
ℕ-lem₈ (suc j) zero .j j≥k refl = s≤s z≤n
ℕ-lem₈ (suc j) (suc k) n (s≤s j≥k) prf = s≤s (ℕ-lem₈ j k n j≥k prf)

ℕ-lem₉ : ∀ j k n
         → j ≥ k
         → j ∸ k ≡ suc n
         → j ∸ suc k ≡ n
ℕ-lem₉ zero zero n j≥k ()
ℕ-lem₉ zero (suc k) n j≥k ()
ℕ-lem₉ (suc j) zero .j j≥k refl = refl
ℕ-lem₉ (suc j) (suc k) n (s≤s j≥k) prf = ℕ-lem₉ j k n j≥k prf

ℕ-lem₁₀ : ∀ j → j ≤ j
ℕ-lem₁₀ zero = z≤n
ℕ-lem₁₀ (suc j) = s≤s (ℕ-lem₁₀ j)

ℕ-lem₁₁ : ∀ n
          → suc n > 0
ℕ-lem₁₁ n = s≤s z≤n

ℕ-lem₁₂ : ∀ j k
          → j ≥ k
          → k ≥ j
          → j ≡ k
ℕ-lem₁₂ zero zero j≥k k≥j = refl
ℕ-lem₁₂ zero (suc k) () k≥j
ℕ-lem₁₂ (suc j) zero j≥k ()
ℕ-lem₁₂ (suc j) (suc k) (s≤s j≥k) (s≤s k≥j) = sym (cong suc (ℕ-lem₁₂ k j k≥j j≥k))

ℕ-lem₁₃ : ∀ n k
          → ¬ n ≤ k
          → n > k
ℕ-lem₁₃ zero zero n≰k = ⊥-elim (n≰k z≤n)
ℕ-lem₁₃ zero (suc k) n≰k = ⊥-elim (n≰k z≤n)
ℕ-lem₁₃ (suc n) zero n≰k = s≤s z≤n
ℕ-lem₁₃ (suc n) (suc k) n≰k = s≤s (ℕ-lem₁₃ n k (λ z → n≰k (s≤s z)))

ℕ-lem₁₄ : ∀ n k
          → n > k
          → n ≥ k
ℕ-lem₁₄ zero k ()
ℕ-lem₁₄ (suc n) zero n>k = z≤n
ℕ-lem₁₄ (suc n) (suc k) (s≤s n>k) = s≤s (ℕ-lem₁₄ n k n>k)

ℕ-lem₁₅ : ∀ {n k}
          → n ≥ k
          → suc n ≥ k
ℕ-lem₁₅ {zero} {zero} n≥k = z≤n
ℕ-lem₁₅ {zero} {suc k} ()
ℕ-lem₁₅ {suc n} {zero} n≥k = z≤n
ℕ-lem₁₅ {suc n} {suc k} (s≤s n≥k) = s≤s (ℕ-lem₁₅ {n} {k} n≥k)

ℕ-lem₁₆ : ∀ {n k}
          → n ≥ k
          → suc n > k
ℕ-lem₁₆ {zero} {zero} n≥k = s≤s n≥k
ℕ-lem₁₆ {zero} {suc k} ()
ℕ-lem₁₆ {suc n} {zero} n≥k = s≤s n≥k
ℕ-lem₁₆ {suc n} {suc k} (s≤s n≥k) = s≤s (ℕ-lem₁₆ n≥k)

ℕ-lem₁₇ : ∀ {n k j}
          → k ≥ j
          → n > k
          → n ≥ suc j
ℕ-lem₁₇ {zero} k≥j ()
ℕ-lem₁₇ {suc n} {j = zero} k≥j n>k = s≤s z≤n
ℕ-lem₁₇ {suc n} {zero} {suc j} () n>k
ℕ-lem₁₇ {suc n} {suc k} {suc j} (s≤s k≥j) (s≤s n>k) = s≤s (ℕ-lem₁₇ k≥j n>k)

ℕ-lem₁₉ : ∀ n
          → n ≥ 1
          → n ≰ 0
ℕ-lem₁₉ zero () n≤0
ℕ-lem₁₉ (suc n) (s≤s n≥1) ()       

ℕ-lem₁₈ : ∀ {n k}
          → n ≤ suc k
          → n ≱ suc (suc k)
ℕ-lem₁₈ {zero} {zero} z≤n ()
ℕ-lem₁₈ {zero} {suc k} n≤sk ()
ℕ-lem₁₈ {suc n} {zero} (s≤s n≤sk) (s≤s n≥ssk) = ℕ-lem₁₉ n n≥ssk n≤sk
ℕ-lem₁₈ {suc n} {suc k} (s≤s n≤sk) (s≤s n≥ssk) = ℕ-lem₁₈ n≤sk n≥ssk


{-
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
-}

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

Bool-lem₁₃ : ∀ {p q}
             → p ≡ false
             → p ∨ q ≡ true
             → q ≡ true
Bool-lem₁₃ {true} {true} prf prfa = refl
Bool-lem₁₃ {true} {false} () prfa
Bool-lem₁₃ {false} {true} prf refl = refl
Bool-lem₁₃ {false} {false} prf ()

∨-assoc : ∀ p q r
          → (p ∨ q) ∨ r ≡ p ∨ (q ∨ r)
∨-assoc true  q r = refl
∨-assoc false q r = refl
          
