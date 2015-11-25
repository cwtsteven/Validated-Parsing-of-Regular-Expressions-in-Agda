module Util where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat

open ≡-Reasoning

postulate undefined : ∀ {α} → {A : Set α} → A


-- Decidable Equality
DecEq : (A : Set) → Set
DecEq A = (x y : A) → Dec (x ≡ y)

decEqToBool : {A : Set} → DecEq A → (x y : A) → Bool
decEqToBool dec x y with dec x y
decEqToBool dec x .x | yes refl = true
decEqToBool dec x  y | no   x≢y = false


-- Decidable predicate and General predicate
satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = T (p x)

-- ℕ
open import Data.Empty
open import Data.Unit
_>0 : ℕ → Set
_>0 zero          = ⊥
_>0 (suc zero)    = ⊤
_>0 (suc (suc n)) = (suc n) >0


-- List lemma
++-assoc : {A : Set}(xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc [] ys zs       = refl
++-assoc (x ∷ xs) ys zs with xs ++ (ys ++ zs) | (xs ++ ys) ++ zs | ++-assoc xs ys zs
... | ws | .ws | refl = refl


List-lem₅ : {A : Set}(xs ys ys' zs : List A) → xs ≡ ys ++ zs → ys ≡ ys' → xs ≡ ys' ++ zs
List-lem₅ xs ys ys' zs xs≡yszs ys≡ys' = begin
                                        xs        ≡⟨ xs≡yszs ⟩
                                        ys ++ zs  ≡⟨ cong (λ ys → ys ++ zs) ys≡ys' ⟩
                                        ys' ++ zs
                                        ∎

List-lem₄ : {A : Set}(xs xs' ys ys' zs : List A) → xs ≡ ys ++ zs → xs' ≡ ys' ++ zs → ys ≡ ys' → xs ≡ xs'
List-lem₄ xs xs' ys ys' zs xs≡yszs xs'≡ys'zs ys≡ys' = begin
                                                      xs        ≡⟨ List-lem₅ xs ys ys' zs xs≡yszs ys≡ys' ⟩
                                                      ys' ++ zs ≡⟨ sym xs'≡ys'zs ⟩
                                                      xs'
                                                      ∎

List-lem₃ : {A B : Set}(f : A → B)(xs ys : List A) → Data.List.map f (xs ++ ys) ≡ Data.List.map f xs ++ Data.List.map f ys
List-lem₃ f []       ys = refl
List-lem₃ f (x ∷ xs) ys = cong (λ xs → f x ∷ xs) (List-lem₃ f xs ys)


List-lem₂ : {A : Set}(xs : List A) → xs ++ [] ≡ xs
List-lem₂ []       = refl
List-lem₂ (x ∷ xs) = cong (_∷_ x) (List-lem₂ xs)


List-lem₁ : {A : Set}(y : A)(xs ys : List A) → xs ++ y ∷ ys ≡ (xs ∷ʳ y) ++ ys
List-lem₁ y xs ys = ++-assoc xs Data.List.[ y ] ys
