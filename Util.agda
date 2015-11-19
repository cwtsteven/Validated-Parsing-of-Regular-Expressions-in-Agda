module Util where

open import Level
open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Function

open ≡-Reasoning

postulate undefined : ∀ {α} → {A : Set α} → A


-- Decidable Equality
DecEq : (A : Set) → Set
DecEq A = (x y : A) → Dec (x ≡ y)

decEqToBool : {A : Set} → DecEq A → (x y : A) → Bool
decEqToBool dec x y with dec x y
... | yes _ = true
... | no  _ = false


-- Decidable predicate and General predicate
satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = T (p x)


-- Boolean lemma
∧-assoc : (a b : Bool) → a ∧ b ≡ b ∧ a
∧-assoc true true   = refl
∧-assoc true false  = refl
∧-assoc false true  = refl
∧-assoc false false = refl

∨-assoc : (a b : Bool) → a ∨ b ≡ b ∨ a
∨-assoc true true   = refl
∨-assoc true false  = refl
∨-assoc false true  = refl
∨-assoc false false = refl

∧-lem₁ : (b : Bool) → b ∧ false ≡ false
∧-lem₁ b = ∧-assoc b false

∧-lem₂ : (b : Bool) → b ∧ true ≡ b
∧-lem₂ b = ∧-assoc b true

∨-lem₁ : (b : Bool) → b ∨ false ≡ b
∨-lem₁ b = ∨-assoc b false

∨-lem₂ : (b : Bool) → b ∨ true ≡ true
∨-lem₂ b = ∨-assoc b true

-- List operations
pop : {A : Set} → List A → List A
pop []       = []
pop (x ∷ xs) = xs

-- List lemma
++-assoc : {A : Set}(xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc [] ys zs       = refl
++-assoc (x ∷ xs) ys zs with xs ++ (ys ++ zs) | (xs ++ ys) ++ zs | ++-assoc xs ys zs
... | ws | .ws | refl = refl

List-lem₁ : {A : Set}(y : A)(xs ys : List A) → xs ++ y ∷ ys ≡ (xs ∷ʳ y) ++ ys
List-lem₁ y xs ys = ++-assoc xs Data.List.[ y ] ys


List-lem₂ : {A : Set}(xs : List A) → xs ++ [] ≡ xs
List-lem₂ []       = refl
List-lem₂ (x ∷ xs) = cong (_∷_ x) (List-lem₂ xs)

List-lem₃ : {A B : Set}(xs ys : List A)(f : A → B) → Data.List.map f (xs ++ ys) ≡ Data.List.map f xs ++ Data.List.map f ys
List-lem₃ [] ys f       = refl
List-lem₃ (x ∷ xs) ys f = cong (λ xs → f x ∷ xs) (List-lem₃ xs ys f)

DecEq-List : {A : Set} → DecEq A →  DecEq (List A)
DecEq-List dec []       []       = yes refl
DecEq-List dec (x ∷ xs) []       = no (λ ())
DecEq-List dec []       (x ∷ xs) = no (λ ())
DecEq-List dec (x ∷ xs) (y ∷ ys) with dec x y | DecEq-List dec xs ys
DecEq-List dec (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl  = yes refl
DecEq-List dec (x ∷ xs) (y ∷ ys)   | no ¬x≡y  | _         = no ¬xs≡ysˡ
 where
  lemˡ : {A : Set}{x y : A}{xs ys : List A} → (x ∷ xs ≡ y ∷ ys) → x ≡ y
  lemˡ refl = refl
  ¬xs≡ysˡ : ¬ (x ∷ xs ≡ y ∷ ys)
  ¬xs≡ysˡ xxs≡yys = ¬x≡y (lemˡ xxs≡yys)
DecEq-List dec (x ∷ xs) (y ∷ ys)   | _        | no ¬xs≡ys = no ¬xs≡ysʳ
 where 
  lemʳ : {A : Set}{x y : A}{xs ys : List A} → (x ∷ xs ≡ y ∷ ys) → xs ≡ ys
  lemʳ refl = refl
  ¬xs≡ysʳ : ¬ (x ∷ xs ≡ y ∷ ys)
  ¬xs≡ysʳ xxs≡yys = ¬xs≡ys (lemʳ xxs≡yys)
