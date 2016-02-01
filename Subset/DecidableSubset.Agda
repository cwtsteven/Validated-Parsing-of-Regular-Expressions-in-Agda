{-
  This module contains the definition of Decidable Subset and its operations.

  Steven Cheung 2015.
  Version 10-01-2016
-}
open import Util
module Subset.DecidableSubset where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function
open import Data.Empty

-- Decidable Subset
DecSubset : (A : Set) → Set
DecSubset A = A → Bool

-- Empty set
Ø : {A : Set} → DecSubset A
Ø = λ _ → false

-- Singleton
⟦_⟧ : {A : Set} → A → {{dec : DecEq A}} → DecSubset A
⟦ a ⟧ {{dec}} = λ b → decEqToBool dec a b


-- Membership
infix 10 _∈?_
_∈?_ : {A : Set} → A → DecSubset A → Bool
a ∈? p = p a

infix 10 _∉?_
_∉?_ : {A : Set} → A → DecSubset A → Bool
a ∉? p = not (a ∈? p)

infix 10 _∈_
_∈_ : {A : Set} → A → DecSubset A → Set
a ∈ p = a ∈? p ≡ true

infix 10 _∉_
_∉_ : {A : Set} → A → DecSubset A → Set
a ∉ p = ¬ (a ∈ p)


⟦a⟧-lem₁ : {A : Set}(dec : DecEq A)(a : A) → a ∈ ⟦ a ⟧ {{dec}}
⟦a⟧-lem₁ dec a with dec a a
⟦a⟧-lem₁ dec a | yes refl = refl
⟦a⟧-lem₁ dec a | no  a≢a  = ⊥-elim (a≢a refl)

{- a ∉ p ⇔ a ∈? p ≡ false -}
∈-lem₃ : {A : Set}{a : A}{p : DecSubset A}
          → a ∉ p
          → a ∈? p ≡ false
∈-lem₃ {A} {a} {p} a∉p with a ∈? p
∈-lem₃ {A} {a} {p} a∉p | true  = ⊥-elim (a∉p refl)
∈-lem₃ {A} {a} {p} a∉p | false = refl

∈-lem₂ : {A : Set}{a : A}{p : DecSubset A}
          → a ∈? p ≡ false
          → a ∉ p
∈-lem₂ {A} {a} {p} a∈?p≡false a∈p with a ∈? p
∈-lem₂ {A} {a} {p} ()         a∈p | true 
∈-lem₂ {A} {a} {p} a∈?p≡false ()  | false

∈-lem₁ : {A : Set}{a : A}{p : DecSubset A}
          → a ∈? p ≡ false ⇔ a ∉ p
∈-lem₁ {A} {a} {p} = ∈-lem₂ {A} {a} {p} , ∈-lem₃ {A} {a} {p}
{- a ∉ p ⇔ a ∈? p ≡ false -}

-- Intersection
infix 11 _⋂_
_⋂_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋂ bs = λ a → a ∈? as ∧ a ∈? bs

-- Union
infix 11 _⋃_
_⋃_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋃ bs = λ a → a ∈? as ∨ a ∈? bs


