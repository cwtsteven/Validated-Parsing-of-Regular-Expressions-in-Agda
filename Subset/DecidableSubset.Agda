{-
  This module contains the definition of Decidable Subset and its operations.

  Steven Cheung 2015.
  Version 9-12-2015
-}
module Subset.DecidableSubset where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Function
open import Data.Empty

open import Util

-- Decidable Subset
DecSubset : (A : Set) → Set
DecSubset A = A → Bool

-- null set
Ø : {A : Set} → DecSubset A
Ø = λ _ → false

-- singleton
singleton : {A : Set}{dec : DecEq A} → A → DecSubset A
singleton {dec = dec} a = λ b → decEqToBool dec a b

infix 10 _∈_
-- membership
_∈_ : {A : Set} → A → DecSubset A → Bool
a ∈ p = p a

infix 10 _∈ᵍ_
_∈ᵍ_ : {A : Set} → A → DecSubset A → Set
a ∈ᵍ p = T (a ∈ p)

infix 11 _⋂_
-- intersection
_⋂_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋂ bs = λ a → a ∈ as ∧ a ∈ bs

infix 11 _⋃_
-- union
_⋃_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋃ bs = λ a → a ∈ as ∨ a ∈ bs


-- operations related to list
toList : {A : Set} → DecSubset A → List A → List A
toList = filter

¬empty : {A : Set} → DecSubset A → List A → Bool
¬empty as l = any (λ a → a ∈ as) l
