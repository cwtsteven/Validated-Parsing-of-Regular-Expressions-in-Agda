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
⟦_⟧ : {A : Set} → A → DecSubset A
⟦ a ⟧ = undefined --λ b → decEqToBool dec a b

infix 10 _∈_
-- membership
_∈_ : {A : Set} → A → DecSubset A → Bool
a ∈ p = p a

infix 10 _∈ᵍ_
-- membership
_∈ᵍ_ : {A : Set} → A → DecSubset A → Set
a ∈ᵍ p = p a ≡ true

infix 11 _⋂_
-- intersection
_⋂_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋂ bs = λ a → a ∈ as ∧ a ∈ bs

infix 11 _⋃_
-- union
_⋃_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋃ bs = λ a → a ∈ as ∨ a ∈ bs

infix 10 _⊆_
-- subset
_⊆_ : {A : Set} → DecSubset A → DecSubset A → Set
as ⊆ bs = ∀ a → a ∈ as ≡ true → a ∈ bs ≡ true

infix 10 _⊇_
-- includes
_⊇_ : {A : Set} → DecSubset A → DecSubset A → Set
as ⊇ bs = bs ⊆ as

infix 0 _≈_
-- equality
_≈_ : {A : Set} → DecSubset A → DecSubset A → Set
as ≈ bs = (as ⊆ bs) × (as ⊇ bs)
                 

-- Decidable Powerset
data Dec-ℙ (A : Set) : Set where
  sub : DecSubset A → Dec-ℙ A
