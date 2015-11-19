open import Util
module Subset where

open import Level
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty

-- General Subset
Subset : ∀ {ℓ} → (A : Set ℓ) → Set (suc ℓ)
Subset {ℓ} A = A → Set ℓ

infix 10 _∈_
-- membership
_∈_ : {A : Set} → A → Subset A → Set
a ∈ p = p a

-- null set
Ø : {A : Set} → Subset A
Ø = λ _ → ⊥

-- singleton
singleton : {A : Set}{dec : DecEq A}(a : A) → Subset A
singleton {A} {dec} a  b with dec a b
singleton {A} {dec} a .a | yes refl = ⊤
singleton {A} {dec} a  b | no  _    = ⊥

infix 11 _⋂_
-- intersection
_⋂_ : {A : Set} → Subset A → Subset A → Subset A
as ⋂ bs = λ a → a ∈ as × a ∈ bs

infix 11 _⋃_
-- union
_⋃_ : {A : Set} → Subset A → Subset A → Subset A
as ⋃ bs = λ a → a ∈ as ⊎ a ∈ bs

infix 10 _⊆_
-- subset
_⊆_ : {A : Set} → Subset A → Subset A → Set
as ⊆ bs = ∀ a → a ∈ as → a ∈ bs

infix 10 _⊇_
-- includes
_⊇_ : {A : Set} → Subset A → Subset A → Set
as ⊇ bs = bs ⊆ as

infix 0 _≈_
-- equality
_≈_ : {A : Set} → Subset A → Subset A → Set
as ≈ bs = (as ⊆ bs) × (as ⊇ bs)


-- Powerset
data ℙ {ℓ : Level}(A : Set ℓ) : Set (suc ℓ) where
 sub : Subset A → ℙ A
