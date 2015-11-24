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
-- membership as general predicate
_∈ᵍ_ : {A : Set} → A → DecSubset A → Set
a ∈ᵍ p = satisfies (λ a → a ∈ p) a

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

-- operations related to list
toList : {A : Set} → DecSubset A → List A → List A
toList = filter

¬empty : {A : Set} → DecSubset A → List A → Bool
¬empty as l = any (λ a → a ∈ as) l


-- lemma
⋂-lem₁ : {A : Set}(a : A)(as : DecSubset A) → a ∈ as ⋂ Ø ≡ false
⋂-lem₁ a as = ∧-lem₁ (a ∈ as)

⋃-lem₁ : {A : Set}(a : A)(as : DecSubset A) → a ∈ as ⋃ Ø ≡ a ∈ as
⋃-lem₁ a as = ∨-lem₁ (a ∈ as)

toList-lem₁ : {A : Set}(as : DecSubset A)(xs : List A) → toList (as ⋂ Ø) xs ≡ []
toList-lem₁ as [] = refl
toList-lem₁ as (x ∷ xs) with x ∈ as ⋂ Ø | ⋂-lem₁ x as | toList (as ⋂ Ø) xs | toList-lem₁ as xs 
toList-lem₁ as (x ∷ xs) | .false | refl | .[] | refl = toList-lem₁ as xs

⋂-toList-lem₁ : {A : Set}(as : DecSubset A)(it : List A) → null (toList (as ⋂ Ø) it) ≡ true
⋂-toList-lem₁ as w = cong null (toList-lem₁ as w)

⋂-¬empty-lem₁ : {A : Set}(as : DecSubset A)(xs : List A) → ¬empty (as ⋂ Ø) xs ≡ false
⋂-¬empty-lem₁ as [] = refl
⋂-¬empty-lem₁ as (x ∷ xs) with x ∈ as ⋂ Ø | ⋂-lem₁ x as | ¬empty (as ⋂ Ø) xs | ⋂-¬empty-lem₁ as xs
⋂-¬empty-lem₁ as (x ∷ xs) | .false | refl | .false | refl = refl

⊆-lem₂ : {A : Set}{as : DecSubset A} → Ø ⊆ as
⊆-lem₂ a ()
                 

-- Decidable Powerset
data Dec-ℙ (A : Set) : Set where
  sub : DecSubset A → Dec-ℙ A
