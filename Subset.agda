module Subset where

open import Level
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product
open import Data.Empty

-- General Powerset
Powerset : (A : Set) → Set₁
Powerset A = A → Set

infix 10 _∈_
-- membership
_∈_ : {A : Set} → A → Powerset A → Set
a ∈ p = p a

-- is Decidable
Decidable : {A : Set}→ Powerset A → Set
Decidable as = ∀ a → Dec (a ∈ as)

-- null set
Ø : {A : Set} → Powerset A
Ø = λ _ → ⊥

-- singleton
⟦_⟧ : {A : Set}(a : A) → Powerset A
⟦ a ⟧ = λ b → a ≡ b

infix 11 _⋂_
-- intersection
_⋂_ : {A : Set} → Powerset A → Powerset A → Powerset A
as ⋂ bs = λ a → a ∈ as × a ∈ bs

infix 11 _⋃_
-- union
_⋃_ : {A : Set} → Powerset A → Powerset A → Powerset A
as ⋃ bs = λ a → a ∈ as ⊎ a ∈ bs

infix 10 _⊆_
-- subset
_⊆_ : {A : Set} → Powerset A → Powerset A → Set
as ⊆ bs = ∀ a → a ∈ as → a ∈ bs

infix 10 _⊇_
-- superset
_⊇_ : {A : Set} → Powerset A → Powerset A → Set
as ⊇ bs = bs ⊆ as

infix 0 _≈_
-- equality
_≈_ : {A : Set} → Powerset A → Powerset A → Set
as ≈ bs = (as ⊆ bs) × (as ⊇ bs)

≈-refl : {A : Set}{as : Powerset A} → as ≈ as
≈-refl = (λ a a∈as → a∈as) , (λ a a∈as → a∈as)

≈-sym : {A : Set}{as bs : Powerset A} → as ≈ bs → bs ≈ as
≈-sym (as⊆bs , as⊃bs) = as⊃bs , as⊆bs

≈-trans : {A : Set}{as bs cs : Powerset A} → as ≈ bs → bs ≈ cs → as ≈ cs
≈-trans (as⊆bs , as⊃bs) (bs⊆cs , bs⊃cs) = (λ a a∈as → bs⊆cs a (as⊆bs a a∈as)) , (λ a a∈cs → as⊃bs a (bs⊃cs a a∈cs))

≈-Decidable : {A : Set}(as bs : Powerset A) → as ≈ bs → Decidable as → Decidable bs
≈-Decidable as bs (as⊆bs , as⊃bs) dec a with dec a
... | yes a∈as = yes (as⊆bs a a∈as)
... | no  a∉as = no  (λ a∈bs → a∉as (as⊃bs a a∈bs))
