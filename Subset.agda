{-
  This module contains the definition of Powerset and its operations.

  Steven Cheung 2015.
  Version 26-11-2015
-}

module Subset where

open import Level
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product
open import Data.Empty

-- General Powerset
Powerset : ∀ {α}(A : Set α) → {ℓ : Level} → Set (α ⊔ suc ℓ)
Powerset A {ℓ} = A → Set ℓ

-- Empty set
Ø : ∀ {α}{A : Set α} → Powerset A
Ø = λ _ → ⊥

-- Singleton
⟦_⟧ : ∀ {α}{A : Set α}(a : A) → Powerset A
⟦ a ⟧ = λ b → a ≡ b

-- Membership
infix 10 _∈_
_∈_ : ∀ {α ℓ}{A : Set α} → A → Powerset A → Set ℓ
a ∈ p = p a

-- Decidable
Decidable : ∀ {α ℓ}{A : Set α} → Powerset A {ℓ} → Set (α ⊔ ℓ)
Decidable as = ∀ a → Dec (a ∈ as)


{- Here we define the operations on set -}

-- Intersection
infix 11 _⋂_
_⋂_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Powerset A {β ⊔ ℓ}
as ⋂ bs = λ a → a ∈ as × a ∈ bs

-- Union
infix 11 _⋃_
_⋃_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Powerset A {β ⊔ ℓ}
as ⋃ bs = λ a → a ∈ as ⊎ a ∈ bs

-- Subset
infix 10 _⊆_
_⊆_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Set (α ⊔ β ⊔ ℓ)
as ⊆ bs = ∀ a → a ∈ as → a ∈ bs

-- Superset
infix 10 _⊇_
_⊇_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Set (α ⊔ β ⊔ ℓ)
as ⊇ bs = bs ⊆ as

-- Equality
infix 0 _≈_
_≈_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Set (α ⊔ β ⊔ ℓ)
as ≈ bs = (as ⊆ bs) × (as ⊇ bs)

-- Reflexivity of ≈
≈-refl : ∀ {α ℓ}{A : Set α}{as : Powerset A {ℓ}} → as ≈ as
≈-refl = (λ a a∈as → a∈as) , (λ a a∈as → a∈as)

-- Symmetry of ≈
≈-sym : ∀ {α β ℓ}{A : Set α}{as : Powerset A {β}}{bs : Powerset A {ℓ}} → as ≈ bs → bs ≈ as
≈-sym (as⊆bs , as⊇bs) = as⊇bs , as⊆bs

-- Transitivity of ≈
≈-trans : ∀ {α β γ ℓ}{A : Set α}{as : Powerset A {β}}{bs : Powerset A {ℓ}}{cs : Powerset A {γ}} → as ≈ bs → bs ≈ cs → as ≈ cs
≈-trans (as⊆bs , as⊇bs) (bs⊆cs , bs⊇cs) = (λ a a∈as → bs⊆cs a (as⊆bs a a∈as)) , (λ a a∈cs → as⊇bs a (bs⊇cs a a∈cs))

-- Equality and decidability
≈-Decidable : ∀ {α β ℓ}{A : Set α}{as : Powerset A {β}}{bs : Powerset A {ℓ}} → as ≈ bs → Decidable as → Decidable bs
≈-Decidable (as⊆bs , as⊇bs) dec a with dec a
... | yes a∈as = yes (as⊆bs a a∈as)
... | no  a∉as = no  (λ a∈bs → a∉as (as⊇bs a a∈bs))

