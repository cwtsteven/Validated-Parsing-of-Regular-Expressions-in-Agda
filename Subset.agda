{-
  This module contains the definition of Subset and its operations.

  Steven Cheung 2015.
  Version 07-01-2016
-}

module Subset where

--open import Util
--open import Level
open import Data.Bool hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product
open import Data.Empty

-- General Subset
Subset : Set → Set₁
Subset A = A → Set

-- Empty set
Ø : {A : Set} → Subset A
Ø = λ _ → ⊥

-- Singleton
⟦_⟧ : {A : Set} → A → Subset A
⟦ a ⟧ = λ b → a ≡ b

-- Membership
infix 10 _∈_
_∈_ : {A : Set} → A → Subset A → Set
a ∈ p = p a

infix 10 _∉_
_∉_ : {A : Set} → A → Subset A → Set
a ∉ p = ¬ (a ∈ p)

-- Decidable
Decidable : {A : Set} → Subset A → Set
Decidable as = ∀ a → Dec (a ∈ as)

-- Membership decider
infix 10 _∈?_
_∈?_ : {A : Set} → (a : A) → (as : Subset A) → {{dec : Decidable as}} → Dec (a ∈ as)
(a ∈? as) {{dec}} = dec a


{- Here we define the operations on subset -}

-- Intersection
infix 11 _⋂_
_⋂_ : {A : Set} → Subset A → Subset A → Subset A
as ⋂ bs = λ a → a ∈ as × a ∈ bs

-- Union
infix 11 _⋃_
_⋃_ : {A : Set} → Subset A → Subset A → Subset A
as ⋃ bs = λ a → a ∈ as ⊎ a ∈ bs

-- Subset
infix 10 _⊆_
_⊆_ : {A : Set} → Subset A → Subset A → Set
as ⊆ bs = ∀ a → a ∈ as → a ∈ bs

-- Superset
infix 10 _⊇_
_⊇_ : {A : Set} → Subset A → Subset A → Set
as ⊇ bs = bs ⊆ as

-- Equality
infix 0 _≈_
_≈_ : {A : Set} → Subset A → Subset A → Set
as ≈ bs = (as ⊆ bs) × (as ⊇ bs)

-- Reflexivity of ≈
≈-refl : {A : Set}{as : Subset A}
         → as ≈ as
≈-refl = (λ a a∈as → a∈as) , (λ a a∈as → a∈as)

-- Symmetry of ≈
≈-sym : {A : Set}{as bs : Subset A}
        → as ≈ bs
        → bs ≈ as
≈-sym (as⊆bs , as⊇bs) = as⊇bs , as⊆bs

-- Transitivity of ≈
≈-trans : {A : Set}{as bs cs : Subset A}
          → as ≈ bs
          → bs ≈ cs
          → as ≈ cs
≈-trans (as⊆bs , as⊇bs) (bs⊆cs , bs⊇cs) = (λ a a∈as → bs⊆cs a (as⊆bs a a∈as)) , (λ a a∈cs → as⊇bs a (bs⊇cs a a∈cs))

-- Equality and decidability
Decidable-lem₁ : {A : Set}{as bs : Subset A}
                 → as ≈ bs
                 → Decidable as
                 → Decidable bs
Decidable-lem₁ (as⊆bs , as⊇bs) dec a with dec a
... | yes a∈as = yes (as⊆bs a a∈as)
... | no  a∉as = no  (λ a∈bs → a∉as (as⊇bs a a∈bs))


{-
-- General Subset
Subset : ∀ {α} → Set α → {ℓ : Level} → Set (α ⊔ suc ℓ)
Subset A {ℓ} = A → Set ℓ

-- Empty set
Ø : ∀ {α}{A : Set α} → Subset A
Ø = λ _ → ⊥

-- Singleton
⟦_⟧ : ∀ {α}{A : Set α} → A → Subset A
⟦ a ⟧ = λ b → a ≡ b

-- Membership
infix 10 _∈_
_∈_ : ∀ {α ℓ}{A : Set α} → A → Subset A → Set ℓ
a ∈ p = p a

-- Decidable
Decidable : ∀ {α ℓ}{A : Set α} → Subset A {ℓ} → Set (α ⊔ ℓ)
Decidable as = ∀ a → Dec (a ∈ as)

-- Membership decider
infix 10 _∈?_
_∈?_ : ∀ {α ℓ}{A : Set α} → (a : A) → (as : Subset A {ℓ}) → {{dec : Decidable as}} → Dec (a ∈ as)
(a ∈? as) {{dec}} = dec a


{- Here we define the operations on subset -}

-- Intersection
infix 11 _⋂_
_⋂_ : ∀ {α β ℓ}{A : Set α} → Subset A {β} → Subset A {ℓ} → Subset A {β ⊔ ℓ}
as ⋂ bs = λ a → a ∈ as × a ∈ bs

-- Union
infix 11 _⋃_
_⋃_ : ∀ {α β ℓ}{A : Set α} → Subset A {β} → Subset A {ℓ} → Subset A {β ⊔ ℓ}
as ⋃ bs = λ a → a ∈ as ⊎ a ∈ bs

-- Subset
infix 10 _⊆_
_⊆_ : ∀ {α β ℓ}{A : Set α} → Subset A {β} → Subset A {ℓ} → Set (α ⊔ β ⊔ ℓ)
as ⊆ bs = ∀ a → a ∈ as → a ∈ bs

-- Superset
infix 10 _⊇_
_⊇_ : ∀ {α β ℓ}{A : Set α} → Subset A {β} → Subset A {ℓ} → Set (α ⊔ β ⊔ ℓ)
as ⊇ bs = bs ⊆ as

-- Equality
infix 0 _≈_
_≈_ : ∀ {α β ℓ}{A : Set α} → Subset A {β} → Subset A {ℓ} → Set (α ⊔ β ⊔ ℓ)
as ≈ bs = (as ⊆ bs) × (as ⊇ bs)

-- Reflexivity of ≈
≈-refl : ∀ {α ℓ}{A : Set α}{as : Subset A {ℓ}} → as ≈ as
≈-refl = (λ a a∈as → a∈as) , (λ a a∈as → a∈as)

-- Symmetry of ≈
≈-sym : ∀ {α β ℓ}{A : Set α}{as : Subset A {β}}{bs : Subset A {ℓ}} → as ≈ bs → bs ≈ as
≈-sym (as⊆bs , as⊇bs) = as⊇bs , as⊆bs

-- Transitivity of ≈
≈-trans : ∀ {α β γ ℓ}{A : Set α}{as : Subset A {β}}{bs : Subset A {ℓ}}{cs : Subset A {γ}} → as ≈ bs → bs ≈ cs → as ≈ cs
≈-trans (as⊆bs , as⊇bs) (bs⊆cs , bs⊇cs) = (λ a a∈as → bs⊆cs a (as⊆bs a a∈as)) , (λ a a∈cs → as⊇bs a (bs⊇cs a a∈cs))

-- Equality and decidability
Decidable-lem₁ : ∀ {α β ℓ}{A : Set α}{as : Subset A {β}}{bs : Subset A {ℓ}} → as ≈ bs → Decidable as → Decidable bs
Decidable-lem₁ (as⊆bs , as⊇bs) dec a with dec a
... | yes a∈as = yes (as⊆bs a a∈as)
... | no  a∉as = no  (λ a∈bs → a∉as (as⊇bs a a∈bs))
-}
