module Approach3.Subset where

open import Level
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product
open import Data.Empty

-- General Powerset
Powerset : ∀ {α}(A : Set α) → {ℓ : Level} → Set (α ⊔ suc ℓ)
Powerset A {ℓ} = A → Set ℓ


infix 10 _∈_
-- membership
_∈_ : ∀ {α ℓ}{A : Set α} → A → Powerset A → Set ℓ
a ∈ p = p a

-- is Decidable
Decidable : ∀ {α ℓ}{A : Set α} → Powerset A {ℓ} → Set (α ⊔ ℓ)
Decidable as = ∀ a → Dec (a ∈ as)


-- null set
Ø : ∀ {α}{A : Set α} → Powerset A
Ø = λ _ → ⊥

-- singleton
⟦_⟧ : ∀ {α}{A : Set α}(a : A) → Powerset A
⟦ a ⟧ = λ b → a ≡ b


infix 11 _⋂_
-- intersection
_⋂_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Powerset A {β ⊔ ℓ}
as ⋂ bs = λ a → a ∈ as × a ∈ bs

infix 11 _⋃_
-- union
_⋃_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Powerset A {β ⊔ ℓ}
as ⋃ bs = λ a → a ∈ as ⊎ a ∈ bs

infix 10 _⊆_
-- subset
_⊆_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Set (α ⊔ β ⊔ ℓ)
as ⊆ bs = ∀ a → a ∈ as → a ∈ bs

infix 10 _⊇_
-- superset
_⊇_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Set (α ⊔ β ⊔ ℓ)
as ⊇ bs = bs ⊆ as

infix 0 _≈_
-- equality
_≈_ : ∀ {α β ℓ}{A : Set α} → Powerset A {β} → Powerset A {ℓ} → Set (α ⊔ β ⊔ ℓ)
as ≈ bs = (as ⊆ bs) × (as ⊇ bs)

≈-refl : ∀ {α ℓ}{A : Set α}{as : Powerset A {ℓ}} → as ≈ as
≈-refl = (λ a a∈as → a∈as) , (λ a a∈as → a∈as)

≈-sym : ∀ {α β ℓ}{A : Set α}{as : Powerset A {β}}{bs : Powerset A {ℓ}} → as ≈ bs → bs ≈ as
≈-sym (as⊆bs , as⊃bs) = as⊃bs , as⊆bs

≈-trans : ∀ {α β γ ℓ}{A : Set α}{as : Powerset A {β}}{bs : Powerset A {ℓ}}{cs : Powerset A {γ}} → as ≈ bs → bs ≈ cs → as ≈ cs
≈-trans (as⊆bs , as⊃bs) (bs⊆cs , bs⊃cs) = (λ a a∈as → bs⊆cs a (as⊆bs a a∈as)) , (λ a a∈cs → as⊃bs a (bs⊃cs a a∈cs))

≈-Decidable : ∀ {α β ℓ}{A : Set α}(as : Powerset A {β})(bs : Powerset A {ℓ}) → as ≈ bs → Decidable as → Decidable bs
≈-Decidable as bs (as⊆bs , as⊃bs) dec a with dec a
... | yes a∈as = yes (as⊆bs a a∈as)
... | no  a∉as = no  (λ a∈bs → a∉as (as⊃bs a a∈bs))

