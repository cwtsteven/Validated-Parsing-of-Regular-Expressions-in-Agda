{-
  Quotient Set

  Steven Cheung
  Version 15-03-2016
-}
module Quotient where

open import Data.Bool
open import Relation.Nullary
open import Relation.Binary
open import Data.Product

open import Util
open import Subset
open import Subset.DecidableSubset
  renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; Ø to Øᵈ ; _⋃_ to _⋃ᵈ_ ; _⋂_ to _⋂ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ
                 ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ≈-refl to ≈ᵈ-refl ; ≈-trans to ≈ᵈ-trans ; ≈-sym to ≈ᵈ-sym)

record QuotientSet : Set₁ where
  field
    Q : Set
    _∼_ : Q → Q → Set
    Dec-∼ : ∀ q q' → Dec (q ∼ q')
    ∼-isEquiv : IsEquivalence _∼_


module Quot-Properties (quot : QuotientSet) where
  open QuotientSet quot

  -- Equivalence classes
  infix 0 ⟪_⟫
  ⟪_⟫ : Q → DecSubset Q
  ⟪ p ⟫ q with Dec-∼ q p
  ... | yes _ = true
  ... | no  _ = false

  ∼iff≈ : ∀ {p q} → (p ∼ q) ⇔ (⟪ p ⟫ ≈ᵈ ⟪ q ⟫)
  ∼iff≈ = undefined

  data Quot-Set : Set where
    class : ∀ qs → Σ[ q ∈ Q ] (qs ≈ᵈ ⟪ q ⟫) → Quot-Set
