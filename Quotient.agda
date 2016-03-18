{-
  Quotient Set

  Steven Cheung
  Version 15-03-2016
-}
module Quotient where

open import Data.Bool
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty
open import Data.Nat
open import Data.Vec renaming (_∈_ to _∈ⱽ_)

open import Util
open import Subset
open import Subset.DecidableSubset
  renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; Ø to Øᵈ ; _⋃_ to _⋃ᵈ_ ; _⋂_ to _⋂ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ
                 ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ≈-refl to ≈ᵈ-refl ; ≈-trans to ≈ᵈ-trans ; ≈-sym to ≈ᵈ-sym ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep


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

  ⟪⟫-lem : ∀ p → p ∈ᵈ ⟪ p ⟫
  ⟪⟫-lem p with Dec-∼ p p
  ... | yes _   = refl
  ... | no  prf = ⊥-elim (prf (IsEquivalence.refl ∼-isEquiv))


  data Quot-Set : Set where
    class : ∀ qs → Σ[ q ∈ Q ] (qs ≈ᵈ ⟪ q ⟫) → Quot-Set

  _≋_ : Quot-Set → Quot-Set → Set
  (class qs (q , prf)) ≋ (class qs' (q' , prf')) = qs ≈ᵈ qs'

  ≋-refl : Reflexive _≋_
  ≋-refl {class qs (q , prf)} = IsEquivalence.refl ≈ᵈ-isEquiv
    
  ≋-sym : Symmetric _≋_
  ≋-sym {class qs (q , prf)} {class qs' (q' , prf')} q≋q' = IsEquivalence.sym ≈ᵈ-isEquiv q≋q'
    
  ≋-trans : Transitive _≋_
  ≋-trans {class qs (q , prf)} {class qs' (q' , prf')} {class qs'' (q'' , prf'')} q≋q' q'≋q'' = IsEquivalence.trans ≈ᵈ-isEquiv q≋q' q'≋q''
    
  ≋-isEquiv : IsEquivalence {A = Quot-Set} _≋_
  ≋-isEquiv = record { refl = λ {q} → ≋-refl {q} ; sym = λ {q} {q'} → ≋-sym {q} {q'} ; trans = λ {q} {q'} {q''} → ≋-trans {q} {q'} {q''} }
