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


  data Q/~ : Set where
    class : ∀ qs → Σ[ q ∈ Q ] (qs ≈ᵈ ⟪ q ⟫) → Q/~

  _≋_ : Q/~ → Q/~ → Set
  (class qs (q , prf)) ≋ (class qs' (q' , prf')) = q ∼ q'

  ≋-refl : Reflexive _≋_
  ≋-refl {class qs (q , prf)} = IsEquivalence.refl ∼-isEquiv
    
  ≋-sym : Symmetric _≋_
  ≋-sym {class qs (q , prf)} {class qs' (q' , prf')} q≋q' = IsEquivalence.sym ∼-isEquiv q≋q'
    
  ≋-trans : Transitive _≋_
  ≋-trans {class qs (q , prf)} {class qs' (q' , prf')} {class qs'' (q'' , prf'')} q≋q' q'≋q'' = IsEquivalence.trans ∼-isEquiv q≋q' q'≋q''
    
  ≋-isEquiv : IsEquivalence {A = Q/~} _≋_
  ≋-isEquiv = record { refl = λ {q} → ≋-refl {q} ; sym = λ {q} {q'} → ≋-sym {q} {q'} ; trans = λ {q} {q'} {q''} → ≋-trans {q} {q'} {q''} }
  

  p∼q⇔⟪p⟫≈⟪q⟫ : ∀ {p q} → (p ∼ q) ⇔ ⟪ p ⟫ ≈ᵈ ⟪ q ⟫
  p∼q⇔⟪p⟫≈⟪q⟫ = lem₁ , lem₂
    where
      lem₁ : ∀ {p q} → p ∼ q → ⟪ p ⟫ ≈ᵈ ⟪ q ⟫
      lem₁ p∼q = lem₁-⊆ p∼q , lem₁-⊇ p∼q
        where
          lem₁-⊆ : ∀ {p} {q} → p ∼ q → ⟪ p ⟫ ⊆ᵈ ⟪ q ⟫
          lem₁-⊆ {p} {q} p∼q x x∈⟪p⟫ with Dec-∼ x q
          lem₁-⊆ {p} {q} p∼q x x∈⟪p⟫ | yes _    = refl
          lem₁-⊆ {p} {q} p∼q x x∈⟪p⟫ | no  ¬x∼q with Dec-∼ x p
          lem₁-⊆ {p} {q} p∼q x x∈⟪p⟫ | no  ¬x∼q | yes x∼p
            = ⊥-elim (¬x∼q (IsEquivalence.trans ∼-isEquiv x∼p p∼q))
          lem₁-⊆ {p} {q} p∼q x ()    | no  ¬x∼q | no  ¬x∼p

          lem₁-⊇ : ∀ {p} {q} → p ∼ q → ⟪ p ⟫ ⊇ᵈ ⟪ q ⟫
          lem₁-⊇ {p} {q} p∼q x x∈⟪q⟫ with Dec-∼ x p
          lem₁-⊇ {p} {q} p∼q x x∈⟪q⟫ | yes _    = refl
          lem₁-⊇ {p} {q} p∼q x x∈⟪q⟫ | no  ¬x∼o with Dec-∼ x q
          lem₁-⊇ {p} {q} p∼q x x∈⟪q⟫ | no  ¬x∼p | yes x∼q
            = ⊥-elim (¬x∼p (IsEquivalence.trans ∼-isEquiv x∼q (IsEquivalence.sym ∼-isEquiv p∼q)))
          lem₁-⊇ {p} {q} p∼q x ()    | no  ¬x∼p | no  ¬x∼q

      lem₂ : ∀ {p q} → ⟪ p ⟫ ≈ᵈ ⟪ q ⟫ → p ∼ q
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ with p ∈ᵈ? ⟪ q ⟫ | inspect (λ p → p ∈ᵈ? ⟪ q ⟫) p
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ | true  | [ p∈⟪q⟫ ] with Dec-∼ p q
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ | true  | [ p∈⟪q⟫ ] | yes p∼q = p∼q
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ | true  | [   ()  ] | no  _ 
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ | false | [ p∉⟪q⟫ ] = ⊥-elim ((Subset.DecidableSubset.∈-lem₂ {Q} {p} {⟪ q ⟫} p∉⟪q⟫) ((proj₁ ⟪p⟫≈⟪q⟫) p (⟪⟫-lem p)))
