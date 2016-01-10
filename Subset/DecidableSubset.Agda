{-
  This module contains the definition of Decidable Subset and its operations.

  Steven Cheung 2015.
  Version 07-01-2016
-}
open import Util
module Subset.DecidableSubset where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Function
open import Data.Empty

-- Decidable Subset
DecSubset : (A : Set) → Set
DecSubset A = A → Bool

-- Empty set
Ø : {A : Set} → DecSubset A
Ø = λ _ → false

-- Singleton
⟦_⟧ : {A : Set} → A → {{dec : DecEq A}} → DecSubset A
⟦ a ⟧ {{dec}} = λ b → decEqToBool dec a b


-- Membership
infix 10 _∈_
_∈_ : {A : Set} → A → DecSubset A → Bool
a ∈ p = p a

infix 10 _∉_
_∉_ : {A : Set} → A → DecSubset A → Bool
a ∉ p = not (a ∈ p)

infix 10 _∈ᵍ_
_∈ᵍ_ : {A : Set} → A → DecSubset A → Set
a ∈ᵍ p = a ∈ p ≡ true

infix 10 _∉ᵍ_
_∉ᵍ_ : {A : Set} → A → DecSubset A → Set
a ∉ᵍ p = ¬ (a ∈ᵍ p)


∈ᵍ-lem₃ : {A : Set}{a : A}{p : DecSubset A}
          → a ∉ᵍ p
          → a ∈ p ≡ false
∈ᵍ-lem₃ {A} {a} {p} a∉ᵍp with a ∈ p
∈ᵍ-lem₃ {A} {a} {p} a∉ᵍp | true  = ⊥-elim (a∉ᵍp refl)
∈ᵍ-lem₃ {A} {a} {p} a∉ᵍp | false = refl

∈ᵍ-lem₂ : {A : Set}{a : A}{p : DecSubset A}
          → a ∈ p ≡ false
          → a ∉ᵍ p
∈ᵍ-lem₂ {A} {a} {p} a∈p≡false a∈ᵍp with a ∈ p
∈ᵍ-lem₂ {A} {a} {p} ()        a∈ᵍp | true 
∈ᵍ-lem₂ {A} {a} {p} a∈p≡false ()   | false

∈ᵍ-lem₁ : {A : Set}{a : A}{p : DecSubset A}
          → a ∈ p ≡ false ⇔ a ∉ᵍ p
∈ᵍ-lem₁ {A} {a} {p} = ∈ᵍ-lem₂ {A} {a} {p} , ∈ᵍ-lem₃ {A} {a} {p}


-- Intersection
infix 11 _⋂_
_⋂_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋂ bs = λ a → a ∈ as ∧ a ∈ bs


-- nion
infix 11 _⋃_
_⋃_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋃ bs = λ a → a ∈ as ∨ a ∈ bs



-- List representation
infix 10 _∈ᴸ_
_∈ᴸ_ : {A : Set} → A → List A → {{dec : DecEq A}} → Bool
(a ∈ᴸ p) {{dec}} = any (λ b → decEqToBool dec a b) p

infix 10 _∉ᴸ_
_∉ᴸ_ : {A : Set} → A → List A → {{dec : DecEq A}} → Bool
(a ∉ᴸ p) {{dec}} = not ((a ∈ᴸ p) {{dec}})

removeDuplicate : {A : Set} → List A → DecEq A → List A
removeDuplicate l dec = removeDuplicate' l [] dec
 where
  removeDuplicate' : {A : Set} → List A → List A → DecEq A → List A
  removeDuplicate' []       l dec = l
  removeDuplicate' (x ∷ xs) l dec = if (x ∈ᴸ l) {{dec}}
                                    then removeDuplicate' xs l dec
                                    else x ∷ removeDuplicate' xs l dec
