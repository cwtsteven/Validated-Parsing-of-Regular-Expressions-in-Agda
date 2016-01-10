{-
  This module contains the definition of Decidable Subset and its operations.

  Steven Cheung 2015.
  Version 10-01-2016
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

{- a ∉ᵍ p ⇔ a ∈ᵈ p ≡ false -}
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
{- a ∉ᵍ p ⇔ a ∈ᵈ p ≡ false -}

-- Intersection
infix 11 _⋂_
_⋂_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋂ bs = λ a → a ∈ as ∧ a ∈ bs

-- Union
infix 11 _⋃_
_⋃_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋃ bs = λ a → a ∈ as ∨ a ∈ bs



-- List representation
open import Data.Vec renaming (_∈_ to _∈ⱽ_)
open import Data.Nat

data Sub (A : Set) : Set where
 keep : A → Sub A
 cast : A → Sub A

DecEq-Sub : {A : Set} → DecEq A → DecEq (Sub A)
DecEq-Sub dec (keep a) (keep  b) with dec a b
DecEq-Sub dec (keep a) (keep .a) | yes refl = yes refl
DecEq-Sub dec (keep a) (keep  b) | no a≢b   = no  (λ a≡b → a≢b (lem₁ a b a≡b))
 where
  lem₁ : {A : Set}(a b : A) → keep a ≡ keep b → a ≡ b
  lem₁ a .a refl = refl
DecEq-Sub dec (keep a) (cast  b) = no (λ ())
DecEq-Sub dec (cast a) (keep  b) = no (λ ())
DecEq-Sub dec (cast a) (cast  b) with dec a b
DecEq-Sub dec (cast a) (cast .a) | yes refl = yes refl
DecEq-Sub dec (cast a) (cast  b) | no a≢b   = no  (λ a≡b → a≢b (lem₁ a b a≡b))
 where
  lem₁ : {A : Set}(a b : A) → cast a ≡ cast b → a ≡ b
  lem₁ a .a refl = refl

_∈ᴸ_ : {A : Set}(a : A)(as : List (Sub A)) → {{dec : DecEq A}} → Bool
(a ∈ᴸ []) {{dec}}            = false
(a ∈ᴸ (keep b ∷ as)) {{dec}} = if decEqToBool dec a b
                               then true
                               else (a ∈ᴸ as) {{dec}}
(a ∈ᴸ (cast b ∷ as)) {{dec}} = if decEqToBool dec a b
                               then false
                               else (a ∈ᴸ as) {{dec}}

_∉ᴸ_ : {A : Set}(a : A)(as : List (Sub A)) → {{dec : DecEq A}} → Bool
(a ∉ᴸ as) {{dec}} = not ((a ∈ᴸ as) {{dec}})

set : {A : Set} → (A → Bool) → List (Sub A) → DecEq A → List (Sub A)
set as []            dec = []
set as (keep b ∷ bs) dec = if as b
                           then keep b ∷ set as bs dec
                           else cast b ∷ set as bs dec
set as (cast b ∷ bs) dec = if as b
                           then keep b ∷ set as bs dec
                           else cast b ∷ set as bs dec
