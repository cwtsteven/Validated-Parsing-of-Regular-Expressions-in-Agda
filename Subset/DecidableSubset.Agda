{-
  This module contains the definition of Decidable Subset and its operations.

  Steven Cheung 2015.
  Version 10-01-2016
-}
open import Util
module Subset.DecidableSubset where

open import Data.Bool
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function
open import Data.Unit
open import Data.Empty

-- Decidable Subset
DecSubset : (A : Set) → Set
DecSubset A = A → Bool

-- Empty set
Ø : {A : Set} → DecSubset A
Ø = λ _ → false

-- Singleton
⟦_⟧ : {A : Set} → A → {{dec : DecEq A}} → DecSubset A
⟦ a ⟧ {{dec}}  b with dec a b
⟦ a ⟧ {{dec}} .a | yes refl = true
⟦ a ⟧ {{dec}}  b | no  _    = false

-- Membership
infix 10 _∈?_
_∈?_ : {A : Set} → A → DecSubset A → Bool
a ∈? p = p a

infix 10 _∉?_
_∉?_ : {A : Set} → A → DecSubset A → Bool
a ∉? p = not (a ∈? p)

infix 10 _∈_
_∈_ : {A : Set} → A → DecSubset A → Set
a ∈ p = a ∈? p ≡ true

infix 10 _∉_
_∉_ : {A : Set} → A → DecSubset A → Set
a ∉ p = ¬ (a ∈ p)

-- ∀a. a ∈ ⟦ a ⟧
⟦a⟧-lem₁ : {A : Set}(dec : DecEq A)(a : A) → a ∈ ⟦ a ⟧ {{dec}}
⟦a⟧-lem₁ dec a with dec a a
⟦a⟧-lem₁ dec a | yes refl = refl
⟦a⟧-lem₁ dec a | no  a≢a  = ⊥-elim (a≢a refl)

{- a ∉ p ⇔ a ∈? p ≡ false -}
∈-lem₃ : {A : Set}{a : A}{p : DecSubset A}
          → a ∉ p
          → a ∈? p ≡ false
∈-lem₃ {A} {a} {p} a∉p with a ∈? p
∈-lem₃ {A} {a} {p} a∉p | true  = ⊥-elim (a∉p refl)
∈-lem₃ {A} {a} {p} a∉p | false = refl

∈-lem₂ : {A : Set}{a : A}{p : DecSubset A}
          → a ∈? p ≡ false
          → a ∉ p
∈-lem₂ {A} {a} {p} a∈?p≡false a∈p with a ∈? p
∈-lem₂ {A} {a} {p} ()         a∈p | true 
∈-lem₂ {A} {a} {p} a∈?p≡false ()  | false

∈-lem₁ : {A : Set}{a : A}{p : DecSubset A}
          → a ∈? p ≡ false ⇔ a ∉ p
∈-lem₁ {A} {a} {p} = ∈-lem₂ {A} {a} {p} , ∈-lem₃ {A} {a} {p}
{- a ∉ p ⇔ a ∈? p ≡ false -}

-- Intersection
infix 11 _⋂_
_⋂_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋂ bs = λ a → a ∈? as ∧ a ∈? bs

-- Union
infix 11 _⋃_
_⋃_ : {A : Set} → DecSubset A → DecSubset A → DecSubset A
as ⋃ bs = λ a → a ∈? as ∨ a ∈? bs

-- Subset
infix 10 _⊆_
_⊆_ : {A : Set} → DecSubset A → DecSubset A → Set
as ⊆ bs = ∀ a → a ∈ as → a ∈ bs

-- Superset
infix 10 _⊇_
_⊇_ : {A : Set} → DecSubset A → DecSubset A → Set
as ⊇ bs = bs ⊆ as

-- Equality
infix 10 _≈_
_≈_ : {A : Set} → DecSubset A → DecSubset A → Set
as ≈ bs = (as ⊆ bs) × (as ⊇ bs)

≈-refl : {A : Set} → Reflexive {A = DecSubset A} _≈_
≈-refl = (λ a z → z) , (λ a z → z)

≈-sym : {A : Set} → Symmetric {A = DecSubset A} _≈_
≈-sym (as⊆bs , as⊇bs) = as⊇bs , as⊆bs

≈-trans : {A : Set} → Transitive {A = DecSubset A} _≈_
≈-trans (as⊆bs , as⊇bs) (bs⊆cs , bs⊇cs)
  = (λ a z → bs⊆cs a (as⊆bs a z)) , (λ a z → as⊇bs a (bs⊇cs a z))

-- Can we prove this ?
postulate ≈-subst : {A : Set}{as bs : DecSubset A} → (P : DecSubset A → Set) → as ≈ bs → P as → P bs

{-
open import Data.Nat
open import Data.Vec renaming (_∈_ to _∈ⱽ_)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
-- Vector Representation
module DSub-VSub {A : Set}{n : ℕ}(dec : DecEq A)(It : Vec A n)(∀a∈It : ∀ a → a ∈ⱽ It) where
  open Vec-Rep {A} {n} dec It ∀a∈It renaming (Ø to Øⱽ)
  

  VSub→DSub-lem₁ : {n : ℕ}{it : Vec A n} → VecSubset it → DecSubset A
  VSub→DSub-lem₁ [] = Ø
  VSub→DSub-lem₁ (keep a ∷ as)  b with dec a b
  VSub→DSub-lem₁ (keep a ∷ as) .a | yes refl = true
  VSub→DSub-lem₁ (keep a ∷ as)  b | no  _    = false
  VSub→DSub-lem₁ (skip a ∷ as)  b = false

  DSub→VSub-lem₁ : {n : ℕ} → (it : Vec A n) → DecSubset A → VecSubset it
  DSub→VSub-lem₁ []       bs = []
  DSub→VSub-lem₁ (a ∷ as) bs with a ∈? bs
  DSub→VSub-lem₁ (a ∷ as) bs | true  = keep a ∷ DSub→VSub-lem₁ as bs
  DSub→VSub-lem₁ (a ∷ as) bs | false = skip a ∷ DSub→VSub-lem₁ as bs

  DSub→VSub : DecSubset A → VecSubset It
  DSub→VSub as = DSub→VSub-lem₁ It as

  VSub→DSub : VecSubset It → DecSubset A
  VSub→DSub as = VSub→DSub-lem₁ {it = It} as

  VSub⇔DSub : VecSubset It ⇔ DecSubset A
  VSub⇔DSub = VSub→DSub , DSub→VSub
      

  Dec-⊇ : (as bs : DecSubset A) → Dec (as ⊇ bs)
  Dec-⊇ as bs with Dec-all as bs
    where
      Dec-all : (as bs : DecSubset A) → Dec (all (λ a → a ∈ bs → a ∈ as) It)
      Dec-all as bs = helper It
        where
          helper : {n : ℕ}(xs : Vec A n) → Dec (all (λ a → a ∈ bs → a ∈ as) xs)
          helper [] = yes tt
          helper (x ∷ xs) with x ∈? bs | x ∈? as
          helper (x ∷ xs) | true  | true  with helper xs
          helper (x ∷ xs) | true  | true  | yes allxs = yes ((λ _ → refl) , allxs)
          helper (x ∷ xs) | true  | true  | no ¬allxs = no ¬all
            where
              ¬all : ¬ ((true ≡ true → true ≡ true) × all (λ a → a ∈ bs → a ∈ as) xs)
              ¬all (_ , allxs) = ¬allxs allxs
          helper (x ∷ xs) | true  | false = no ¬all
            where
              ¬all : ¬ ((true ≡ true → false ≡ true) × all (λ a → a ∈ bs → a ∈ as) xs)
              ¬all (absurd , _) = Bool-lem₁₂ (absurd refl)
          helper (x ∷ xs) | false | a∈bs  with helper xs
          helper (x ∷ xs) | false | a∈bs  | yes allxs = yes ((λ ()) , allxs)
          helper (x ∷ xs) | false | a∈bs  | no ¬allxs = no ¬all
            where
              ¬all : ¬ ((false ≡ true → a∈bs ≡ true) × all (λ a → a ∈ bs → a ∈ as) xs)
              ¬all (_ , allxs) = ¬allxs allxs
  ... | yes prf = yes (Vec-all-lem₂ (λ a → a ∈ bs → a ∈ as) prf)
  ... | no  prf = no  (Vec-all-lem₄ (λ a → a ∈ bs → a ∈ as) prf)
  
  
  Dec-⊆ : (as bs : DecSubset A) → Dec (as ⊆ bs)
  Dec-⊆ as bs with Dec-all as bs
    where
      Dec-all : (as bs : DecSubset A) → Dec (all (λ a → a ∈ as → a ∈ bs) It)
      Dec-all as bs = helper It
        where
          helper : {n : ℕ}(xs : Vec A n) → Dec (all (λ a → a ∈ as → a ∈ bs) xs)
          helper [] = yes tt
          helper (x ∷ xs) with x ∈? as | x ∈? bs
          helper (x ∷ xs) | true  | true  with helper xs
          helper (x ∷ xs) | true  | true  | yes allxs = yes ((λ _ → refl) , allxs)
          helper (x ∷ xs) | true  | true  | no ¬allxs = no ¬all
            where
              ¬all : ¬ ((true ≡ true → true ≡ true) × all (λ a → a ∈ as → a ∈ bs) xs)
              ¬all (_ , allxs) = ¬allxs allxs
          helper (x ∷ xs) | true  | false = no ¬all
            where
              ¬all : ¬ ((true ≡ true → false ≡ true) × all (λ a → a ∈ as → a ∈ bs) xs)
              ¬all (absurd , _) = Bool-lem₁₂ (absurd refl)
          helper (x ∷ xs) | false | a∈bs  with helper xs
          helper (x ∷ xs) | false | a∈bs  | yes allxs = yes ((λ ()) , allxs)
          helper (x ∷ xs) | false | a∈bs  | no ¬allxs = no ¬all
            where
              ¬all : ¬ ((false ≡ true → a∈bs ≡ true) × all (λ a → a ∈ as → a ∈ bs) xs)
              ¬all (_ , allxs) = ¬allxs allxs
  ... | yes prf = yes (Vec-all-lem₂ (λ a → a ∈ as → a ∈ bs) prf)
  ... | no  prf = no  (Vec-all-lem₄ (λ a → a ∈ as → a ∈ bs) prf)
  
  
  Dec-≈ : (as bs : DecSubset A) → Dec (as ≈ bs)
  Dec-≈ as bs with Dec-⊆ as bs | Dec-⊇ as bs
  Dec-≈ as bs | yes as⊆bs | yes as⊇bs = yes (as⊆bs , as⊇bs)
  Dec-≈ as bs | no  as⊈bs | _         = no ¬eq
    where
      ¬eq : ¬ (as ≈ bs)
      ¬eq (as⊆bs , _) = as⊈bs as⊆bs
  Dec-≈ as bs | _        | no  as⊉bs  = no ¬eq
    where
      ¬eq : ¬ (as ≈ bs)
      ¬eq (_ , as⊇bs) = as⊉bs as⊇bs
-}
