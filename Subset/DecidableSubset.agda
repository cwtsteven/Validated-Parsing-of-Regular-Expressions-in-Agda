{-
  Definition of Decidable Subset and its operations.

  Steven Cheung
  Version 15-03-2016
-}
module Subset.DecidableSubset where

open import Util
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
DecSubset : Set → Set
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

-- Reflexivity of ≈
≈-refl : {A : Set} → Reflexive {A = DecSubset A} _≈_
≈-refl = (λ a z → z) , (λ a z → z)

-- Symmetry of ≈
≈-sym : {A : Set} → Symmetric {A = DecSubset A} _≈_
≈-sym (as⊆bs , as⊇bs) = as⊇bs , as⊆bs

-- Transitivity of ≈
≈-trans : {A : Set} → Transitive {A = DecSubset A} _≈_
≈-trans (as⊆bs , as⊇bs) (bs⊆cs , bs⊇cs)
  = (λ a z → bs⊆cs a (as⊆bs a z)) , (λ a z → as⊇bs a (bs⊇cs a z))

-- ≈ is a Equivalence relation
≈-isEquiv : {A : Set} → IsEquivalence {A = DecSubset A} _≈_
≈-isEquiv = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }


-- Proving the decidability of ≈ using vector representation
open import Data.Nat
open import Data.Vec renaming (_∈_ to _∈ⱽ_)
open import Subset.VectorRep hiding (_∈?_ ; ∈-lem₂)

module Decidable-≈ {A : Set}{n : ℕ}(dec : DecEq A)(It : Vec A (suc n))(∀a∈It : ∀ a → a ∈ⱽ It)(unique : Unique It) where
  open Vec-Rep {A} {n} dec It ∀a∈It unique

  -- ⊇ is decidable
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
  
  -- ⊆ is decidable
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
  
  -- ≈ is decidable
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


  ⊆-lem₁ : {as bs : DecSubset A} → ¬ (Σ[ a ∈ A ] (a ∈ as × a ∉ bs)) → as ⊆ bs
  ⊆-lem₁ {as} {bs} ¬∃a∈as a a∈as with a ∈? bs | inspect (λ a → a ∈? bs) a
  ... | true  | [ a∈bs ] = refl
  ... | false | [ a∉bs ] = ⊥-elim (¬∃a∈as (a , a∈as , ∈-lem₂ {A} {a} {bs} a∉bs))

  Dec-any-⊆? : (as bs : DecSubset A) → Dec (any (λ a → a ∈ as × a ∉ bs) It)
  Dec-any-⊆? as bs = helper It
    where
      helper : {n : ℕ}(ps : Vec A n) → Dec (any (λ a → a ∈ as × a ∉ bs) ps)
      helper [] = no (λ z → z)
      helper (p ∷ ps) with p ∈? as | p ∈? bs
      helper (p ∷ ps) | true  | false = yes (inj₁ (refl , (λ ())))
      helper (p ∷ ps) | true  | true  with helper ps
      helper (p ∷ ps) | true  | true  | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | true  | true  | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (true ≡ true × (true ≡ true → ⊥) ⊎ any (λ a → a ∈ as × a ∉ bs) ps)
          ¬any (inj₁ (_ , prf)) = ⊥-elim (prf refl)
          ¬any (inj₂ anyps) = ¬anyps anyps
      helper (p ∷ ps) | false | p∈?F  with helper ps
      helper (p ∷ ps) | false | p∈?F  | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | false | p∈?F  | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (false ≡ true × (p∈?F ≡ true → ⊥) ⊎ any (λ a → a ∈ as × a ∉ bs) ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ anyps) = ¬anyps anyps

  Dec-⊆? : (as bs : DecSubset A) → Dec (Σ[ a ∈ A ] (a ∈ as × a ∉ bs))
  Dec-⊆? as bs with Dec-any-⊆? as bs
  Dec-⊆? as bs | yes prf = yes (Vec-any-lem₂ (λ a → a ∈ as × a ∉ bs) prf)
  Dec-⊆? as bs | no  prf = no  (Vec-any-lem₄ (λ a → a ∈ as × a ∉ bs) prf)

  ⊆-lem₂ : {as bs : DecSubset A} → ¬ as ⊆ bs → Σ[ a ∈ A ] (a ∈ as × a ∉ bs)
  ⊆-lem₂ {as} {bs} as⊈bs with Dec-⊆? as bs
  ... | yes (a , a∈as , a∉bs) = a , a∈as , a∉bs
  ... | no  ¬∃a∈as            = ⊥-elim (as⊈bs (⊆-lem₁ ¬∃a∈as))
