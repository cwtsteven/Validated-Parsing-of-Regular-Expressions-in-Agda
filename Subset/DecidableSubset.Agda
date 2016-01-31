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
open import Data.Sum
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


-- List representation
{-
infix 10 _∈ᴸ_
_∈ᴸ_ : {A : Set}(a : A)(as : List A) → {{dec : DecEq A}} → Bool
(a ∈ᴸ [])       {{dec}} = false
(a ∈ᴸ ( b ∷ bs)) {{dec}} with dec a b
(a ∈ᴸ (.a ∷ bs)) {{dec}} | yes refl = true
(a ∈ᴸ ( b ∷ bs)) {{dec}} | no  _    = (a ∈ᴸ bs) {{dec}}
--(a ∈ᴸ as) {{dec}} = any (λ b → decEqToBool dec a b) as


infix 10 _∈ᴸᵍ_
_∈ᴸᵍ_ : {A : Set}(a : A)(as : List A) → {{dec : DecEq A}} → Set
(a ∈ᴸᵍ as) {{dec}} = (a ∈ᴸ as) {{dec}} ≡ true

∈ᴸ-lem₃ : {A : Set}(dec : DecEq A)(a : A)(as : List A) → (a ∈ᴸᵍ (a ∷ as)) {{dec}}
∈ᴸ-lem₃ dec a as with dec a a
∈ᴸ-lem₃ dec a as | yes refl = refl
∈ᴸ-lem₃ dec a as | no  a≢a  = ⊥-elim (a≢a refl)

∈ᴸ-lem₁ : {A B : Set}(decA : DecEq A)(decB : DecEq B)(f : A → B) → Injective f → (a : A)(as : List A) → (a ∈ᴸᵍ as) {{decA}} → (f a ∈ᴸᵍ Data.List.map f as) {{decB}}
∈ᴸ-lem₁ decA decB f f-inj a [] prf = prf
∈ᴸ-lem₁ decA decB f f-inj a ( x ∷ as) prf with decA a x
∈ᴸ-lem₁ decA decB f f-inj a (.a ∷ as) prf | yes refl = ∈ᴸ-lem₃ decB (f a) _
∈ᴸ-lem₁ decA decB f f-inj a ( x ∷ as) prf | no  ¬a≡x with decB (f a) (f x)
∈ᴸ-lem₁ decA decB f f-inj a ( x ∷ as) prf | no  ¬a≡x | yes fa≡fx = ⊥-elim (¬a≡x (f-inj a x fa≡fx))
∈ᴸ-lem₁ decA decB f f-inj a ( x ∷ as) prf | no  ¬a≡x | no  _     = ∈ᴸ-lem₁ decA decB f f-inj a as prf

∈ᴸ-lem₂ : {A : Set}(dec : DecEq A) → ∀ a as bs → (a ∈ᴸ (as ++ bs)) {{dec}} ≡ (a ∈ᴸ as) {{dec}} ∨ (a ∈ᴸ bs) {{dec}}
∈ᴸ-lem₂ dec a [] bs       = refl
∈ᴸ-lem₂ dec a ( x ∷ as) bs with dec a x
∈ᴸ-lem₂ dec a (.a ∷ as) bs | yes refl = refl
∈ᴸ-lem₂ dec a ( x ∷ as) bs | no  _    = ∈ᴸ-lem₂ dec a as bs


module List-Rep-Lemmas (A : Set)(dec : DecEq A)(It : List A)(∀a∈L : ∀ a → (a ∈ᴸᵍ It) {{dec}}) where
                                                                                    
  apply : (P : A → Set) → List A → Set
  apply P []       = ⊥
  apply P (a ∷ as) = P a ⊎ apply P as

  List-Rep-lem₄ : (P : A → Set)(as : List A) → Σ[ a ∈ A ] ( P a × (a ∈ᴸᵍ as) {{dec}} ) → apply P as
  List-Rep-lem₄ P []       ( b , Pb , ())
  List-Rep-lem₄ P (a ∷ as) ( b , Pb , q∈pps) with dec b a
  List-Rep-lem₄ P (a ∷ as) (.a , Pa , q∈pps) | yes refl = inj₁ Pa
  List-Rep-lem₄ P (a ∷ as) ( b , Pb , q∈pps) | no  q≢p  = inj₂ (List-Rep-lem₄ P as (b , Pb , q∈pps))
                                                                                             
  List-Rep-lem₃ : (P : A → Set) → Σ[ a ∈ A ] P a → apply P It
  List-Rep-lem₃ P (a , Pa) = List-Rep-lem₄ P It (a , Pa , ∀a∈L a)
                                                               
  List-Rep-lem₅ : (P : A → Set)(as : List A) → apply P as → Σ[ a ∈ A ] P a
  List-Rep-lem₅ P []       ()
  List-Rep-lem₅ P (a ∷ as) (inj₁ Pa)    = a , Pa
  List-Rep-lem₅ P (a ∷ as) (inj₂ apply) = List-Rep-lem₅ P as apply
                                                             
  List-Rep-lem₂ : (P : A → Set) → apply P It → Σ[ a ∈ A ] P a
  List-Rep-lem₂ P prf = List-Rep-lem₅ P It prf

  List-Rep-lem₁ : (P : A → Set) → apply P It ⇔ Σ[ a ∈ A ] P a
  List-Rep-lem₁ P = List-Rep-lem₂ P , List-Rep-lem₃ P

  List-Rep-lem₆ : (P : A → Set) → ¬ apply P It → ¬ (Σ[ a ∈ A ] P a)
  List-Rep-lem₆ P ¬apply prf = ⊥-elim (¬apply (List-Rep-lem₃ P prf))
                                                             
-}
