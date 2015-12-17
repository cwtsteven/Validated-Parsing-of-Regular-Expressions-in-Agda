{-
  This module contains the set of states and its decidable equality
  of each case.

  Steven Cheung 2015.
  Version 10-12-2015
-}

module State where

open import Level
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Unit
open import Data.Empty

open import Util
open import Subset renaming (Ø to ø)

{- Ø states -}
data Ø-State : Set where
 init : Ø-State

DecEq-Ø : DecEq Ø-State
DecEq-Ø init init = yes refl

Ø-List : List Ø-State
Ø-List = init ∷ []



{- ε states -}
data ε-State : Set where
 init  : ε-State

DecEq-ε : DecEq ε-State
DecEq-ε init init   = yes refl

ε-List : List ε-State
ε-List = init ∷ []



{- singleton states -}
data σ-State : Set where
 init   : σ-State
 accept : σ-State

DecEq-σ : DecEq σ-State
DecEq-σ init init     = yes refl
DecEq-σ init accept   = no (λ ())
DecEq-σ accept accept = yes refl
DecEq-σ accept init   = no (λ ())

σ-List : List σ-State
σ-List = init ∷ accept ∷ []



{- union states -}
infix 1 _⊍_
data _⊍_ (A B : Set) : Set where
  init : A ⊍ B
  ⊍inj₁ : A → A ⊍ B
  ⊍inj₂ : B → A ⊍ B

⊍-lem₁ : {A B : Set}{q q' : A}{injq injq' : A ⊍ B} → injq ≡ ⊍inj₁ q → injq' ≡ ⊍inj₁ q' → injq ≡ injq' → q ≡ q'
⊍-lem₁ refl refl refl = refl

⊍-lem₂ : {A B : Set}{q q' : A}{injq injq' : A ⊍ B} → injq ≡ ⊍inj₁ q → injq' ≡ ⊍inj₁ q' → q ≢ q' → injq ≢ injq'
⊍-lem₂ pr₁ pr₂ ¬q≡q' injq≡injq' = ¬q≡q' (⊍-lem₁ pr₁ pr₂ injq≡injq')

⊍-lem₃ : {A B : Set}{q q' : B}{injq injq' : A ⊍ B} → injq ≡ ⊍inj₂ q → injq' ≡ ⊍inj₂ q' → injq ≡ injq' → q ≡ q'
⊍-lem₃ refl refl refl = refl

⊍-lem₄ : {A B : Set}{q q' : B}{injq injq' : A ⊍ B} → injq ≡ ⊍inj₂ q → injq' ≡ ⊍inj₂ q' → q ≢ q' → injq ≢ injq'
⊍-lem₄ pr₁ pr₂ ¬q≡q' injq≡injq' = ¬q≡q' (⊍-lem₃ pr₁ pr₂ injq≡injq')

DecEq-⊍ : {A B : Set} → DecEq A → DecEq B → DecEq (A ⊍ B)
DecEq-⊍ decA decB init init = yes refl
DecEq-⊍ decA decB init (⊍inj₁ _) = no (λ ())
DecEq-⊍ decA decB init (⊍inj₂ _) = no (λ ())
DecEq-⊍ decA decB (⊍inj₁ q) init = no (λ ())
DecEq-⊍ decA decB (⊍inj₁ q) (⊍inj₁ q') with decA q q'
DecEq-⊍ decA decB (⊍inj₁ q) (⊍inj₁ .q) | yes refl = yes refl
DecEq-⊍ decA decB (⊍inj₁ q) (⊍inj₁ q') | no ¬q≡q' = no (⊍-lem₂ refl refl ¬q≡q')
DecEq-⊍ decA decB (⊍inj₁ q) (⊍inj₂ _) = no (λ ())
DecEq-⊍ decA decB (⊍inj₂ q) init = no (λ ())
DecEq-⊍ decA decB (⊍inj₂ q) (⊍inj₂ q') with decB q q'
DecEq-⊍ decA decB (⊍inj₂ q) (⊍inj₂ .q) | yes refl = yes refl
DecEq-⊍ decA decB (⊍inj₂ q) (⊍inj₂ q') | no ¬q≡q' = no (⊍-lem₄ refl refl ¬q≡q')
DecEq-⊍ decA decB (⊍inj₂ q) (⊍inj₁ _) = no (λ ())

⊍-List : {A B : Set} → List A → List B → List (A ⊍ B)
⊍-List as bs = init ∷ map ⊍inj₁ as ++ map ⊍inj₂ bs



{- concatenation states -}
infix 2 _⍟_
data _⍟_ (A B : Set) : Set where
 ⍟inj₁ : A → A ⍟ B
 mid   : A ⍟ B
 ⍟inj₂ : B → A ⍟ B
 
⍟-lem₁ : {A B : Set}{q q' : A}{injq injq' : A ⍟ B} → injq ≡ ⍟inj₁ q → injq' ≡ ⍟inj₁ q' → injq ≡ injq' → q ≡ q'
⍟-lem₁ refl refl refl = refl

⍟-lem₂ : {A B : Set}{q q' : A}{injq injq' : A ⍟ B} → injq ≡ ⍟inj₁ q → injq' ≡ ⍟inj₁ q' → q ≢ q' → injq ≢ injq'
⍟-lem₂ pr₁ pr₂ ¬q≡q' injq≡injq' = ¬q≡q' (⍟-lem₁ pr₁ pr₂ injq≡injq')

⍟-lem₃ : {A B : Set}{q q' : B}{injq injq' : A ⍟ B} → injq ≡ ⍟inj₂ q → injq' ≡ ⍟inj₂ q' → injq ≡ injq' → q ≡ q'
⍟-lem₃ refl refl refl = refl

⍟-lem₄ : {A B : Set}{q q' : B}{injq injq' : A ⍟ B} → injq ≡ ⍟inj₂ q → injq' ≡ ⍟inj₂ q' → q ≢ q' → injq ≢ injq'
⍟-lem₄ pr₁ pr₂ ¬q≡q' injq≡injq' = ¬q≡q' (⍟-lem₃ pr₁ pr₂ injq≡injq')

DecEq-⍟ : {A B : Set} → DecEq A → DecEq B → DecEq (A ⍟ B)
DecEq-⍟ decA decB (⍟inj₁ q) (⍟inj₁ q') with decA q q'
DecEq-⍟ decA decB (⍟inj₁ q) (⍟inj₁ .q) | yes refl = yes refl
DecEq-⍟ decA decB (⍟inj₁ q) (⍟inj₁ q') | no ¬q≡q' = no (⍟-lem₂ refl refl ¬q≡q')
DecEq-⍟ decA decB (⍟inj₁ q) mid        = no (λ ())
DecEq-⍟ decA decB (⍟inj₁ q) (⍟inj₂ q') = no (λ ())
DecEq-⍟ decA decB (⍟inj₂ q) (⍟inj₂ q') with decB q q'
DecEq-⍟ decA decB (⍟inj₂ q) (⍟inj₂ .q) | yes refl = yes refl
DecEq-⍟ decA decB (⍟inj₂ q) (⍟inj₂ q') | no ¬q≡q' = no (⍟-lem₄ refl refl ¬q≡q')
DecEq-⍟ decA decB (⍟inj₂ q) mid        = no (λ ())
DecEq-⍟ decA decB (⍟inj₂ q) (⍟inj₁ q') = no (λ ())
DecEq-⍟ decA decB mid       mid        = yes refl
DecEq-⍟ decA decB mid       (⍟inj₁ q') = no (λ ())
DecEq-⍟ decA decB mid       (⍟inj₂ q') = no (λ ())

⍟-List : {A B : Set} → List A → List B → List (A ⍟ B)
⍟-List as bs = map ⍟inj₁ as ++ mid ∷ map ⍟inj₂ bs



{- kleen star states -}
data _*-State (A : Set) : Set where
 init : A *-State
 inj  : A → A *-State

*-lem₁ : {A : Set}{q q' : A} → inj q ≡ inj q' → q ≡ q'
*-lem₁ refl = refl

*-lem₂ : {A : Set}{q q' : A} → q ≢ q' → inj q ≢ inj q'
*-lem₂ ¬q≡q' injq≡q' = ¬q≡q' (*-lem₁ injq≡q')

DecEq-* : {A : Set} → DecEq A → DecEq (A *-State)
DecEq-* dec init init        = yes refl
DecEq-* dec init (inj _)     = no (λ ())
DecEq-* dec (inj q) (inj q') with dec q q'
DecEq-* dec (inj q) (inj .q) | yes refl = yes refl
DecEq-* dec (inj q) (inj q') | no ¬q≡q' = no (*-lem₂ ¬q≡q')
DecEq-* dec (inj _) init     = no (λ ())

*-List : {A : Set} → List A → List (A *-State)
*-List as = init ∷ map inj as
