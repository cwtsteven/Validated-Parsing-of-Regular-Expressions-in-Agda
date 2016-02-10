{-
  This module contains the set of states and its decidable equality
  of each case.

  Steven Cheung 2015.
  Version 07-01-2016
-}

module State where

--open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Vec hiding (init) renaming (_∈_ to _∈ⱽ_)

open import Util
open import Subset renaming (Ø to ø)
open import Subset.DecidableSubset
open import Subset.VectorRep

{- Ø states -}
data Ø-State : Set where
  init : Ø-State

DecEq-Ø : DecEq Ø-State
DecEq-Ø init init = yes refl

Ø-Vec : Vec Ø-State 1
Ø-Vec = init ∷ []

unique-Ø : Unique Ø-Vec
unique-Ø = tt



{- ε states -}
data ε-State : Set where
  init : ε-State

DecEq-ε : DecEq ε-State
DecEq-ε init init = yes refl

ε-Vec : Vec ε-State 1
ε-Vec = init ∷ []

unique-ε : Unique ε-Vec
unique-ε = tt


{- singleton states -}
data σ-State : Set where
  init   : σ-State
  accept : σ-State

DecEq-σ : DecEq σ-State
DecEq-σ init init     = yes refl
DecEq-σ init accept   = no (λ ())
DecEq-σ accept accept = yes refl
DecEq-σ accept init   = no (λ ())

σ-Vec : Vec σ-State 2
σ-Vec = init ∷ accept ∷ []

unique-σ : Unique σ-Vec
unique-σ = prf , tt
  where
    prf : ¬ init ∈ⱽ accept ∷ []
    prf (there ())


{- union states -}
infix 1 _⊍_
data _⊍_ (A B : Set) : Set where
  init  : A ⊍ B
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

⊍-Vec : {A B : Set}{n m : ℕ} → Vec A n → Vec B m → Vec (A ⊍ B) (suc n + m)
⊍-Vec as bs = init ∷ map ⊍inj₁ as ++ map ⊍inj₂ bs

⊍inj₁-Injective : {A B : Set} → Injective {A} {A ⊍ B} ⊍inj₁
⊍inj₁-Injective refl = refl

⊍inj₂-Injective : {A B : Set} → Injective {B} {A ⊍ B} ⊍inj₂
⊍inj₂-Injective refl = refl

unique-⊍ : {A B : Set}{n m : ℕ}(It₁ : Vec A (suc n))(It₂ : Vec B (suc m)) → Unique It₁ → Unique It₂ → Unique (⊍-Vec It₁ It₂)
unique-⊍ (a ∷ as) bs un-as un-bs = ¬init∈V , prf a as bs un-as un-bs
  where
    ¬init∈asbs : {A B : Set}{n m : ℕ}(as : Vec A n)(bs : Vec B m) → ¬ init ∈ⱽ (map ⊍inj₁ as) ++ map ⊍inj₂ bs
    ¬init∈asbs [] [] ()
    ¬init∈asbs [] (b ∷ bs) (there x) = ¬init∈asbs [] bs x
    ¬init∈asbs (a ∷ as) bs (there x) = ¬init∈asbs as bs x
    ¬init∈V : ¬ init ∈ⱽ ⊍inj₁ a ∷ (map ⊍inj₁ as) ++ map ⊍inj₂ bs
    ¬init∈V (there prf) = ¬init∈asbs as bs prf
    ¬a∈bs : {A B : Set}{m : ℕ}(a : A)(bs : Vec B m) → ¬ ⊍inj₁ a ∈ⱽ (map ⊍inj₂ bs)
    ¬a∈bs a [] ()
    ¬a∈bs a (b ∷ bs) (there prf) = ¬a∈bs a bs prf
    prf : {A B : Set}{n m : ℕ}(a : A)(as : Vec A n)(bs : Vec B (suc m)) → Unique (a ∷ as) → Unique bs → Unique (⊍inj₁ a ∷ (map ⊍inj₁ as) ++ map ⊍inj₂ bs)
    prf a []       (b ∷ bs) un-aas un-bs = ¬a∈bs a (b ∷ bs) , Unique-lem₁ ⊍inj₂ ⊍inj₂-Injective (b ∷ bs) un-bs
    prf a (x ∷ as) (b ∷ bs) un-aas un-bs = helper₁ a x as b bs un-aas , helper₂ a x as b bs un-aas un-bs
      where --let temp = lem₂ (proj₁ un-aas) in 
        helper₁ : {A B : Set}{n m : ℕ}(a x : A)(as : Vec A n)(b : B)(bs : Vec B m)
                  → Unique (a ∷ x ∷ as)
                  → ¬ ⊍inj₁ a ∈ⱽ ⊍inj₁ x ∷ (map ⊍inj₁ as) ++ map ⊍inj₂ (b ∷ bs)
        helper₁ a .a as b bs unaxas here = proj₁ unaxas here
        helper₁ a x [] b bs unaxas (there prf) = ¬a∈bs a (b ∷ bs) prf
        helper₁ a x (y ∷ as) b bs (proj₁ , proj₂ , proj₃) (there prf) = helper₁ a y as b bs ((λ x₁ → proj₁ (there x₁)) , proj₃) prf
        helper₂ : {A B : Set}{n m : ℕ}(a x : A)(as : Vec A n)(b : B)(bs : Vec B m)
                  → Unique (a ∷ x ∷ as)
                  → Unique (b ∷ bs)
                  → Unique (⊍inj₁ x ∷ (replicate ⊍inj₁ ⊛ as) ++ map ⊍inj₂ (b ∷ bs))
        helper₂ a x [] b bs un-axas unbbs = (λ prf → ¬a∈bs x (b ∷ bs) prf) , Unique-lem₁ ⊍inj₂ ⊍inj₂-Injective (b ∷ bs) unbbs
        helper₂ a x (y ∷ as) b bs un-axas unbbs = (λ prf → helper₁ x y as b bs (proj₂ un-axas) prf) , helper₂ x y as b bs (proj₂ un-axas) unbbs





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

⍟-Vec : {A B : Set}{n m : ℕ} → Vec A n → Vec B m → Vec (A ⍟ B) (n + suc m)
⍟-Vec as bs = map ⍟inj₁ as ++ mid ∷ map ⍟inj₂ bs

⍟inj₁-Injective : {A B : Set} → Injective {A} {A ⍟ B} ⍟inj₁
⍟inj₁-Injective refl = refl

⍟inj₂-Injective : {A B : Set} → Injective {B} {A ⍟ B} ⍟inj₂
⍟inj₂-Injective refl = refl

unique-⍟ : {A B : Set}{n m : ℕ}(It₁ : Vec A (suc n))(It₂ : Vec B (suc m)) → Unique It₁ → Unique It₂ → Unique (⍟-Vec It₁ It₂)
unique-⍟ (a ∷ [])     (b ∷ bs) un-as un-bs = ¬a∈midbs a (b ∷ bs) , ¬mid∈bs b bs , Unique-lem₁ ⍟inj₂ ⍟inj₂-Injective (b ∷ bs) un-bs
  where
    ¬a∈bs : {A B : Set}{m : ℕ}(a : A)(bs : Vec B m) → ¬ ⍟inj₁ a ∈ⱽ (map ⍟inj₂ bs)
    ¬a∈bs a [] ()
    ¬a∈bs a (b ∷ bs) (there prf) = ¬a∈bs a bs prf
    ¬a∈midbs : {A B : Set}{m : ℕ}(a : A)(bs : Vec B m) → ¬ ⍟inj₁ a ∈ⱽ mid ∷ (map ⍟inj₂ bs)
    ¬a∈midbs a bs (there prf) = ¬a∈bs a bs prf
    ¬mid∈bs : {m : ℕ}{B : Set}(b : B)(bs : Vec B m) → ¬ mid ∈ⱽ map ⍟inj₂ (b ∷ bs)
    ¬mid∈bs b₁ [] (there ())
    ¬mid∈bs b₁ (x ∷ bs₁) (there prf) = ¬mid∈bs x bs₁ prf
unique-⍟ (a ∷ x ∷ as) (b ∷ bs) un-as un-bs = helper₁ a x as b bs un-as , helper₂ a x as b bs un-as un-bs
  where
    ¬a∈bs : {A B : Set}{m : ℕ}(a : A)(bs : Vec B m) → ¬ ⍟inj₁ a ∈ⱽ (map ⍟inj₂ bs)
    ¬a∈bs a [] ()
    ¬a∈bs a (b ∷ bs) (there prf) = ¬a∈bs a bs prf
    ¬a∈midbs : {A B : Set}{m : ℕ}(a : A)(bs : Vec B m) → ¬ ⍟inj₁ a ∈ⱽ mid ∷ (map ⍟inj₂ bs)
    ¬a∈midbs a bs (there prf) = ¬a∈bs a bs prf
    helper₁ : {A B : Set}{n m : ℕ}(a x : A)(as : Vec A n)(b : B)(bs : Vec B m)
              → Unique (a ∷ x ∷ as)
              → ¬ ⍟inj₁ a ∈ⱽ ⍟inj₁ x ∷ (map ⍟inj₁ as) ++ mid ∷ map ⍟inj₂ (b ∷ bs)
    helper₁ a₁ .a₁ as₁ b₁ bs₁ un-as₁ here = proj₁ un-as₁ here
    helper₁ a₁ x₁ [] b₁ bs₁ (proj₁ , proj₂) (there prf) = ¬a∈midbs a₁ (b₁ ∷ bs₁) prf
    helper₁ a₁ x₁ (x₂ ∷ as₁) b₁ bs₁ (proj₁ , proj₂ , proj₃) (there prf)
      = helper₁ a₁ x₂ as₁ b₁ bs₁ ((λ x₃ → proj₁ (there x₃)) , proj₃) prf
    helper₂ : {A B : Set}{n m : ℕ}(a x : A)(as : Vec A n)(b : B)(bs : Vec B m)
              → Unique (a ∷ x ∷ as)
              → Unique (b ∷ bs)
              → Unique (⍟inj₁ x ∷ (replicate ⍟inj₁ ⊛ as) ++ mid ∷ map ⍟inj₂ (b ∷ bs))
    helper₂ {A} {B} a₁ x₁ [] b₁ bs₁ un-axas un-bbs = (λ x₂ → ¬a∈midbs x₁ (b₁ ∷ bs₁) x₂) , (λ prf → ¬mid∈bs b₁ bs₁ prf) , (Unique-lem₁ ⍟inj₂ ⍟inj₂-Injective (b₁ ∷ bs₁) un-bbs)
      where
        ¬mid∈bs : {m : ℕ}(b : B)(bs : Vec B m) → ¬ mid ∈ⱽ map ⍟inj₂ (b ∷ bs)
        ¬mid∈bs b₁ [] (there ())
        ¬mid∈bs b₁ (x ∷ bs₁) (there prf) = ¬mid∈bs x bs₁ prf
    helper₂ a₁ x₁ (x₂ ∷ as₁) b₁ bs₁ un-axas un-bbs = (λ x₃ → helper₁ x₁ x₂ as₁ b₁ bs₁ (proj₂ un-axas) x₃) , (helper₂ x₁ x₂ as₁ b₁ bs₁ (proj₂ un-axas) un-bbs)



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

*-Vec : {A : Set}{n : ℕ} → Vec A n → Vec (A *-State) (suc n)
*-Vec as = init ∷ map inj as

inj-Injective : {A : Set} → Injective {A} {A *-State} inj
inj-Injective refl = refl

unique-* : {A : Set}{n : ℕ}(It₁ : Vec A (suc n))→ Unique It₁ → Unique (*-Vec It₁)
unique-* (a ∷ as) un-as = ¬init∈V a as , prf a as un-as
  where
    ¬init∈as : {A : Set}{n : ℕ}(a : A)(as : Vec A n) → ¬ init ∈ⱽ (map inj (a ∷ as))
    ¬init∈as a₁ [] (there ())
    ¬init∈as a (x ∷ as) (there prf) = ¬init∈as x as prf
    ¬init∈V : {A : Set}{n : ℕ}(a : A)(as : Vec A n) → ¬ init ∈ⱽ inj a ∷ (map inj as)
    ¬init∈V a as prf = ¬init∈as a as prf
    prf : {A : Set}{n : ℕ}(a : A)(as : Vec A n) → Unique (a ∷ as) → Unique (inj a ∷ (map inj as))
    prf a₁ [] un-aas = tt
    prf a₁ (x ∷ as₁) (proj₁ , proj₂) = helper₁ a₁ x as₁ (proj₁ , proj₂) , (Unique-lem₁ inj inj-Injective (x ∷ as₁) proj₂)
      where
        helper₁ : {A : Set}{n : ℕ}(a x : A)(as : Vec A n) → Unique (a ∷ x ∷ as) → ¬ inj a ∈ⱽ inj x ∷ (map inj as)
        helper₁ a₂ .a₂ [] (proj₃ , proj₄) here = proj₃ here
        helper₁ a₂ x₁  [] (proj₃ , proj₄) (there ())
        helper₁ a₂ .a₂ (x₂ ∷ as₂) (proj₃ , proj₄) here = proj₃ here
        helper₁ a₂ x₁ (x₂ ∷ as₂) (proj₃ , proj₄ , proj₅) (there x₃) = helper₁ a₂ x₂ as₂ ((λ x₄ → proj₃ (there x₄)) , proj₅) x₃
