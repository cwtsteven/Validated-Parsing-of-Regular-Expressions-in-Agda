{-
  Here is an example of recognising words

  Steven Cheung
  Version 19-03-2016
-}
module Example where

open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Nat

open import Util
open import Subset
open import Subset.DecidableSubset
  renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; Ø to Øᵈ ; _⋃_ to _⋃ᵈ_ ; _⋂_ to _⋂ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ
                 ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv ; ≈-refl to ≈ᵈ-refl ; ≈-trans to ≈ᵈ-trans ; ≈-sym to ≈ᵈ-sym)

data A : Set where
  a : A
  b : A

dec : DecEq A
dec a a = yes refl
dec a b = no (λ ())
dec b a = no (λ ())
dec b b = yes refl

open import Language A dec
open import RegularExpression A dec
open import RegExp-Decidability A dec

regex : RegExp
regex = (σ a ∣ σ b) *

w : Σ*
w = b ∷ a ∷ []

regex⇨w? : Dec (w ∈ (Lᴿ regex))
regex⇨w? = Dec-Lᴿ regex w

regex⇨w : Dec ((a ∷ []) ∈ (Lᴿ (σ a *)))
regex⇨w = yes (suc zero , a ∷ [] , [] , refl , refl , refl)
