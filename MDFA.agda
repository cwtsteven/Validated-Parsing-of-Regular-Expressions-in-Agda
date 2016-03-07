open import Util
module MDFA (Σ : Set)(dec : DecEq Σ) where

open import Data.List hiding (any ; all) 
open import Data.Bool
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset
  renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; Ø to Øᵈ ; _⋃_ to _⋃ᵈ_ ; _⋂_ to _⋂ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ
                 ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ≈-refl to ≈ᵈ-refl ; ≈-trans to ≈ᵈ-trans ; ≈-sym to ≈ᵈ-sym)
open import Data.Vec hiding (_++_) renaming (_∈_ to _∈ⱽ_ ; tail to tailⱽ)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import Language Σ dec
open import DFA Σ dec


record ReachableStateDFA (D : DFA) : Set₁ where
  open DFA D
  open DFA-Operations D
  open DFA-Properties D
  field
    Qᴿ    : DecSubset Q
    ∀qAccess : ∀ q → q ∈ᵈ Qᴿ ⇔ Reachable q
    --δᴿ    : ∀ (q : Q) → q ∈ᵈ Qᴿ → Σ → Σ[ q' ∈ Q ] q' ∈ᵈ Qᴿ
    q₀∈Qᴿ : q₀ ∈ᵈ Qᴿ
    Fᴿ    : DecSubset Q
    Fᴿ⊆Qᴿ : Fᴿ ⊆ᵈ Qᴿ


record Minimal (D : DFA)(R : ReachableStateDFA D) : Set₁ where
  field
    Qᴹ  : Set
    δᴹ  : Qᴹ → Σ → Qᴹ
    q₀ᴹ : Qᴹ
    Fᴹ  : DecSubset Qᴹ


{-
module MDFA-Operations (D : DFA)(M : Minimal D) where
  open DFA D
  open Minimal M
               
  δ* : (q : Q) → q ∈ᵈ Qᴹ → Σ* → Q
  δ* q q∈Qᴹ []      = q
  δ* q q∈Qᴹ (a ∷ w) = δ* (proj₁ (δᴹ q q∈Qᴹ a)) (proj₂ (δᴹ q q∈Qᴹ a)) w
  
  δ₀ : Σ* → Q
  δ₀ w = δ* q₀ q₀∈Qᴹ w


Lᴹ : ∀ {D : DFA} → Minimal D → Language
Lᴹ {D} M = λ w → δ₀ w ∈ᵈ Fᴹ
  where
    open Minimal M
    open MDFA-Operations D M
-}
