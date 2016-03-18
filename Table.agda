open import Util
open import Data.Nat
open import Data.Vec renaming (_∈_ to _∈ⱽ_)
open import Subset.VectorRep

module Table (A : Set)(A? : DecEq A)(n : ℕ)(It : Vec A (suc n))(∀a∈It : ∀ a → a ∈ⱽ It)(unique : Unique It)
             (_∼_ : A → A → Set) where

open import Relation.Nullary
open import Data.Product
open import Data.Sum

Entry : Set
Entry = (a : A) → (b : A) → (a ∼ b) ⊎ ¬ (a ∼ b)

postulate row : Vec Entry (suc n)

postulate table₀ : Vec (Vec Entry (suc n)) (suc n)
