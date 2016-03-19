open import Util
open import Data.Nat
open import Data.Vec renaming (_∈_ to _∈ⱽ_)
open import Subset.VectorRep
{-
module Table (A : Set)(A? : DecEq A)(n : ℕ)(It : Vec A (suc n))(∀a∈It : ∀ a → a ∈ⱽ It)(unique : Unique It)
             (_∼_ : A → A → Set) where
-}

module RelationTable where

open import Data.Bool
open import Relation.Nullary
open import Data.Product
open import Data.Sum

Entry : Set → Set
Entry A = A × A × Bool

Row : Set → ℕ → Set
Row A n = Vec (Entry A) n

Table : Set → ℕ → Set
Table A n = Vec (Row A n) n

makeRow : ∀ {A n} → A → Vec A n → Row A n
makeRow a [] = []
makeRow a (b ∷ bs) = (a , b , false) ∷ makeRow a bs
  
makeTable : ∀ {A m n} → Vec A n → Vec A m → Vec (Row A m) n
makeTable []       bs = []
makeTable (a ∷ as) bs = makeRow a bs ∷ makeTable as bs

search : ∀ {A n} → Table A n → (A × A) → Bool
search []      (a , b) = {!!}
search (x ∷ t) (a , b) = {!!}


module Table-Construction (A : Set)(A? : DecEq A)(n : ℕ)(It : Vec A (suc n))(∀a∈It : ∀ a → a ∈ⱽ It)(unique : Unique It) where
  R-Entry : Set
  R-Entry = Entry A

  R-Table : Set
  R-Table = Table A (suc n)

  R-Row : Set
  R-Row = Row A (suc n)

  table₀ : Table A (suc n)
  table₀ = makeTable It It

  update : R-Entry → Bool → R-Table → R-Table
  update (a , b , _) bool (row ∷ rs) = {!!}
