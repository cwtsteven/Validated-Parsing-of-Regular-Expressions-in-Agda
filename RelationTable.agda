module RelationTable where

open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Util hiding (tail)
open import Data.Nat
open import Data.Vec renaming (_∈_ to _∈ⱽ_)

open import Subset
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep


makeRow : ∀ {ℓ n}{A : Set ℓ} → A → Vec A n → Vec (A × A) n
makeRow a [] = []
makeRow a (b ∷ bs) = (a , b) ∷ makeRow a bs
  
makeColumn : ∀ {ℓ m n}{A : Set ℓ} → Vec A n → Vec A m → Vec (Vec (A × A) m) n
makeColumn []       bs = []
makeColumn (a ∷ as) bs = makeRow a bs ∷ makeColumn as bs

toVec : ∀ {ℓ m n}{A : Set ℓ} → Vec (Vec (A × A) m) n → Vec (A × A) (n * m)
toVec []         = []
toVec (row ∷ rs) = row ++ toVec rs

makeTable : ∀ {ℓ m n}{A : Set ℓ} → Vec A n → Vec A m → Vec (A × A) (n * m)
makeTable as bs = toVec (makeColumn as bs)

module Table-Construction (A : Set)(A? : DecEq A)(n : ℕ)(It : Vec A (suc n))(∀a∈It : ∀ a → a ∈ⱽ It)(unique : Unique It) where
  Table : Set
  Table = Vec (A × A) (suc n * suc n)

  table : Table
  table = makeTable It It

  lem : ∀ {a b a₁ b₁ : A} → (a , b) ≡ (a₁ , b₁) → a ≡ a₁ × b ≡ b₁
  lem refl = refl , refl

  Dec-Pair : DecEq (A × A)
  Dec-Pair (a , b) (a₁ , b₁) with A? a a₁ | A? b b₁
  Dec-Pair (a , b) (.a , .b) | yes refl | yes refl = yes refl
  Dec-Pair (a , b) (a₁ , b₁) | no  a≢a₁ | _        = no (λ x → a≢a₁ (proj₁ (lem x)))
  Dec-Pair (a , b) (a₁ , b₁) | yes _    | no  b≢b₁ = no (λ x → b≢b₁ (proj₂ (lem x)))

  postulate ∀ab∈table : ∀ a b → (a , b) ∈ⱽ table
  --∀ab∈table a b = {!!}

  postulate unique-table : Unique table
  --unique-table = {!!}

  postulate It-lem : {n : ℕ}(as : Vec (A × A) (suc n))
                     → ∀ a → a ∈ⱽ as → a ≡ head as ⊎ a ∈ⱽ mytail as
  
