module QuotientSet where
open import Util
open import Data.Unit

open import Subset


module Quot (A : Set)(_∼_ : A → A → Set) where
  ⟪_⟫ : A → Subset A -- A → A → Set
  ⟪ a ⟫ = λ b → b ∼ a

  A/∼ : Set₁
  A/∼ = undefined


_/_ : (A : Set) → (A → A → Set) → Set₁
A / _∼_ = Quot.A/∼ A _∼_

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open ≡-Reasoning
{-
Pair : Set
Pair = ℕ × ℕ

_∼_ : Pair → Pair → Set
(a , b) ∼ (c , d) = a + d ≡ c + b

∼-sym : Transitive _∼_
∼-sym {a , b} {c , d} {e , f} prf₁ prf₂ = begin
                                          a + f ≡⟨ undefined ⟩
                                          e + b
                                          ∎
                                          

∼-isEquiv : IsEquivalence _∼_
∼-isEquiv = record { refl = refl ; sym = λ prf → sym prf ; trans = λ prf₁ prf₂ → undefined } -- } trans prf₁ prf₂ }
-}
