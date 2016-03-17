{-
  Here the translation from ε-NFA to NFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung
  Version 15-03-2016
-}
open import Util
module Translation.eNFA-NFA (Σ : Set)(dec : DecEq Σ) where

open import Data.Bool

open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Language Σ dec hiding (⟦_⟧)
open import eNFA Σ dec
open import NFA Σ dec 

remove-ε-step : ε-NFA → NFA
remove-ε-step nfa =
  record { Q = Q ; Q? = Q? ; δ = δ' ; q₀ = q₀ ; F = F' ; ∣Q∣-1 = _ ; It = It ; ∀q∈It = ∀q∈It ; unique = unique }
    where
      open ε-NFA nfa
      open ε-NFA-Operations nfa
      open ε-NFA-Properties nfa

      δ' : Q → Σ → DecSubset Q
      --     = { q' | q' ∈ δ q (α a) ∨ ∃p∈Q. q' ∈ δ p (α a) ∧ p ∈ ε-closure(q) }
      --     = λ q' → q' ∈ δ q (α a) ⊎ Σ[ p ∈ Q ] (q' ∈ δ p (α a) × p ∈ ε-closure q)
      δ' q a = λ q' → q' ∈ᵈ? δ q (α a) ∨ ∃q⊢a-q'? (Dec-→ε*⊢ q a q')

      F' : DecSubset Q
      -- = { q | q ∈ F ∨ ∃p∈Q. p ∈ F ∧ p ∈ ε-closure(q) }
      -- = λ q → q ∈ F ⊎ Σ[ p ∈ Q ] (p ∈ F × p ∈ ε-closure q)
      F' = λ q → q ∈ᵈ? F ∨ ∃q∈F? (Dec-→ε*∈F q)
