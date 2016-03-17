{-
  Here the translation from NFA to DFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung
  Version 15-03-2016
-}
open import Util
module Translation.NFA-DFA (Σ : Set)(dec : DecEq Σ) where

open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (Σ ; map)
open import Data.Empty

open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import NFA Σ dec
open import DFA Σ dec 


powerset-construction : NFA → DFA
powerset-construction nfa =
  record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' ; _≋_ = _≈ᵈ_ ; Dec-≋ = Decidable-≈.Dec-≈ {Q} {∣Q∣-1} Q? It ∀q∈It unique ; ≋-isEquiv = ≈ᵈ-isEquiv ; F-lem = F-lem ; δ-lem = δ-lem }
    where
      open NFA nfa
      open NFA-Operations nfa
      open NFA-Properties nfa
      open Vec-Rep {Q} {∣Q∣-1} Q? It ∀q∈It unique
      Q' : Set
      Q' = DecSubset Q
      
      δ' : Q' → Σ → Q'
      -- qs a = { q' | ∃q∈Q.q ∈ qs ∧ q' ∈ δ q a }
      -- qs a = λ q' → Σ[ q ∈ Q ] ( q ∈ qs × q' ∈ᵈ δ q a )
      δ' qs a q' with Dec-⊢ qs a q'
      ... | yes _ = true
      ... | no  _ = false
      
      q₀' : Q'
      q₀' = ⟦ q₀ ⟧ᵈ {{Q?}}
      
      F' : DecSubset Q'
      -- = { qs | ∃q∈Q. q ∈ qs ∧ q ∈ F }
      -- = λ qs → Σ[ q ∈ Q ] ( q ∈ qs × q ∈ F )
      F' qs with Dec-qs∈F qs
      ... | yes _ = true
      ... | no  _ = false

      δ-lem : ∀ {qs ps : Q'} a
              → qs ≈ᵈ ps
              → δ' qs a ≈ᵈ δ' ps a
      δ-lem {qs} {ps} a qs≈ps = δ-lem₁ , δ-lem₂
        where
          δ-lem₁ : δ' qs a ⊆ᵈ δ' ps a
          δ-lem₁ q q∈δqsa with q ∈ᵈ? δ' ps a | inspect (δ' ps a) q
          δ-lem₁ q q∈δqsa | true  | [ q∈δpsa ] = refl
          δ-lem₁ q q∈δqsa | false | [ q∉δpsa ] with Dec-⊢ ps a q
          δ-lem₁ q q∈δqsa | false | [     () ] | yes _
          δ-lem₁ q q∈δqsa | false | [ q∉δpsa ] | no  ¬∃q with Dec-⊢ qs a q
          δ-lem₁ q q∈δqsa | false | [ q∉δpsa ] | no  ¬∃q | yes (q₁ , q₁∈qs , q∈δq₁a)
            = ⊥-elim (¬∃q (q₁ , proj₁ qs≈ps q₁ q₁∈qs , q∈δq₁a))
          δ-lem₁ q     () | false | [ q∉δpsa ] | no  ¬∃q | no  _
          δ-lem₂ : δ' qs a ⊇ᵈ δ' ps a
          δ-lem₂ q q∈δpsa with q ∈ᵈ? δ' qs a | inspect (δ' qs a) q
          δ-lem₂ q q∈δpsa | true  | [ q∈δqsa ] = refl
          δ-lem₂ q q∈δpsa | false | [ q∉δqsa ] with Dec-⊢ qs a q
          δ-lem₂ q q∈δpsa | false | [     () ] | yes _
          δ-lem₂ q q∈δpsa | false | [ q∉δqsa ] | no  ¬∃q with Dec-⊢ ps a q
          δ-lem₂ q q∈δpsa | false | [ q∉δqsa ] | no  ¬∃q | yes (q₁ , q₁∈ps , q∈δq₁a)
            = ⊥-elim (¬∃q (q₁ , proj₂ qs≈ps q₁ q₁∈ps , q∈δq₁a))
          δ-lem₂ q     () | false | [ q∉δqsa ] | no  ¬∃q | no  _

      F-lem : ∀ {qs ps}
              → qs ≈ᵈ ps
              → qs ∈ᵈ F'
              → ps ∈ᵈ F'
      F-lem {qs} {ps} qs≈ps qs∈F with ps ∈ᵈ? F' | inspect F' ps
      F-lem {qs} {ps} qs≈ps qs∈F | true  | [ ps∈F ] = refl
      F-lem {qs} {ps} qs≈ps qs∈F | false | [ ps∉F ] with Dec-qs∈F ps
      F-lem {qs} {ps} qs≈ps qs∈F | false | [   () ] | yes prf
      F-lem {qs} {ps} qs≈ps qs∈F | false | [ ps∉F ] | no  ¬∃p with Dec-qs∈F qs
      F-lem {qs} {ps} qs≈ps qs∈F | false | [ ps∉F ] | no  ¬∃p | yes (q , q∈qs , q∈F)
        = ⊥-elim (¬∃p (q , proj₁ qs≈ps q q∈qs , q∈F))
      F-lem {qs} {ps} qs≈ps   () | false | [ ps∉F ] | no  ¬∃p | no  _
