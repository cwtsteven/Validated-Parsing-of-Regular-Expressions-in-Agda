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
open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Data.Vec hiding (_++_) renaming (_∈_ to _∈ⱽ_ ; tail to tailⱽ)

open import Subset.DecidableSubset
  renaming (_∈_ to _∈ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import NFA Σ dec
open import DFA Σ dec 

module Powerset-Construction (nfa : NFA) where
  open NFA nfa
  open NFA-Operations nfa
  open Vec-Rep {Q} {_} Q? It ∀q∈It unique

  -- proving the Decidability of (q' ∈ δ qs a) using Vector reprsentation
  Dec-any-⊢ : ∀ qs a q' → Dec (any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) It)
  Dec-any-⊢ qs a q' = helper It
    where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) ps)
      helper [] = no (λ z → z)
      helper (p ∷ ps) with p ∈ᵈ? qs | q' ∈ᵈ? δ p a
      helper (p ∷ ps) | true  | true  = yes (inj₁ (refl , refl))
      helper (p ∷ ps) | true  | false with helper ps
      helper (p ∷ ps) | true  | false | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | true  | false | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (true ≡ true × false ≡ true ⊎ any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) ps)
          ¬any (inj₁ (_ , ()))
          ¬any (inj₂ anyps) = ¬anyps anyps
      helper (p ∷ ps) | false | q'∈?δpa  with helper ps
      helper (p ∷ ps) | false | q'∈?δpa  | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | false | q'∈?δpa  | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (false ≡ true × q'∈?δpa ≡ true ⊎ any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ anyps) = ¬anyps anyps

  -- proving the Decidability of (q' ∈ δ qs a)
  Dec-⊢ : ∀ qs a q' → Dec ( Σ[ q ∈ Q ] ( q ∈ᵈ qs × q' ∈ᵈ δ q a ) )
  Dec-⊢ qs a q' with Dec-any-⊢ qs a q'
  Dec-⊢ qs a q' | yes prf = yes (Vec-any-lem₂ (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) prf)
  Dec-⊢ qs a q' | no  prf = no  (Vec-any-lem₄ (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) prf)


  -- proving the Decidability of (qs ∈ F) using Vector representation
  Dec-any-qs∈F : ∀ qs → Dec ( any (λ q → q ∈ᵈ qs × q ∈ᵈ F) It )
  Dec-any-qs∈F qs = helper It
    where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (any (λ q → q ∈ᵈ qs × q ∈ᵈ F) ps)
      helper [] = no (λ z → z)
      helper (p ∷ ps) with p ∈ᵈ? qs | p ∈ᵈ? F
      helper (p ∷ ps) | true  | true  = yes (inj₁ (refl , refl))
      helper (p ∷ ps) | true  | false with helper ps
      helper (p ∷ ps) | true  | false | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | true  | false | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (true ≡ true × false ≡ true ⊎ any (λ q → q ∈ᵈ qs × q ∈ᵈ F) ps)
          ¬any (inj₁ (_ , ()))
          ¬any (inj₂ anyps) = ¬anyps anyps
      helper (p ∷ ps) | false | p∈?F  with helper ps
      helper (p ∷ ps) | false | p∈?F  | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | false | p∈?F  | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (false ≡ true × p∈?F ≡ true ⊎ any (λ q → q ∈ᵈ qs × q ∈ᵈ F) ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ anyps) = ¬anyps anyps

  -- proving the Decidability of (qs ∈ F) using Vector representation
  Dec-qs∈F : ∀ qs → Dec ( Σ[ q ∈ Q ] ( q ∈ᵈ qs × q ∈ᵈ F) )
  Dec-qs∈F qs with Dec-any-qs∈F qs
  Dec-qs∈F qs | yes prf = yes (Vec-any-lem₂ (λ q → q ∈ᵈ qs × q ∈ᵈ F) prf)
  Dec-qs∈F qs | no  prf = no  (Vec-any-lem₄ (λ q → q ∈ᵈ qs × q ∈ᵈ F) prf)



powerset-construction : NFA → DFA
powerset-construction nfa =
  record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' ; _≋_ = _≈ᵈ_ ; ≋-isEquiv = ≈ᵈ-isEquiv ; F-lem = F-lem ; δ-lem = δ-lem }
    where
      open NFA nfa
      open NFA-Operations nfa
      open NFA-Properties nfa
      open Powerset-Construction nfa
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
