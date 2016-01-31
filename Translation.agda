{-
  Here the translation of a regular expression to a DFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung 2015.
  Version 10-01-2016
-}
open import Util
module Translation (Σ : Set)(dec : DecEq Σ) where

open import Level
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum hiding (map)
open import Data.Product hiding (Σ ; map)
open import Data.Unit
open import Data.Empty
open import Function
open import Data.Nat renaming (_≟_ to _≟N_) 
open import Data.Vec renaming (_∈_ to _∈ⱽ_) hiding (init)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)

open import Subset.DecidableSubset renaming (Ø to ø ; _⋃_ to _⋃ᵈ_)
open import Language Σ hiding (⟦_⟧)
open import RegularExpression Σ
open import Automata Σ
open import State

open ≡-Reasoning


-- translate a Regular expression to a NFA with ε-step
regexToε-NFA : RegExp → ε-NFA
regexToε-NFA Ø =
  record { Q = Ø-State ; Q? = DecEq-Ø ; δ = λ _ _ _ → false ; q₀ = init ; F = ø ; It = Ø-Vec ; ∣Q∣ = _ ; ∀q∈It = ∀q∈It' }
    where
      ∀q∈It' : ∀ q → q ∈ⱽ Ø-Vec
      ∀q∈It' init = here
regexToε-NFA ε =
  record { Q = Q' ; Q? = DecEq-ε ; δ = δ' ; q₀ = init ; F = F' ; It = ε-Vec ; ∣Q∣ = _ ; ∀q∈It = ∀q∈It' }
    where
      Q' : Set
      Q' = ε-State
      δ' : Q' → Σᵉ → DecSubset Q'
      δ' init E     init = true
      δ' init (α a) init = false
      F' : DecSubset Q'
      F' init  = true
      ∀q∈It' : ∀ q → (q ∈ⱽ ε-Vec)
      ∀q∈It' init = here
regexToε-NFA (σ a) =
  record { Q = Q' ; Q? = DecEq-σ ; δ = δ' ; q₀ = init ; F = F' ; It = σ-List ; ∣Q∣ = _ ; ∀q∈It = ∀q∈It' }
    where
      Q' : Set
      Q' = σ-State
      δ' : Q' → Σᵉ → DecSubset Q'
      δ' init   E     init   = true
      δ' init   (α b) accept = decEqToBool dec a b
      δ' accept E     accept = true
      δ' _      _     _      = false
      F' : DecSubset Q'
      F' init   = false
      F' accept = true
      ∀q∈It' : ∀ q → (q ∈ⱽ σ-List)
      ∀q∈It' init   = here
      ∀q∈It' accept = there here
regexToε-NFA (e₁ ∣ e₂) =
  record { Q = Q' ; Q? = DecEq-⊍ Q₁? Q₂? ; δ = δ' ; q₀ = init ; F = F' ; It = ⊍-Vec It₁ It₂ ; ∣Q∣ = _ ; ∀q∈It = ∀q∈It' }
    where
      open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; It to It₁ ; ∀q∈It to ∀q∈It₁)
      open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; It to It₂ ; ∀q∈It to ∀q∈It₂)
      Q' : Set
      Q' = Q₁ ⊍ Q₂
      δ' : Q' → Σᵉ → DecSubset Q'
      δ' init      E init       = true
      δ' init      E (⊍inj₁ q)  = decEqToBool Q₁? q q₀₁
      δ' init      E (⊍inj₂ q)  = decEqToBool Q₂? q q₀₂
      δ' (⊍inj₁ q) a (⊍inj₁ q') = q' ∈? δ₁ q a
      δ' (⊍inj₂ q) a (⊍inj₂ q') = q' ∈? δ₂ q a
      δ' _         _ _          = false
      F' : DecSubset Q'
      F' init      = false
      F' (⊍inj₁ q) = q ∈? F₁
      F' (⊍inj₂ q) = q ∈? F₂
      ∀q∈It' : ∀ q → q ∈ⱽ ⊍-Vec It₁ It₂
      ∀q∈It' init      = here
      ∀q∈It' (⊍inj₁ q) = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⊍ Q₁? Q₂?) (⊍inj₁ q) (map ⊍inj₁ It₁) (map ⊍inj₂ It₂) in
                         let prf₂ = Subset.VectorRep.∈-lem₂ Q₁? (DecEq-⊍ Q₁? Q₂?) ⊍inj₁ q It₁ (∀q∈It₁ q) in there (prf₁ (inj₁ prf₂))
      ∀q∈It' (⊍inj₂ q) = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⊍ Q₁? Q₂?) (⊍inj₂ q) (map ⊍inj₁ It₁) (map ⊍inj₂ It₂) in
                         let prf₂ = Subset.VectorRep.∈-lem₂ Q₂? (DecEq-⊍ Q₁? Q₂?) ⊍inj₂ q It₂ (∀q∈It₂ q) in there (prf₁ (inj₂ prf₂))
      
regexToε-NFA (e₁ ∙ e₂) =
  record { Q = Q' ; Q? = DecEq-⍟ Q₁? Q₂? ; δ = δ' ; q₀ = ⍟inj₁ q₀₁ ; F = F' ; It = ⍟-Vec It₁ It₂ ; ∣Q∣ = _ ; ∀q∈It = ∀q∈It' }
    where
      open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; It to It₁ ; ∀q∈It to ∀q∈It₁)
      open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; It to It₂ ; ∀q∈It to ∀q∈It₂)
      Q' : Set
      Q' = Q₁ ⍟ Q₂
      δ' : Q' → Σᵉ → DecSubset Q'
      δ' (⍟inj₁ q) a (⍟inj₁ q') = q' ∈? δ₁ q a
      δ' (⍟inj₁ q) E mid        = q  ∈? F₁
      δ' (⍟inj₂ q) a (⍟inj₂ q') = q' ∈? δ₂ q a
      δ' mid       E mid        = true
      δ' mid       E (⍟inj₂ q)  = decEqToBool Q₂? q q₀₂
      δ' _         _ _ = false  
      F' : DecSubset Q'
      F' (⍟inj₁ q) = false
      F' mid       = false
      F' (⍟inj₂ q) = q ∈? F₂
      ∀q∈It' : ∀ q → q ∈ⱽ ⍟-Vec It₁ It₂
      ∀q∈It' mid       = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⍟ Q₁? Q₂?) mid (map ⍟inj₁ It₁) (mid ∷ map ⍟inj₂ It₂) in
                         prf₁ (inj₂ here)
      ∀q∈It' (⍟inj₁ q) = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⍟ Q₁? Q₂?) (⍟inj₁ q) (map ⍟inj₁ It₁) (mid ∷ map ⍟inj₂ It₂) in
                         let prf₂ = Subset.VectorRep.∈-lem₂ Q₁? (DecEq-⍟ Q₁? Q₂?) ⍟inj₁ q It₁ (∀q∈It₁ q) in prf₁ (inj₁ prf₂)
      ∀q∈It' (⍟inj₂ q) = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⍟ Q₁? Q₂?) (⍟inj₂ q) (map ⍟inj₁ It₁) (mid ∷ map ⍟inj₂ It₂) in
                         let prf₂ = Subset.VectorRep.∈-lem₂ Q₂? (DecEq-⍟ Q₁? Q₂?) ⍟inj₂ q It₂ (∀q∈It₂ q) in prf₁ (inj₂ (there prf₂))
      
regexToε-NFA (e *) =
  record { Q = Q' ; Q? = DecEq-* Q₁? ; δ = δ' ; q₀ = init ; F = F' ; It = *-Vec It₁ ; ∣Q∣ = _ ; ∀q∈It = ∀q∈It' }
    where
      open ε-NFA (regexToε-NFA e) renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; It to It₁ ; ∀q∈It to ∀q∈It₁)
      Q' : Set
      Q' = Q₁ *-State
      δ' : Q' → Σᵉ → DecSubset Q'
      δ' init    E     init     = true
      δ' init    E     (inj q)  = decEqToBool Q₁? q q₀₁
      δ' (inj q) E     (inj q') = q' ∈? δ₁ q E ∨ (q ∈? F₁ ∧ decEqToBool Q₁? q' q₀₁)
      δ' (inj q) (α a) (inj q') = q' ∈? δ₁ q (α a)
      δ' _       _     _        = false
      F' : DecSubset Q'
      F' init    = true
      F' (inj q) = q ∈? F₁
      ∀q∈It' : ∀ q → q ∈ⱽ *-Vec It₁
      ∀q∈It' init    = here
      ∀q∈It' (inj q) = there (Subset.VectorRep.∈-lem₂ Q₁? (DecEq-* Q₁?) inj q It₁ (∀q∈It₁ q))
   

-- remove ε-steps
remove-ε-step : ε-NFA → NFA
remove-ε-step nfa =
  record { Q = Q ; Q? = Q? ; δ = δ' ; q₀ = q₀ ; F = F' ; It = It }
    where
      open ε-NFA nfa
      open ε-NFA-Operations nfa

      δ' : Q → Σ → DecSubset Q
      --     = { q' | q' ∈ δ q (α a) ∨ ∃p∈Q. q' ∈ δ p (α a) ∧ p ∈ ε-closure(q) }
      --     = λ q' → q' ∈ δ q (α a) ⊎ Σ[ p ∈ Q ] (q' ∈ δ p (α a) × p ∈ ε-closure q)
      --     = λ q' → q' ∈ δ q (α a) ∨ any (λ p → q' ∈ δ p (α a) ∧ p ∈ ε-closure q) It
      δ' q a = λ q' → q' ∈? δ q (α a) ∨ ∃q⊢a-q'? (Dec-→ε*⊢ q a q')

      F' : DecSubset Q
      -- = { q | q ∈ F ∨ ∃p∈Q. p ∈ F ∧ p ∈ ε-closure(q) }
      -- = λ q → q ∈ F ⊎ Σ[ p ∈ Q ] (p ∈ F × p ∈ ε-closure q)
      -- = λ q → q ∈ F ∨ any (λ p → p ∈ F ∧ p ∈ ε-closure q) It
      F' = λ q → q ∈? F ∨ ∃q∈F? (Dec-→ε*∈F q)



-- determinise the NFA by powerset construction
powerset-construction : NFA → DFA
powerset-construction nfa =
  record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' }
    where
      open NFA nfa
      Q' : Set
      Q' = DecSubset Q
      
      δ' : Q' → Σ → Q'
      --      = λ q → Σ[ p ∈ Q ] (p ∈ qs × q ∈ δ p a)
      δ' qs a = λ q → undefined --Data.List.any (λ p → p ∈ qs ∧ q ∈ δ p a) It
      
      q₀' : Q'
      q₀' = ⟦ q₀ ⟧ {{Q?}}
      
      F' : DecSubset Q'
      -- = λ qs → Σ[ p ∈ Q ] (p ∈ qs × p ∈ F)
      F' = λ qs → undefined --any (λ p → p ∈ qs ∧ p ∈ F) It 



-- translating a regular expression to a NFA w/o ε-step
regexToNFA : RegExp → NFA
regexToNFA = remove-ε-step ∘ regexToε-NFA


-- translating a regular expression to a DFA
regexToDFA : RegExp → DFA
regexToDFA = powerset-construction ∘ remove-ε-step ∘ regexToε-NFA
