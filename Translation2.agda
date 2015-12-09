{-
  Here the translation of a regular expression to a DFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung 2015.
  Version 9-12-2015
-}
open import Util
module Translation2 (Σ : Set)(dec : DecEq Σ) where

open import Level
open import Data.Bool
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Function


open import Subset renaming (Ø to ø)
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; Ø to øᵈ)
open import Language Σ hiding (⟦_⟧)
open import RegularExpression Σ
open import Automata2 Σ
open import State


-- translate a Regular expression to a NFA with ε-step
regexToε-NFA : RegExp → ε-NFA
regexToε-NFA Ø =
 record { Q = Ø-State ; Q? = DecEq-Ø ; δ = λ _ _ _ → false ; q₀ = init ; F = øᵈ}
regexToε-NFA ε =
 record { Q = Q' ; Q? = DecEq-ε ; δ = δ' ; q₀ = init ; F = F' } 
  where
   Q' : Set
   Q' = ε-State
   δ' : Q' → Σᵉ → DecSubset Q'
   δ' init  E     init  = true
   δ' init  (α a) error = false
   δ' error _     error = true
   δ' _     _     _     = false
   F' : DecSubset Q'
   F' init  = true
   F' error = false
regexToε-NFA (σ a) =
 record { Q = Q' ; Q? = DecEq-σ ; δ = δ' ; q₀ = init ; F = F' }
  where
   Q' : Set
   Q' = σ-State
   δ' : Q' → Σᵉ → DecSubset Q'
   δ' init   E       init   = true
   δ' init   (α  b)  accept = decEqToBool (DecEq-Σᵉ dec) (α a) (α b)
   δ' init   (α  b)  error  = not (decEqToBool (DecEq-Σᵉ dec) (α a) (α b))
   δ' accept E       accept = true
   δ' accept (α a)   error  = true
   δ' error  _       error  = true
   δ' _      _       _      = false
   F' : DecSubset Q'
   F' init   = false
   F' accept = true
   F' error  = false
regexToε-NFA (e₁ ∣ e₂) =
 record { Q = Q' ; Q? = DecEq-⊍ Q₁? Q₂? ; δ = δ' ; q₀ = init ; F = F' }
  where
   open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
   open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
   Q' : Set
   Q' = Q₁ ⊍ Q₂
   δ' : Q' → Σᵉ → DecSubset Q'
   δ' init      Ε (⊍inj₁ q)  = decEqToBool Q₁? q q₀₁
   δ' init      Ε (⊍inj₂ q)  = decEqToBool Q₂? q q₀₂
   δ' (⊍inj₁ q) a (⊍inj₁ q') = q' ∈ᵈ δ₁ q a
   δ' (⊍inj₂ q) a (⊍inj₂ q') = q' ∈ᵈ δ₂ q a
   δ' _         _ _          = false
   F' : DecSubset Q'
   F' init      = false
   F' (⊍inj₁ q) = q ∈ᵈ F₁
   F' (⊍inj₂ q) = q ∈ᵈ F₂
regexToε-NFA (e₁ ∙ e₂) =
 record { Q = Q' ; Q? = DecEq-⍟ Q₁? Q₂? ; δ = δ' ; q₀ = ⍟inj₁ q₀₁ ; F = F' }
  where
   open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
   open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
   Q' : Set
   Q' = Q₁ ⍟ Q₂
   δ' : Q' → Σᵉ → DecSubset Q'
   δ' (⍟inj₁ q) a (⍟inj₁ q') = q' ∈ᵈ δ₁ q a
   δ' (⍟inj₁ q) Ε mid        = q  ∈ᵈ F₁
   δ' (⍟inj₂ q) a (⍟inj₂ q') = q' ∈ᵈ δ₂ q a
   δ' mid       Ε (⍟inj₂ q)  = decEqToBool Q₂? q q₀₂
   δ' _         _ _ = false  
   F' : DecSubset Q'
   F' (⍟inj₁ q) = false
   F' mid       = false
   F' (⍟inj₂ q) = q ∈ᵈ F₂
regexToε-NFA (e *) =
 record { Q = Q' ; Q? = DecEq-* Q? ; δ = δ' ; q₀ = init ; F = F' }
  where
   open ε-NFA (regexToε-NFA e)
   Q' : Set
   Q' = Q *-State
   δ' : Q' → Σᵉ → DecSubset Q'
   δ' init    E     (inj q)  = decEqToBool Q? q q₀
   δ' (inj q) E     (inj q') = (q ∈ᵈ F ∧ decEqToBool Q? q' q₀) ∨ (q' ∈ᵈ δ q E)
   δ' (inj q) (α a) (inj q') = q' ∈ᵈ δ q (α a)
   δ' _       _     _        = false
   F' : DecSubset Q'
   F' init    = true
   F' (inj q) = q ∈ᵈ F


-- remove ε-steps
remove-ε-step : ε-NFA → NFA
remove-ε-step nfa =
 record { Q = Q ; Q? = Q? ; δ = δ' ; q₀ = q₀ ; F = F }
  where
   open ε-NFA nfa
   open ε-NFA-Operations nfa
   δ' : Q → Σ → DecSubset Q
   δ' q a = λ q' → q' ∈ᵈ δ q (α a) ∨ undefined --(Σ[ p ∈ Q ] (q →*ε p × q' ∈ δ p (α a)))



-- determinise the NFA by powerset construction
powerset-construction : NFA → DFA
powerset-construction nfa =
 record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' }
  where
   open NFA nfa
   Q' : Set
   Q' = DecSubset Q
   δ' : Q' → Σ → Q'
   δ' qs a q = undefined --Σ[ p ∈ Q ] (p ∈ qs × q ∈ δ p a)
   q₀' : Q'
   q₀' = singleton {Q} {Q?} q₀
   F' : DecSubset Q'
   F' = undefined


-- translating a regular expression to a NFA w/o ε-step
regexToNFA : RegExp → NFA
regexToNFA = remove-ε-step ∘ regexToε-NFA


-- translating a regular expression to a DFA
regexToDFA : RegExp → DFA
regexToDFA = powerset-construction ∘ remove-ε-step ∘ regexToε-NFA
