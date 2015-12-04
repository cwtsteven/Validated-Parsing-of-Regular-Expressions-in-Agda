{-
  Here the translation of a regular expression to a DFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung 2015.
  Version 4-12-2015
-}

module Translation (Σ : Set) where

open import Level
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Function

open import Util
open import Subset renaming (Ø to ø)
open import Language Σ hiding (⟦_⟧)
open import RegularExpression Σ
open import Automata Σ
open import State


-- translate a Regular expression to a NFA with ε-step
regexToε-NFA : RegExp → ε-NFA
regexToε-NFA Ø =
 record { Q = Ø-State ; Q? = DecEq-Ø ; δ = λ _ _ _ → ⊥ ; q₀ = init ; F = ø ; F? = λ _ → no (λ ()) }
regexToε-NFA ε =
 record { Q = Q' ; Q? = DecEq-ε ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' } 
  where
   Q' : Set
   Q' = ε-State
   δ' : Q' → Σᵉ → Subset Q'
   δ' init  E     init  = ⊤
   δ' init  (α a) error = ⊤
   δ' error _     error = ⊤
   δ' _     _     _     = ⊥
   F' : Subset Q'
   F' init  = ⊤
   F' error = ⊥
   F?' : Decidable F'
   F?' init  = yes tt
   F?' error = no (λ ())
regexToε-NFA (σ a) =
 record { Q = Q' ; Q? = DecEq-σ ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' }
  where
   Q' : Set
   Q' = σ-State
   δ' : Q' → Σᵉ → Subset Q'
   δ' init   E       init   = ⊤
   δ' init   (α  b)  accept = a ≡ b
   δ' init   (α  b)  error  = a ≢ b
   δ' accept E       accept = ⊤
   δ' accept (α a)   error  = ⊤
   δ' error  _       error  = ⊤
   δ' _      _       _      = ⊥
   F' : Subset Q'
   F' init   = ⊥
   F' accept = ⊤
   F' error  = ⊥
   F?' : Decidable F'
   F?' init   = no (λ ())
   F?' accept = yes tt
   F?' error  = no (λ ())
regexToε-NFA (e₁ ∣ e₂) =
 record { Q = Q' ; Q? = DecEq-⊍ Q₁? Q₂? ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' }
  where
   open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; F? to F₁?)
   open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; F? to F₂?)
   Q' : Set
   Q' = Q₁ ⊍ Q₂
   δ' : Q' → Σᵉ → Subset Q'
   δ' init      Ε (⊍inj₁ q)  = q ≡ q₀₁
   δ' init      Ε (⊍inj₂ q)  = q ≡ q₀₂
   δ' (⊍inj₁ q) a (⊍inj₁ q') = δ₁ q a q'
   δ' (⊍inj₂ q) a (⊍inj₂ q') = δ₂ q a q'
   δ' _         _ _          = ⊥
   F' : Subset Q'
   F' init      = ⊥
   F' (⊍inj₁ q) = F₁ q
   F' (⊍inj₂ q) = F₂ q
   F?' : Decidable F'
   F?' init = no (λ ())
   F?' (⊍inj₁ q) = F₁? q
   F?' (⊍inj₂ q) = F₂? q
regexToε-NFA (e₁ ∙ e₂) =
 record { Q = Q' ; Q? = DecEq-⍟ Q₁? Q₂? ; δ = δ' ; q₀ = ⍟inj₁ q₀₁ ; F = F' ; F? = F?' }
  where
   open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; F? to F₁?)
   open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; F? to F₂?)
   Q' : Set
   Q' = Q₁ ⍟ Q₂
   δ' : Q' → Σᵉ → Subset Q'
   δ' (⍟inj₁ q) a (⍟inj₁ q') = δ₁ q a q'
   δ' (⍟inj₁ q) Ε mid        = F₁ q
   δ' (⍟inj₂ q) a (⍟inj₂ q') = δ₂ q a q'
   δ' mid       Ε (⍟inj₂ q)  = q ≡ q₀₂
   δ' _         _ _ = ⊥  
   F' : Subset Q'
   F' (⍟inj₁ q) = ⊥
   F' mid       = ⊥
   F' (⍟inj₂ q) = F₂ q
   F?' : Decidable F'
   F?' (⍟inj₁ q) = no (λ ())
   F?' mid       = no (λ ())
   F?' (⍟inj₂ q) = F₂? q
regexToε-NFA (e *) =
 record { Q = Q' ; Q? = DecEq-* Q? ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' }
  where
   open ε-NFA (regexToε-NFA e)
   Q' : Set
   Q' = Q *-State
   δ' : Q' → Σᵉ → Subset Q'
   δ' init    E     (inj q)  = q ≡ q₀
   δ' (inj q) E     (inj q') = (q ∈ F × q' ≡ q₀) ⊎ (δ q E q')
   δ' (inj q) (α a) (inj q') = δ q (α a) q'
   δ' _       _     _        = ⊥
   F' : Subset Q'
   F' init = ⊤
   F' (inj q) = F q
   F?' : Decidable F'
   F?' init    = yes tt
   F?' (inj q) = F? q


-- remove ε-steps
remove-ε-step : ε-NFA → NFA
remove-ε-step nfa =
 record { Q = Q ; Q? = Q? ; δ = δ' ; q₀ = q₀ ; F = F ; F? = F? }
  where
   open ε-NFA nfa
   open ε-NFA-Operations nfa
   δ' : Q → Σ → Subset Q
   δ' q a = λ q' → q' ∈ δ q (α a) ⊎ Σ[ p ∈ Q ] (q →*ε p × q' ∈ δ p (α a))



-- determinise the NFA by powerset construction
powerset-construction : NFA → DFA
powerset-construction nfa =
 record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' ; F? = F?' }
  where
   open NFA nfa
   Q' : Set₁
   Q' = Subset Q
   δ' : Q' → Σ → Q'
   δ' qs a = λ p → Σ[ q ∈ Q ] (q ∈ qs × p ∈ δ q a)
   q₀' : Q'
   q₀' = ⟦ q₀ ⟧
   F' : Subset Q'
   F' = λ qs → Σ[ q ∈ Q ] (q ∈ qs × q ∈ F)

   Q?' : (qs : Subset Q {zero}) → Decidable qs
   Q?' = undefined
   It : List Q
   It = undefined
   F?' : Decidable F'
   F?' qs = find (toList qs (Q?' qs) It)
    where
     find : (l : List Q) → Dec (Σ[ q ∈ Q ] (q ∈ qs × q ∈ F))
     find []      = no ¬F'
      where
       ¬F' : ¬ (Σ[ q ∈ Q ] (q ∈ qs × q ∈ F))
       ¬F' (q , q∈qs , q∈F) = undefined
     find (q ∷ l) with Q?' qs q | F? q
     find (q ∷ l) | yes q∈qs | yes q∈F = yes (q , q∈qs , q∈F)
     find (q ∷ l) | _        | _       = find l


-- translating a regular expression to a NFA w/o ε-step
regexToNFA : RegExp → NFA
regexToNFA = remove-ε-step ∘ regexToε-NFA


-- translating a regular expression to a DFA
regexToDFA : RegExp → DFA
regexToDFA = powerset-construction ∘ remove-ε-step ∘ regexToε-NFA
