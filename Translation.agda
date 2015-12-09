{-
  Here the translation of a regular expression to a DFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung 2015.
  Version 9-12-2015
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
 record { Q = Ø-State ; δ = λ _ _ _ → ⊥ ; q₀ = init ; F = ø ; Dec-F = λ _ → no (λ ()) }
regexToε-NFA ε =
 record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; Dec-F = Dec-F' } 
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
   Dec-F' : Decidable F'
   Dec-F' init  = yes tt
   Dec-F' error = no (λ ())
regexToε-NFA (σ a) =
 record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; Dec-F = Dec-F' }
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
   Dec-F' : Decidable F'
   Dec-F' init   = no (λ ())
   Dec-F' accept = yes tt
   Dec-F' error  = no (λ ())
regexToε-NFA (e₁ ∣ e₂) =
 record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; Dec-F = Dec-F' }
  where
   open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; Dec-F to Dec-F₁)
   open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; Dec-F to Dec-F₂)
   Q' : Set
   Q' = Q₁ ⊍ Q₂
   δ' : Q' → Σᵉ → Subset Q'
   δ' init      Ε (⊍inj₁ q)  = q ≡ q₀₁
   δ' init      Ε (⊍inj₂ q)  = q ≡ q₀₂
   δ' (⊍inj₁ q) a (⊍inj₁ q') = q' ∈ δ₁ q a
   δ' (⊍inj₂ q) a (⊍inj₂ q') = q' ∈ δ₂ q a
   δ' _         _ _          = ⊥
   F' : Subset Q'
   F' init      = ⊥
   F' (⊍inj₁ q) = q ∈ F₁
   F' (⊍inj₂ q) = q ∈ F₂
   Dec-F' : Decidable F'
   Dec-F' init      = no (λ ())
   Dec-F' (⊍inj₁ q) = Dec-F₁ q
   Dec-F' (⊍inj₂ q) = Dec-F₂ q
regexToε-NFA (e₁ ∙ e₂) =
 record { Q = Q' ; δ = δ' ; q₀ = ⍟inj₁ q₀₁ ; F = F' ; Dec-F = Dec-F' }
  where
   open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; Dec-F to Dec-F₁)
   open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; Dec-F to Dec-F₂)
   Q' : Set
   Q' = Q₁ ⍟ Q₂
   δ' : Q' → Σᵉ → Subset Q'
   δ' (⍟inj₁ q) a (⍟inj₁ q') = q' ∈ δ₁ q a
   δ' (⍟inj₁ q) Ε mid        = q  ∈ F₁
   δ' (⍟inj₂ q) a (⍟inj₂ q') = q' ∈ δ₂ q a
   δ' mid       Ε (⍟inj₂ q)  = q  ≡ q₀₂
   δ' _         _ _          = ⊥  
   F' : Subset Q'
   F' (⍟inj₁ q) = ⊥
   F' mid       = ⊥
   F' (⍟inj₂ q) = q ∈ F₂
   Dec-F' : Decidable F'
   Dec-F' (⍟inj₁ q) = no (λ ())
   Dec-F' mid       = no (λ ())
   Dec-F' (⍟inj₂ q) = Dec-F₂ q
regexToε-NFA (e *) =
 record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; Dec-F = Dec-F' }
  where
   open ε-NFA (regexToε-NFA e)
   Q' : Set
   Q' = Q *-State
   δ' : Q' → Σᵉ → Subset Q'
   δ' init    E     (inj q)  = q ≡ q₀
   δ' (inj q) E     (inj q') = (q ∈ F × q' ≡ q₀) ⊎ (q' ∈ δ q E)
   δ' (inj q) (α a) (inj q') = q' ∈ δ q (α a)
   δ' _       _     _        = ⊥
   F' : Subset Q'
   F' init    = ⊤
   F' (inj q) = q ∈ F
   Dec-F' : Decidable F'
   Dec-F' init    = yes tt
   Dec-F' (inj q) = Dec-F q


-- remove ε-steps
remove-ε-step : ε-NFA → NFA
remove-ε-step nfa =
 record { Q = Q ; δ = δ' ; q₀ = q₀ ; F = F ; Dec-F = Dec-F }
  where
   open ε-NFA nfa
   open ε-NFA-Operations nfa
   δ' : Q → Σ → Subset Q
   δ' q a = λ q' → q' ∈ δ q (α a) ⊎ Σ[ p ∈ Q ] (q →*ε p × q' ∈ δ p (α a))


-- determinise the NFA by powerset construction
powerset-construction : NFA → DFA
powerset-construction nfa =
 record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' ; Dec-F = Dec-F' }
  where
   open NFA nfa
   Q' : Set₁
   Q' = Subset Q
   δ' : Q' → Σ → Q'
   δ' qs a = λ q' → Σ[ q ∈ Q ] (q ∈ qs × q' ∈ δ q a)
   q₀' : Q'
   q₀' = ⟦ q₀ ⟧
   F' : Subset Q'
   F' = λ qs → Σ[ q ∈ Q ] (q ∈ qs × q ∈ F)
   
   It : List Q
   It = undefined
   
   Dec-Q' : (qs : Q') → Decidable qs -- possible?
   Dec-Q' = undefined
   
   Dec-F' : Decidable F'
   Dec-F' qs = find It
    where
     find : List Q → Dec (Σ[ q ∈ Q ] (q ∈ qs × q ∈ F))
     find []       = no undefined -- postulate something about list and function representation?
     find (x ∷ xs) with (x ∈? qs) {{Dec-Q' qs}} | (x ∈? F) {{Dec-F}}
     ... | yes x∈qs | yes x∈F = yes (x , x∈qs , x∈F)
     ... | _        | _       = find xs


-- translating a regular expression to a NFA w/o ε-step
regexToNFA : RegExp → NFA
regexToNFA = remove-ε-step ∘ regexToε-NFA


-- translating a regular expression to a DFA
regexToDFA : RegExp → DFA
regexToDFA = powerset-construction ∘ remove-ε-step ∘ regexToε-NFA
