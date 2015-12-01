{-
  The translation of a Regular expression to a DFA follows the lecture notes 
  written by Achim Jung from The University of Birmingham, 
  School of Computer Science

  Steven Cheung 2015.
  Version 26-11-2015
-}

module Parsing (Σ : Set) where

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
open import Language Σ
open import RegularExpression Σ
open import Automata Σ


{- Here we define the set of states of different cases -}

data Ø-State : Set where
 init : Ø-State

data ε-State : Set where
 init  : ε-State
 error : ε-State

data σ-State : Set where
 init   : σ-State
 accept : σ-State
 error  : σ-State

data _⊍_ (A B : Set) : Set where
  init : A ⊍ B
  ⊍inj₁ : A → A ⊍ B
  ⊍inj₂ : B → A ⊍ B

data _⍟_ (A B : Set) : Set where
 ⍟inj₁ : A → A ⍟ B
 mid   : A ⍟ B
 ⍟inj₂ : B → A ⍟ B

data _*-State (A : Set) : Set where
 init : A *-State
 inj  : A → A *-State

-- translate a Regular expression to a NFA with ε-step
regexToε-NFA : RegExp → ε-NFA
regexToε-NFA Ø =
 record { Q = Ø-State ; δ = λ _ _ _ → ⊥ ; q₀ = init ; F = ø ; F? = λ _ → no (λ ()) }
regexToε-NFA ε =
 record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' } 
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
 record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' }
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
 record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' }
  where
   open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; F? to F₁?)
   open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; F? to F₂?)
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
 record { Q = Q' ; δ = δ' ; q₀ = ⍟inj₁ q₀₁ ; F = F' ; F? = F?' }
  where
   open ε-NFA (regexToε-NFA e₁) renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; F? to F₁?)
   open ε-NFA (regexToε-NFA e₂) renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; F? to F₂?)
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
 record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' }
  where
   open ε-NFA (regexToε-NFA e)
   Q' : Set
   Q' = Q *-State
   δ' : Q' → Σᵉ → Subset Q'
   δ' init    E     (inj q)  = q ≡ q₀
   δ' (inj q) E     (inj q') = q ≡ q₀
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
 record { Q = Q ; δ = δ' ; q₀ = q₀ ; F = F ; F? = F? }
  where
   open ε-NFA nfa
   δ' : Q → Σ → Subset Q
   δ' = undefined


-- determinise the NFA by powerset construction
powerset-construction : NFA → DFA
powerset-construction nfa =
 record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' ; F? = F?' }
  where
   open NFA nfa
   Q' : Set₁
   Q' = Subset Q
   δ' : Q' → Σ → Q'
   δ' = undefined
   q₀' : Q'
   q₀' = undefined
   F' : Subset Q'
   F' = undefined
   F?' : Decidable F'
   F?' = undefined


-- translating a regular expression to a NFA w/o ε-step
regexToNFA : RegExp → NFA
regexToNFA = remove-ε-step ∘ regexToε-NFA


-- translating a regular expression to a DFA
regexToDFA : RegExp → DFA
regexToDFA = powerset-construction ∘ remove-ε-step ∘ regexToε-NFA
