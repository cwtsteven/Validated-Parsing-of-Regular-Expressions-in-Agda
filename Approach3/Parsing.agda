module Approach3.Parsing (Σ : Set) where

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
open import Approach3.Subset renaming (Ø to ø)
open import Approach3.Language Σ
open import Approach3.RegularExpression Σ
open import Approach3.Automata Σ

data _⊍_ (A B : Set) : Set where
  init : A ⊍ B
  ⊍inj₁ : (a : A) → A ⊍ B
  ⊍inj₂ : (b : B) → A ⊍ B

data _⍟_ (A B : Set) : Set where
 ⍟inj₁ : (a : A) → A ⍟ B
 mid   : A ⍟ B
 ⍟inj₂ : (b : B) → A ⍟ B

data _*-State (A : Set) : Set where
 init : A *-State
 inj  : (a : A) → A *-State

data σ-State : Set where
 init   : σ-State
 accept : σ-State
 error  : σ-State

data ε-State : Set where
 init  : ε-State
 error : ε-State

data Ø-State : Set where
 init : Ø-State


parseToε-NFA : RegExp → ε-NFA
parseToε-NFA Ø = record { Q = Ø-State ; δ = λ _ _ _ → ⊥ ; q₀ = init ; F = ø ; F? = λ _ → no (λ ()) }
parseToε-NFA ε = record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' } 
 where
  Q' : Set
  Q' = ε-State
  δ' : Q' → Σᵉ → Powerset Q' zero
  δ' init  E     init  = ⊤
  δ' init  (α a) error = ⊤
  δ' error _     error = ⊤
  δ' _     _     _     = ⊥
  F' : Powerset Q' zero
  F' init  = ⊤
  F' error = ⊥
  F?' : Decidable F'
  F?' init  = yes tt
  F?' error = no (λ ())
parseToε-NFA (σ a) = record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' }
 where
  Q' : Set
  Q' = σ-State
  δ' : Q' → Σᵉ → Powerset Q' zero
  δ' init   E       init   = ⊤
  δ' init   (α  b)  accept = a ≡ b
  δ' init   (α  b)  error  = a ≢ b
  δ' accept E       accept = ⊤
  δ' accept (α a)   error  = ⊤
  δ' error  _       error  = ⊤
  δ' _      _       _      = ⊥
  F' : Powerset Q' zero
  F' init   = ⊥
  F' accept = ⊤
  F' error  = ⊥
  F?' : Decidable F'
  F?' init   = no (λ ())
  F?' accept = yes tt
  F?' error  = no (λ ())
parseToε-NFA (e₁ ∣ e₂) = record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' }
 where
  open ε-NFA (parseToε-NFA e₁) renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; F? to F₁?)
  open ε-NFA (parseToε-NFA e₂) renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; F? to F₂?)
  Q' : Set
  Q' = Q₁ ⊍ Q₂
  δ' : Q' → Σᵉ → Powerset Q' zero
  δ' init      Ε (⊍inj₁ q)  = q ≡ q₀₁
  δ' init      Ε (⊍inj₂ q)  = q ≡ q₀₂
  δ' (⊍inj₁ q) a (⊍inj₁ q') = δ₁ q a q'
  δ' (⊍inj₂ q) a (⊍inj₂ q') = δ₂ q a q'
  δ' _         _ _          = ⊥
  F' : Powerset Q' zero
  F' init      = ⊥
  F' (⊍inj₁ q) = F₁ q
  F' (⊍inj₂ q) = F₂ q
  F?' : Decidable F'
  F?' init = no (λ ())
  F?' (⊍inj₁ q) = F₁? q
  F?' (⊍inj₂ q) = F₂? q
parseToε-NFA (e₁ ∙ e₂) = record { Q = Q' ; δ = δ' ; q₀ = ⍟inj₁ q₀₁ ; F = F' ; F? = F?' }
  where
   open ε-NFA (parseToε-NFA e₁) renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; F? to F₁?)
   open ε-NFA (parseToε-NFA e₂) renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; F? to F₂?)
   Q' : Set
   Q' = Q₁ ⍟ Q₂
   δ' : Q' → Σᵉ → Powerset Q' zero
   δ' (⍟inj₁ q) a (⍟inj₁ q') = δ₁ q a q'
   δ' (⍟inj₁ q) Ε mid        = F₁ q
   δ' (⍟inj₂ q) a (⍟inj₂ q') = δ₂ q a q'
   δ' mid       Ε (⍟inj₂ q)  = q ≡ q₀₂
   δ' _         _ _ = ⊥  
   F' : Powerset Q' zero
   F' (⍟inj₁ q) = ⊥
   F' mid       = ⊥
   F' (⍟inj₂ q) = F₂ q
   F?' : Decidable F'
   F?' (⍟inj₁ q) = no (λ ())
   F?' mid       = no (λ ())
   F?' (⍟inj₂ q) = F₂? q
parseToε-NFA (e *)     = record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' ; F? = F?' }
 where
  open ε-NFA (parseToε-NFA e)
  Q' : Set
  Q' = Q *-State
  δ' : Q' → Σᵉ → Powerset Q' zero
  δ' init    E     (inj q)  = q ≡ q₀
  δ' (inj q) E     (inj q') = q ≡ q₀
  δ' (inj q) (α a) (inj q') = δ q (α a) q'
  δ' _       _     _        = ⊥
  F' : Powerset Q' zero
  F' init = ⊤
  F' (inj q) = F q
  F?' : Decidable F'
  F?' init    = yes tt
  F?' (inj q) = F? q

remove-ε-setp : ε-NFA → NFA
remove-ε-setp nfa = record { Q = Q ; δ = δ' ; q₀ = q₀ ; F = F ; F? = F? }
 where
  open ε-NFA nfa
  δ' : Q → Σ → Powerset Q zero
  δ' = undefined

powerset-construction : NFA → DFA
powerset-construction nfa = record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' ; F? = F?' }
 where
  open NFA nfa
  --open import Subset.DecidableSubset renaming (⟦_⟧ to ⟦_⟧₁)
  Q' : Set₁
  Q' = Powerset Q zero
  δ' : Q' → Σ → Q'
  δ' = undefined
  q₀' : Q'
  q₀' = undefined
  F' : Powerset Q' (suc zero)
  F' = undefined
  F?' : Decidable F'
  F?' = undefined


parseToDFA : RegExp → DFA
parseToDFA = powerset-construction ∘ remove-ε-setp ∘ parseToε-NFA
