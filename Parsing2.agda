open import Util
module Parsing2 (Σ : Set)(dec : DecEq Σ) where

open import Data.List
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (Σ)
open import Function


open import Subset.DecidableSubset renaming (Ø to ø)
open import Language Σ
open import RegularExpression Σ
open import Automata2 Σ

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


parseToNFA : RegExp → NFA
parseToNFA Ø = record { Q = Ø-State ; δ = λ _ _ _ → false ; q₀ = init ; F = ø }
parseToNFA ε = record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' } 
 where
  Q' : Set
  Q' = ε-State
  δ' : Q' → Σᵉ → DecSubset Q'
  δ' init  E     init  = true
  δ' init  (α a) error = true
  δ' error _     error = true
  δ' _     _     _     = false
  F' : DecSubset Q'
  F' init  = true
  F' error = false
parseToNFA (σ a) = record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' }
 where
  Q' : Set
  Q' = σ-State
  δ' : Q' → Σᵉ → DecSubset Q'
  δ' init   E       init   = true
  δ' init   (α  b)  accept = a ≡ b
  δ' init   (α  b)  error  = not (decEqToBool dec a b)
  δ' accept E       accept = true
  δ' accept (α a)   error  = true
  δ' error  _       error  = true
  δ' _      _       _      = false
  F' : DecSubset Q'
  F' init   = false
  F' accept = true
  F' error  = false
parseToNFA (e₁ ∣ e₂) = record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' }
 where
  open NFA (parseToNFA e₁) renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
  open NFA (parseToNFA e₂) renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
  Q' : Set
  Q' = Q₁ ⊍ Q₂
  δ' : Q' → Σᵉ → DecSubset Q'
  δ' init      Ε (⊍inj₁ q)  = true --q ≡ q₀₁
  δ' init      Ε (⊍inj₂ q)  = true --q ≡ q₀₂
  δ' (⊍inj₁ q) a (⊍inj₁ q') = δ₁ q a q'
  δ' (⊍inj₂ q) a (⊍inj₂ q') = δ₂ q a q'
  δ' _         _ _          = false
  F' : DecSubset Q'
  F' init      = false
  F' (⊍inj₁ q) = F₁ q
  F' (⊍inj₂ q) = F₂ q
parseToNFA (e₁ ∙ e₂) = record { Q = Q' ; δ = δ' ; q₀ = ⍟inj₁ q₀₁ ; F = F' }
  where
   open NFA (parseToNFA e₁) renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
   open NFA (parseToNFA e₂) renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
   Q' : Set
   Q' = Q₁ ⍟ Q₂
   δ' : Q' → Σᵉ → DecSubset Q'
   δ' (⍟inj₁ q) a (⍟inj₁ q') = δ₁ q a q'
   δ' (⍟inj₁ q) Ε mid        = F₁ q
   δ' (⍟inj₂ q) a (⍟inj₂ q') = δ₂ q a q'
   δ' mid       Ε (⍟inj₂ q)  = true --q ≡ q₀₂
   δ' _         _ _ = false  
   F' : DecSubset Q'
   F' (⍟inj₁ q) = false
   F' mid       = false
   F' (⍟inj₂ q) = F₂ q
parseToNFA (e *)     = record { Q = Q' ; δ = δ' ; q₀ = init ; F = F' }
 where
  open NFA (parseToNFA e)
  Q' : Set
  Q' = Q *-State
  δ' : Q' → Σᵉ → DecSubset Q'
  δ' init    E     (inj q)  = true --q ≡ q₀
  δ' (inj q) E     (inj q') = true --q ≡ q₀
  δ' (inj q) (α a) (inj q') = δ q (α a) q'
  δ' _       _     _        = false
  F' : DecSubset Q'
  F' init = true
  F' (inj q) = F q


determinise : NFA → DFA
determinise nfa = record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' }
 where
  open NFA nfa
  Q' : Set
  Q' = DecSubset Q
  δ' : Q' → Σ → Q'
  δ' = undefined
  q₀' : Q'
  q₀' = undefined
  F' : DecSubset Q'
  F' = undefined


parseToDFA : RegExp → DFA
parseToDFA = determinise ∘ parseToNFA
