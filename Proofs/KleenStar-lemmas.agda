open import RegularExpression
open import Data.Nat
module Proofs.KleenStar-lemmas (Σ : Set)(e : RegularExpression.RegExp Σ)(n : ℕ) where

open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Util
open import Subset
open import Language Σ
open import Automata Σ
open import Parsing Σ

nfa : ε-NFA
nfa = regexToε-NFA (e *)

nfa₁ : ε-NFA
nfa₁ = regexToε-NFA e

nfa₂ : ε-NFA
nfa₂ = undefined

open ε-NFA nfa
open ε-NFA nfa₁ renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
open ε-NFA nfa₂ renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
open ε-NFA-Operations nfa
open ε-NFA-Operations nfa₁ renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₁)
open ε-NFA-Operations nfa₂ renaming (_⊢_ to _⊢ₑ₂_ ; _⊢*_ to _⊢*ₑ₂_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₂_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₂)

lem₁ : ∀ n w u v
       → w ≡ u ++ v
       → u ∈ Lᵉᴺ nfa₁
       → v ∈ (Lᴿ Σ e ^ n)
       → w ∈ Lᵉᴺ nfa
lem₁ zero    w u v w≡uv u∈Lᴿe v∈Lᴿeⁿ = undefined
lem₁ (suc n) w u v w≡uv u∈Lᴿe v∈Lᴿeⁿ = undefined
