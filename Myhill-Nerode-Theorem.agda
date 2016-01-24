open import Util
module Myhill-Nerode-Theorem (Σ : Set) (dec : DecEq Σ) where

open import Level
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (Σ)

open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ dec

open ≡-Reasoning

Right-invariant : Rel Σ* _ → Set
Right-invariant rel = ∀ {w u} → rel w u → ∀ z → rel (w ++ z) (u ++ z)


module Condition1 (dfa : DFA) where
  open DFA dfa
  open DFA-Operations dfa

  infix 3 _Rm_
  _Rm_ : Rel Σ* _
  w Rm u = δ₀ w ≡ δ₀ u

  Rm-refl : Reflexive _Rm_
  Rm-refl = refl

  Rm-sym : Symmetric _Rm_
  Rm-sym {w} {u} wRmu with δ₀ w | δ₀ u
  Rm-sym {w} {u} refl | q | .q = refl

  Rm-trans : Transitive _Rm_
  Rm-trans {w} {u} {v} wRmu uRmv with δ₀ w | δ₀ u | δ₀ v
  Rm-trans {w} {u} {v} refl refl | q | .q | .q = refl


  Rm-Right-invariant : Right-invariant _Rm_
  Rm-Right-invariant {w} {u} wRmu z
    = begin
      δ₀ (w ++ z)     ≡⟨ lem₁ q₀ w z ⟩
      δ* (δ* q₀ w) z  ≡⟨ cong (λ q → δ* q z) wRmu ⟩
      δ* (δ* q₀ u) z  ≡⟨ sym (lem₁ q₀ u z) ⟩
      δ₀ (u ++ z)
      ∎

lem₃ : ∀ L
       → Regular L
       → Σ[ rm ∈ Rel Σ* _ ] ( Right-invariant rm × IsEquivalence rm ) -- ∧ finite index ∧ L is the union of its equivalence classes
lem₃ L (e , L≡Lᴿe) = _Rm_ , Rm-Right-invariant , record { refl = Rm-refl ; sym = Rm-sym ; trans = Rm-trans }
  where
    dfa : DFA
    dfa = regexToDFA e
    open Condition1 dfa


lem₂ : ∀ L
       → Σ[ rm ∈ Rel Σ* _ ] ( Right-invariant rm × IsEquivalence rm ) -- ∧ finite index ∧ L is the union of its equivalence classes
       → Regular L
lem₂ = undefined


lem₁ : ∀ L
       → Regular L
         ⇔ Σ[ rm ∈ Rel Σ* _ ] ( Right-invariant rm × IsEquivalence rm ) -- ∧ finite index ∧ L is the union of its equivalence classes
lem₁ = undefined