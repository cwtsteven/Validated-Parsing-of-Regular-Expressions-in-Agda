{-
  Here the Automata and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 2.2: Regular sets, their generators, and their recognizers
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 10-01-2016
-}

module Automata (Σ : Set) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Util
open import Subset
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_)
open import Language Σ

-- Nondeterministic finite automata with ε-step
-- section 2.2.3: Finite Automata
record ε-NFA : Set₁ where
  field
    Q  : Set
    δ  : Q → Σᵉ → DecSubset Q
    q₀ : Q
    F  : DecSubset Q
    Q? : DecEq Q
    It : List Q

-- section 2.2.3: Finite Automata
module ε-NFA-Operations (N : ε-NFA) where
  open ε-NFA N
  open ≡-Reasoning

  -- a move from (q , aw) to (q' , w)
  infix 7 _⊢_
  _⊢_ : (Q × Σᵉ × Σᵉ*) → (Q × Σᵉ*) → Set
  (q , aᵉ , wᵉ) ⊢ (q' , wᵉ') = wᵉ ≡ wᵉ' × q' ∈ᵍ δ q aᵉ

  -- k moves from (q , w) to (q' , w')
  infix 7 _⊢ᵏ_─_
  _⊢ᵏ_─_ : (Q × Σᵉ*) → ℕ → (Q × Σᵉ*) → Set
  (q , wᵉ) ⊢ᵏ zero    ─ (q' , wᵉ')
    = q ≡ q' × wᵉ ≡ wᵉ'
  (q , wᵉ) ⊢ᵏ (suc n) ─ (q' , wᵉ')
    = Σ[ p ∈ Q ] Σ[ aᵉ ∈ Σᵉ ] Σ[ uᵉ ∈ Σᵉ* ]
      ( wᵉ ≡ aᵉ ∷ uᵉ × (q , aᵉ , uᵉ) ⊢ (p , uᵉ) × (p , uᵉ) ⊢ᵏ n ─ (q' , wᵉ') )
      --( ((w ≡ a ∷ u × Σ[ b ∈ Σ ] a ≡ α b) ⊎ (w ≡ u × a ≡ E)) × (q , a , u) ⊢ (p , u) × (p , u) ⊢ᵏ n ─ (q' , w') )

  -- alternative definition of ⊢ᵏ
  infix 7 _⊢ᵏ₂_─_
  _⊢ᵏ₂_─_ : (Q × Σᵉ*) → ℕ → (Q × Σᵉ*) → Set
  (q , wᵉ) ⊢ᵏ₂ zero ─ (q' , wᵉ')
    = (q , wᵉ) ⊢ᵏ zero ─ (q' , wᵉ')
  (q , wᵉ) ⊢ᵏ₂ (suc n) ─ (q' , wᵉ')
    = Σ[ p ∈ Q ] Σ[ aᵉ ∈ Σᵉ ]
      ( (q , wᵉ) ⊢ᵏ n ─ (p , aᵉ ∷ wᵉ') × (p , aᵉ , wᵉ') ⊢ (q' , wᵉ') )
 
  -- transitive closure of ⊢
  infix 7 _⊢*_
  _⊢*_ : (Q × Σᵉ*) → (Q × Σᵉ*) → Set
  (q , wᵉ) ⊢* (q' , wᵉ') = Σ[ n ∈ ℕ ] (q , wᵉ) ⊢ᵏ n ─ (q' , wᵉ')

  -- alternative definition of ⊢*, we will later prove that ⊢*₂ is equivalent to ⊢*
  infix 7 _⊢*₂_
  _⊢*₂_ : (Q × Σᵉ*) → (Q × Σᵉ*) → Set
  (q , wᵉ) ⊢*₂ (q' , wᵉ') = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] Σ[ p ∈ Q ] Σ[ uᵉ ∈ Σᵉ* ]
                            ((q , wᵉ) ⊢ᵏ n ─ (p , uᵉ) × (p , uᵉ) ⊢ᵏ m ─ (q' , wᵉ'))
  -- ε closure
  mutual
    ε-closure₁' : Q → DecSubset Q
    ε-closure₁' q = ø --ε-closure It (⟦ q ⟧ {{Q?}})

    ε-closure₁ : List Q → DecSubset Q → DecSubset Q
    ε-closure₁ []       qs = ø
    ε-closure₁ (p ∷ ps) qs = if p ∈ᵈ qs
                             then ε-closure₁' p ⋃ᵈ ε-closure₁ ps qs
                             else ε-closure₁ ps qs

  one-step : List Q → DecSubset Q → DecSubset Q
  one-step []       qs = ø
  one-step (p ∷ ps) qs = if p ∈ᵈ qs
                         then δ p E ⋃ᵈ one-step ps qs
                         else one-step ps qs

  ε-closure₂ : DecSubset Q → DecSubset Q
  ε-closure₂ qs = let ps = one-step It qs in
                  if qs ≈ᵈ ps
                  then qs
                  else ø --undefined --ε-closure₂ ps
  
  ε-closure₃ : ℕ → DecSubset Q → DecSubset Q
  ε-closure₃ zero    qs = qs
  ε-closure₃ (suc n) qs = let ps = one-step It qs in
                          if qs ≈ᵈ ps
                          then qs
                          else ε-closure₃ n ps

  {- below are the proofs of ⊢ᵏ ⇔ ⊢ᵏ₂ -}
  find-p : ∀ q wᵉ n q' wᵉ'
           → (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ')
           → Q
  find-p q ._ zero    .p  .uᵉ  (p , a , uᵉ , refl , prf₁ , (refl , refl)) = q
  find-p q ._ (suc n)  q'  wᵉ' (p , a , uᵉ , refl , prf₁ , prf₂)          = find-p p uᵉ n q' wᵉ' prf₂
  
  find-a : ∀ q wᵉ n q' wᵉ'
           → (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ')
           → Σᵉ
  find-a q ._ zero    .p  .uᵉ  (p , aᵉ , uᵉ , refl , prf₁ , (refl , refl)) = aᵉ
  find-a q ._ (suc n)  q'  wᵉ' (p , aᵉ , uᵉ , refl , prf₁ , prf₂)          = find-a p uᵉ n q' wᵉ' prf₂
  
  ⊢ᵏ₂-lem₈ : ∀ q wᵉ n q' wᵉ'
             → (prf : (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ'))
             → Σ[ p ∈ Q ] Σ[ a ∈ Σᵉ ] ( p ≡ find-p q wᵉ n q' wᵉ' prf × a ≡ find-a q wᵉ n q' wᵉ' prf × (p , a , wᵉ') ⊢ (q' , wᵉ') )
  ⊢ᵏ₂-lem₈ q ._ zero    .p  .uᵉ  (p , a , uᵉ , refl , prf₁ , (refl , refl)) = q , a , refl , refl , prf₁
  ⊢ᵏ₂-lem₈ q ._ (suc n)  q'  wᵉ' (p , a , uᵉ , refl , prf₁ , prf₂)          = ⊢ᵏ₂-lem₈ p uᵉ n q' wᵉ' prf₂
  
  ⊢ᵏ₂-lem₇ : ∀ q wᵉ n q' wᵉ' p a
             → (prf : (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ'))
             → p ≡ find-p q wᵉ n q' wᵉ' prf
             → a ≡ find-a q wᵉ n q' wᵉ' prf
             → (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ')
  ⊢ᵏ₂-lem₇ q ._ zero    .p' .uᵉ  p a (p' , a' , uᵉ , refl , prf₁ , (refl , refl)) p≡q a≡a'
    = sym p≡q , cong (λ a → a ∷ uᵉ) (sym a≡a')
  ⊢ᵏ₂-lem₇ q ._ (suc n)  q'  wᵉ' p a (p' , a' , uᵉ , refl , prf₁ ,          prf₂) p≡p a≡a
    = p' , a' , uᵉ , refl , prf₁ , ⊢ᵏ₂-lem₇ p' uᵉ n q' wᵉ' p a prf₂ p≡p a≡a
  
  ⊢ᵏ₂-lem₆ : ∀ q wᵉ n q' wᵉ'
             → (prf : (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ'))
             → Σ[ p ∈ Q ] Σ[ a ∈ Σᵉ ] ( p ≡ find-p q wᵉ n q' wᵉ' prf × a ≡ find-a q wᵉ n q' wᵉ' prf × (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ') )
  ⊢ᵏ₂-lem₆ q wᵉ n q' wᵉ' prf = p , a , refl , refl , ⊢ᵏ₂-lem₇ q wᵉ n q' wᵉ' p a prf refl refl
    where
      p : Q
      p = find-p q wᵉ n q' wᵉ' prf
      a : Σᵉ
      a = find-a q wᵉ n q' wᵉ' prf
  
  ⊢ᵏ₂-lem₅ : ∀ q wᵉ n q' wᵉ'
             → (prf : (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ'))
             → Σ[ p ∈ Q ] Σ[ a ∈ Σᵉ ] (p ≡ find-p q wᵉ n q' wᵉ' prf × a ≡ find-a q wᵉ n q' wᵉ' prf × (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ') × (p , a , wᵉ') ⊢ (q' , wᵉ'))
  ⊢ᵏ₂-lem₅ q wᵉ n q' wᵉ' prf with ⊢ᵏ₂-lem₆ q wᵉ n q' wᵉ' prf | ⊢ᵏ₂-lem₈ q wᵉ n q' wᵉ' prf
  ... | p₁ , a₁ , p₁≡p , a₁≡a , prf₁ |  p₂ , a₂ , p₂≡p , a₂≡a , prf₂ = p₁ , a₁ , p₁≡p , a₁≡a , prf₁ , prf₂''
    where
      prf₂' : (p₁ , a₂ , wᵉ') ⊢ (q' , wᵉ')
      prf₂' = subst (λ p₁ → (p₁ , a₂ , wᵉ') ⊢ (q' , wᵉ')) (trans p₂≡p (sym p₁≡p)) prf₂
      prf₂'' : (p₁ , a₁ , wᵉ') ⊢ (q' , wᵉ')
      prf₂'' = subst (λ a₁ → (p₁ , a₁ , wᵉ') ⊢ (q' , wᵉ')) (trans a₂≡a (sym a₁≡a)) prf₂'

  ⊢ᵏ₂-lem₄ : ∀ q wᵉ n q' wᵉ'
             → (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ')
             → (q , wᵉ) ⊢ᵏ₂ suc n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₄ q wᵉ n q' wᵉ' prf with ⊢ᵏ₂-lem₅ q wᵉ n q' wᵉ' prf
  ... | p' , a' , p≡p' , a≡a' , prf₁ = p , a , prf₁''
    where
      p : Q
      p = find-p q wᵉ n q' wᵉ' prf
      a : Σᵉ
      a = find-a q wᵉ n q' wᵉ' prf
      prf₁' : (q , wᵉ) ⊢ᵏ n ─ (p , a' ∷ wᵉ') × (p , a' , wᵉ') ⊢ (q' , wᵉ')
      prf₁' = subst (λ p → (q , wᵉ) ⊢ᵏ n ─ (p , a' ∷ wᵉ') × (p , a' , wᵉ') ⊢ (q' , wᵉ')) p≡p' prf₁
      prf₁'' : (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ') × (p , a , wᵉ') ⊢ (q' , wᵉ')
      prf₁'' = subst (λ a → (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ') × (p , a , wᵉ') ⊢ (q' , wᵉ')) a≡a' prf₁'

  ⊢ᵏ₂-lem₉ : ∀ {q wᵉ n p a q' wᵉ'}
             → (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ')
             → (p , a , wᵉ') ⊢ (q' , wᵉ')
             → (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₉ {.p} {._} {zero}  {p} {a} {q'} {wᵉ'} (refl , refl) prf = q' , a , wᵉ' , refl , prf , (refl , refl)
  ⊢ᵏ₂-lem₉ {q}  {._} {suc n} {p} {a} {q'} {wᵉ'} (p₁ , a₁ , u₁ , refl , prf₁ , prf₂) prf₃ = p₁ , a₁ , u₁ , refl , prf₁ , ⊢ᵏ₂-lem₉ {p₁} {u₁} {n} {p} {a} {q'} {wᵉ'} prf₂ prf₃
  
  ⊢ᵏ₂-lem₃ : ∀ {q wᵉ n q' wᵉ'}
             → (q , wᵉ) ⊢ᵏ₂ n ─ (q' , wᵉ')
             → (q , wᵉ) ⊢ᵏ n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₃ {q} {wᵉ} {zero}  {.q} {.wᵉ} (refl , refl) = refl , refl
  ⊢ᵏ₂-lem₃ {q} {wᵉ} {suc n} {q'} {wᵉ'} (p , a , prf₁ , prf₂) = ⊢ᵏ₂-lem₉ {q} {wᵉ} {n} {p} {a} {q'} {wᵉ'} prf₁ prf₂

  ⊢ᵏ₂-lem₂ : ∀ {q wᵉ n q' wᵉ'}
             → (q , wᵉ) ⊢ᵏ n ─ (q' , wᵉ')
             → (q , wᵉ) ⊢ᵏ₂ n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₂ {q} {wᵉ} {zero}  {.q} {.wᵉ} (refl , refl) = refl , refl
  ⊢ᵏ₂-lem₂ {q} {wᵉ} {suc n} {q'} {wᵉ'} prf           = ⊢ᵏ₂-lem₄ q wᵉ n q' wᵉ' prf

  ⊢ᵏ₂-lem₁ : ∀ {q wᵉ n q' wᵉ'}
             → (q , wᵉ) ⊢ᵏ n ─ (q' , wᵉ') ⇔ (q , wᵉ) ⊢ᵏ₂ n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₁ {q} {wᵉ} {n} {q'} {wᵉ'} = ⊢ᵏ₂-lem₂ {q} {wᵉ} {n} {q'} {wᵉ'} , ⊢ᵏ₂-lem₃ {q} {wᵉ} {n} {q'} {wᵉ'}
  {- above are the proofs of ⊢ᵏ ⇔ ⊢ᵏ₂ -}

  {- below are the proofs of ⊢* ⇔ ⊢*₂ -}
  ⊢*-lem₄ : ∀ q wᵉ n q' wᵉ' p uᵉ m
            → (q , wᵉ) ⊢ᵏ n ─ (p , uᵉ)
            → (p , uᵉ) ⊢ᵏ m ─ (q' , wᵉ')
            → (q , wᵉ) ⊢ᵏ n + m ─ (q' , wᵉ')
  ⊢*-lem₄ .p wᵉ zero     q'  wᵉ' p .wᵉ m (refl , refl) prf
    = prf
  ⊢*-lem₄  q wᵉ (suc n)  q'  wᵉ' p  uᵉ m (r , a , vᵉ , prf₁ , prf₂ , prf₃) prf₄
    = r , a , vᵉ , prf₁ , prf₂ , ⊢*-lem₄ r vᵉ n q' wᵉ' p uᵉ m prf₃ prf₄

  ⊢*-lem₃ : ∀ {q wᵉ q' wᵉ'}
            → (q , wᵉ) ⊢*  (q' , wᵉ')
            → (q , wᵉ) ⊢*₂ (q' , wᵉ')
  ⊢*-lem₃ {q} {wᵉ} {q'} {wᵉ'} (n , prf)
    = n , zero , q' , wᵉ' , prf , (refl , refl)
  
  ⊢*-lem₂ : ∀ {q wᵉ q' wᵉ'}
            → (q , wᵉ) ⊢*₂ (q' , wᵉ')
            → (q , wᵉ) ⊢*  (q' , wᵉ')
  ⊢*-lem₂ {q} {wᵉ} {q'} {wᵉ'} (n , m , p , uᵉ , prf₁ , prf₂)
    = n + m , ⊢*-lem₄ q wᵉ n q' wᵉ' p uᵉ m prf₁ prf₂
  
  ⊢*-lem₁ : ∀ {q wᵉ q' wᵉ'}
            → (q , wᵉ) ⊢* (q' , wᵉ') ⇔ (q , wᵉ) ⊢*₂ (q' , wᵉ')
  ⊢*-lem₁ = ⊢*-lem₃ , ⊢*-lem₂
  {- above are the proofs of ⊢* ⇔ ⊢*₂ -}
  
-- Language denoted by a ε-NFA
-- section 2.2.3: Finite Automata
-- L(nfa) = { w | ∃wᵉ∈Σᵉ*. w ≡ toΣ* wᵉ ∧ ∃q∈F. (q₀ , wᵉ) ⊢* (q , []) }
Lᵉᴺ : ε-NFA → Language
Lᵉᴺ nfa = λ w → Σ[ wᵉ ∈ Σᵉ* ] (w ≡ toΣ* wᵉ × Σ[ q ∈ Q ] (q ∈ᵍ F × (q₀ , wᵉ) ⊢* (q , [])))
  where
    open ε-NFA nfa
    open ε-NFA-Operations nfa
  


-- Nondeterministic finite automata w/o ε-step
-- section 2.2.3: Finite Automata
record NFA : Set₁ where
  field
    Q  : Set
    Q? : DecEq Q
    δ  : Q → Σ → DecSubset Q
    q₀ : Q
    F  : DecSubset Q
    It : List Q

module NFA-Operations (N : NFA) where
  open NFA N

  -- a move from (q , aw) to (q' , w)
  infix 7 _⊢_
  _⊢_ : (Q × Σ × Σ*) → (Q × Σ*) → Set
  (q , a , w) ⊢ (q' , w') = w ≡ w' × q' ∈ᵍ δ q a
  
  -- k moves from (q , w) to (q' , w')
  infix 7 _⊢ᵏ_─_
  _⊢ᵏ_─_ : (Q × Σ*) → ℕ → (Q × Σ*) → Set
  (q , w) ⊢ᵏ zero    ─ (q' , w')
    = q ≡ q' × w ≡ w'
  (q , w) ⊢ᵏ (suc n) ─ (q' , w')
    = Σ[ p ∈ Q ] Σ[ a ∈ Σ ] Σ[ u ∈ Σ* ]
      (w ≡ a ∷ u × (q , a , u) ⊢ (p , u) × (p , u) ⊢ᵏ n ─ (q' , w'))
                                  
  -- transitive closure of ⊢
  infix 7 _⊢*_
  _⊢*_ : (Q × Σ*) → (Q × Σ*) → Set
  (q , w) ⊢* (q' , w') = Σ[ n ∈ ℕ ] (q , w) ⊢ᵏ n ─ (q' , w')
  
-- Language denoted by a NFA
-- section 2.2.3: Finite Automata
Lᴺ : NFA → Language
Lᴺ nfa = λ w → Σ[ q ∈ Q ] (q ∈ᵍ F × (q₀ , w) ⊢* (q , []))
  where
    open NFA nfa
    open NFA-Operations nfa



-- Deterministic finite automata
-- section 2.2.3: Finite Automata
record DFA : Set₁ where
  field
    Q  : Set
    δ  : Q → Σ → Q
    q₀ : Q
    F  : DecSubset Q
  
module DFA-Operations (D : DFA) where
  open DFA D

  δ* : Q → Σ* → Q
  δ* q []      = q
  δ* q (a ∷ w) = δ* (δ q a) w
  
  δ₀ : Σ* → Q
  δ₀ w = δ* q₀ w

-- Language denoted by a DFA
Lᴰ : DFA → Language
Lᴰ dfa = λ w → δ₀ w ∈ᵍ F
  where
    open DFA dfa
    open DFA-Operations dfa


{- ∀dfa∈DFA. L(dfa) is decidable -}
Dec-Lᴰ : ∀ dfa → Decidable (Lᴰ dfa)
Dec-Lᴰ dfa w with (δ₀ w) ∈ᵈ F
 where
  open DFA dfa
  open DFA-Operations dfa
... | true  = yes refl
... | false = no (λ ())
