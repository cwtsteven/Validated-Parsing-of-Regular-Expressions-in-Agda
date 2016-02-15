{-
  Here the Automata and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 2.2: Regular sets, their generators, and their recognizers
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 10-01-2016
-}
open import Util
module Automata (Σ : Set)(dec : DecEq Σ) where

open import Data.List hiding (any ; all) 
open import Data.Bool
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit hiding (_≤_ ; _≤?_)
open import Data.Empty
open import Data.Nat


open import Subset
open import Subset.DecidableSubset
  renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; _⋂_ to _⋂ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ
                 ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ≈-refl to ≈ᵈ-refl ; ≈-trans to ≈ᵈ-trans ; ≈-sym to ≈ᵈ-sym)
open import Data.Vec hiding (_++_) renaming (_∈_ to _∈ⱽ_ ; tail to tailⱽ)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import Language Σ dec hiding (Ø ; _⋃_ ; ⟦_⟧)

open ≡-Reasoning

-- Nondeterministic finite automata with ε-step
-- section 2.2.3: Finite Automata
record ε-NFA : Set₁ where
  field
    Q      : Set
    δ      : Q → Σᵉ → DecSubset Q
    q₀     : Q
    F      : DecSubset Q
    ∀qEq   : ∀ q → q ∈ᵈ δ q E
    Q?     : DecEq Q
    ∣Q∣-1  : ℕ
    It     : Vec Q (suc ∣Q∣-1)
    ∀q∈It  : (q : Q) → (q ∈ⱽ It)
    unique : Unique It

-- section 2.2.3: Finite Automata
module ε-NFA-Operations (N : ε-NFA) where
  open ε-NFA N

  -- a move from (q , aw) to (q' , w)
  infix 7 _⊢_
  _⊢_ : (Q × Σᵉ × Σᵉ*) → (Q × Σᵉ*) → Set
  (q , aᵉ , wᵉ) ⊢ (q' , wᵉ') = wᵉ ≡ wᵉ' × q' ∈ᵈ δ q aᵉ

  -- k moves from (q , w) to (q' , w')
  infix 7 _⊢ᵏ_─_
  _⊢ᵏ_─_ : (Q × Σᵉ*) → ℕ → (Q × Σᵉ*) → Set
  (q , wᵉ) ⊢ᵏ zero    ─ (q' , wᵉ')
    = q ≡ q' × wᵉ ≡ wᵉ'
  (q , wᵉ) ⊢ᵏ (suc n) ─ (q' , wᵉ')
    = Σ[ p ∈ Q ] Σ[ aᵉ ∈ Σᵉ ] Σ[ uᵉ ∈ Σᵉ* ]
      ( wᵉ ≡ aᵉ ∷ uᵉ × (q , aᵉ , uᵉ) ⊢ (p , uᵉ) × (p , uᵉ) ⊢ᵏ n ─ (q' , wᵉ') )
  
  -- transitive closure of ⊢
  infix 7 _⊢*_
  _⊢*_ : (Q × Σᵉ*) → (Q × Σᵉ*) → Set
  (q , wᵉ) ⊢* (q' , wᵉ') = Σ[ n ∈ ℕ ] (q , wᵉ) ⊢ᵏ n ─ (q' , wᵉ')
 
  
-- Language denoted by a ε-NFA
-- section 2.2.3: Finite Automata
-- L(nfa) = { w | ∃wᵉ∈Σᵉ*. w ≡ toΣ* wᵉ ∧ ∃q∈F. (q₀ , wᵉ) ⊢* (q , []) }
Lᵉᴺ : ε-NFA → Language
Lᵉᴺ nfa = λ w → Σ[ wᵉ ∈ Σᵉ* ] (w ≡ toΣ* wᵉ × ( Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , wᵉ) ⊢* (q , [])) ))
  where
    open ε-NFA nfa
    open ε-NFA-Operations nfa
  


-- Nondeterministic finite automata w/o ε-step
-- section 2.2.3: Finite Automata
record NFA : Set₁ where
  field
    Q      : Set
    Q?     : DecEq Q
    δ      : Q → Σ → DecSubset Q
    q₀     : Q
    F      : DecSubset Q
    ∣Q∣-1  : ℕ
    It     : Vec Q (suc ∣Q∣-1)
    ∀q∈It  : ∀ q → q ∈ⱽ It
    unique : Unique It

module NFA-Operations (N : NFA) where
  open NFA N

  -- a move from (q , aw) to (q' , w)
  infix 7 _⊢_
  _⊢_ : (Q × Σ × Σ*) → (Q × Σ*) → Set
  (q , a , w) ⊢ (q' , w') = w ≡ w' × q' ∈ᵈ δ q a
  
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

  
  ⊢ᵏ₂-lem₉ : ∀ {q wᵉ n p a q' wᵉ'}
             → (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ')
             → (p , a , wᵉ') ⊢ (q' , wᵉ')
             → (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₉ {.p} {._} {zero}  {p} {a} {q'} {wᵉ'} (refl , refl) prf
    = q' , a , wᵉ' , refl , prf , (refl , refl)
  ⊢ᵏ₂-lem₉ {q}  {._} {suc n} {p} {a} {q'} {wᵉ'} (p₁ , a₁ , u₁ , refl , prf₁ , prf₂) prf₃
    = p₁ , a₁ , u₁ , refl , prf₁ , ⊢ᵏ₂-lem₉ {p₁} {u₁} {n} {p} {a} {q'} {wᵉ'} prf₂ prf₃


  {- Belows are operations/proofs that will be used when performing powerest construction -}

  open Vec-Rep {Q} {_} Q? It ∀q∈It unique

  -- proving the Decidability of (q' ∈ δ qs a) using Vector reprsentation
  Dec-any-⊢ : ∀ qs a q' → Dec (any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) It)
  Dec-any-⊢ qs a q' = helper It
    where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) ps)
      helper [] = no (λ z → z)
      helper (p ∷ ps) with p ∈ᵈ? qs | q' ∈ᵈ? δ p a
      helper (p ∷ ps) | true  | true  = yes (inj₁ (refl , refl))
      helper (p ∷ ps) | true  | false with helper ps
      helper (p ∷ ps) | true  | false | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | true  | false | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (true ≡ true × false ≡ true ⊎ any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) ps)
          ¬any (inj₁ (_ , ()))
          ¬any (inj₂ anyps) = ¬anyps anyps
      helper (p ∷ ps) | false | q'∈?δpa  with helper ps
      helper (p ∷ ps) | false | q'∈?δpa  | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | false | q'∈?δpa  | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (false ≡ true × q'∈?δpa ≡ true ⊎ any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ anyps) = ¬anyps anyps

  -- proving the Decidability of (q' ∈ δ qs a)
  Dec-⊢ : ∀ qs a q' → Dec ( Σ[ q ∈ Q ] ( q ∈ᵈ qs × q' ∈ᵈ δ q a ) )
  Dec-⊢ qs a q' with Dec-any-⊢ qs a q'
  Dec-⊢ qs a q' | yes prf = yes (Vec-any-lem₂ (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) prf)
  Dec-⊢ qs a q' | no  prf = no  (Vec-any-lem₄ (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q a) prf)


  -- proving the Decidability of (qs ∈ F) using Vector representation
  Dec-any-qs∈F : ∀ qs → Dec ( any (λ q → q ∈ᵈ qs × q ∈ᵈ F) It )
  Dec-any-qs∈F qs = helper It
    where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (any (λ q → q ∈ᵈ qs × q ∈ᵈ F) ps)
      helper [] = no (λ z → z)
      helper (p ∷ ps) with p ∈ᵈ? qs | p ∈ᵈ? F
      helper (p ∷ ps) | true  | true  = yes (inj₁ (refl , refl))
      helper (p ∷ ps) | true  | false with helper ps
      helper (p ∷ ps) | true  | false | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | true  | false | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (true ≡ true × false ≡ true ⊎ any (λ q → q ∈ᵈ qs × q ∈ᵈ F) ps)
          ¬any (inj₁ (_ , ()))
          ¬any (inj₂ anyps) = ¬anyps anyps
      helper (p ∷ ps) | false | p∈?F  with helper ps
      helper (p ∷ ps) | false | p∈?F  | yes anyps = yes (inj₂ anyps)
      helper (p ∷ ps) | false | p∈?F  | no ¬anyps = no  ¬any
        where
          ¬any : ¬ (false ≡ true × p∈?F ≡ true ⊎ any (λ q → q ∈ᵈ qs × q ∈ᵈ F) ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ anyps) = ¬anyps anyps

  -- proving the Decidability of (qs ∈ F) using Vector representation
  Dec-qs∈F : ∀ qs → Dec ( Σ[ q ∈ Q ] ( q ∈ᵈ qs × q ∈ᵈ F) )
  Dec-qs∈F qs with Dec-any-qs∈F qs
  Dec-qs∈F qs | yes prf = yes (Vec-any-lem₂ (λ q → q ∈ᵈ qs × q ∈ᵈ F) prf)
  Dec-qs∈F qs | no  prf = no  (Vec-any-lem₄ (λ q → q ∈ᵈ qs × q ∈ᵈ F) prf)
  
  
-- Language denoted by a NFA
-- section 2.2.3: Finite Automata
Lᴺ : NFA → Language
Lᴺ nfa = λ w → Σ[ q ∈ Q ] (q ∈ᵈ F × (q₀ , w) ⊢* (q , []))
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
    _≋_ : (q q' : Q) → Set
    ≋-refl  : Reflexive _≋_
    ≋-sym   : Symmetric _≋_
    ≋-trans : Transitive _≋_
    F-lem   : ∀ {q} {p}   → q ≋ p → q ∈ᵈ F → p ∈ᵈ F
    δ-lem   : ∀ {q} {p} a → q ≋ p → δ q a ≋ δ p a
  
module DFA-Operations (D : DFA) where
  open DFA D
  
  -- a move from (q , aw) to (q' , w)
  infix 7 _⊢_
  _⊢_ : (Q × Σ × Σ*) → (Q × Σ*) → Set
  (q , a , w) ⊢ (q' , w') = w ≡ w' × q' ≋ δ q a

  
  -- k moves from (q , w) to (q' , w')
  infix 7 _⊢ᵏ_─_
  _⊢ᵏ_─_ : (Q × Σ*) → ℕ → (Q × Σ*) → Set
  (q , w) ⊢ᵏ zero    ─ (q' , w')
    = q ≋ q' × w ≡ w'
  (q , w) ⊢ᵏ (suc n) ─ (q' , w')
    = Σ[ p ∈ Q ] Σ[ a ∈ Σ ] Σ[ u ∈ Σ* ]
      (w ≡ a ∷ u × (q , a , u) ⊢ (p , u) × (p , u) ⊢ᵏ n ─ (q' , w'))

  -- transitive closure of ⊢
  infix 7 _⊢*_
  _⊢*_ : (Q × Σ*) → (Q × Σ*) → Set
  (q , w) ⊢* (q' , w') = Σ[ n ∈ ℕ ] (q , w) ⊢ᵏ n ─ (q' , w')

  -- Alternative definition for running the DFA
  δ* : Q → Σ* → Q
  δ* q []      = q
  δ* q (a ∷ w) = δ* (δ q a) w
  
  δ₀ : Σ* → Q
  δ₀ w = δ* q₀ w


  -- proving the two definitons are equivalent, i.e. δ₀ w ∈ᵈ F ⇔ Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) )
  δ₀-lem₇ : ∀ q w p
            → q ≋ p
            → δ* q w ≋ δ* p w
  δ₀-lem₇ q []      p q≋p = q≋p
  δ₀-lem₇ q (a ∷ w) p q≋p = δ₀-lem₇ (δ q a) w (δ p a) (δ-lem a q≋p)

  δ₀-lem₅ : ∀ q w n q'
           → q' ∈ᵈ F
           → (q , w) ⊢ᵏ n ─ (q' , [])
           → δ* q w ∈ᵈ F
  δ₀-lem₅ q .[] zero    q' q'∈F (q≋q' , refl)
    = F-lem (≋-sym q≋q') q'∈F
  δ₀-lem₅ q ._  (suc n) q' q'∈F (p , a , u , refl , (refl , prf₁) , prf₂)
    = let prf₃ = δ₀-lem₇ p u (δ q a) prf₁ in
      F-lem prf₃ (δ₀-lem₅ p u n q' q'∈F prf₂)

  δ₀-lem₃ : ∀ w
            → Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) )
            → δ₀ w ∈ᵈ F  
  δ₀-lem₃ w (q , q∈F , n , prf) = δ₀-lem₅ q₀ w n q q∈F prf

  δ₀-lem₆ : ∀ q w
            → δ* q w ∈ᵈ F
            → Σ[ q' ∈ Q ] ( q' ∈ᵈ F × ( Σ[ n ∈ ℕ ] (q , w) ⊢ᵏ n ─ (q' , []) ) )
  δ₀-lem₆ q []      prf = q  , prf , zero , (≋-refl , refl)
  δ₀-lem₆ q (a ∷ w) prf with δ₀-lem₆ (δ q a) w prf
  ... | q' , q'∈F , n , prf₁ = q' , q'∈F , suc n , (δ q a , a , w , refl , (refl , ≋-refl) , prf₁)

  δ₀-lem₂ : ∀ w
            → δ₀ w ∈ᵈ F
            → Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) )
  δ₀-lem₂ w prf = δ₀-lem₆ q₀ w prf

  δ₀-lem₁ : ∀ w
            → δ₀ w ∈ᵈ F ⇔ ( Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) ) )
  δ₀-lem₁ w = δ₀-lem₂ w , δ₀-lem₃ w

  -- 
  δ₀-lem₄ : ∀ w
            → ¬ δ₀ w ∈ᵈ F 
            → ¬ ( Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) ) )
  δ₀-lem₄ w ¬δ₀w∈F prf = ⊥-elim (¬δ₀w∈F (δ₀-lem₃ w prf))

-- Language denoted by a DFA
Lᴰ : DFA → Language
Lᴰ dfa = λ w → Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) )
  where
    open DFA dfa
    open DFA-Operations dfa


{- ∀dfa∈DFA. L(dfa) is decidable -}
Dec-Lᴰ : ∀ dfa → Decidable (Lᴰ dfa)
Dec-Lᴰ dfa w with (δ₀ w) ∈ᵈ? F | inspect (λ w → (δ₀ w) ∈ᵈ? F) w
 where
  open DFA dfa
  open DFA-Operations dfa
... | true  | [ prf ] = yes (δ₀-lem₂ w prf)
 where
  open DFA dfa
  open DFA-Operations dfa
... | false | [ prf ] = no (δ₀-lem₄ w (Subset.DecidableSubset.∈-lem₂ {Q} {δ₀ w} {F} prf))
 where
  open DFA dfa
  open DFA-Operations dfa
