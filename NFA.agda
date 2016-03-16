{-
  Here the Automata and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 2.2: Regular sets, their generators, and their recognizers
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung
  Version 27-02-2016
-}
open import Util
module NFA (Σ : Set)(dec : DecEq Σ) where

open import Data.List hiding (any ; all) 
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Nat

open import Subset
open import Subset.DecidableSubset
  renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; Ø to Øᵈ ; _⋃_ to _⋃ᵈ_ ; _⋂_ to _⋂ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ
                 ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ≈-refl to ≈ᵈ-refl ; ≈-trans to ≈ᵈ-trans ; ≈-sym to ≈ᵈ-sym)
open import Data.Vec hiding (_++_) renaming (_∈_ to _∈ⱽ_ ; tail to tailⱽ)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import Language Σ dec

-- Nondeterministic finite automata w/o ε-step
-- section 2.2.3: Finite Automata
record NFA : Set₁ where
  field
    Q      : Set
    δ      : Q → Σ → DecSubset Q
    q₀     : Q
    F      : DecSubset Q
    Q?     : DecEq Q
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

module NFA-Properties (N : NFA) where
  open NFA N
  open NFA-Operations N

  -- adding a step at the end
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
