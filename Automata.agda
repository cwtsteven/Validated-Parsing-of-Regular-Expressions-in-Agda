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
open import Subset.DecidableSubset renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; _⋂_ to _⋂ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _≈_ to _≈ᵈ_)
open import Data.Vec hiding (_++_) renaming (_∈_ to _∈ⱽ_)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import Language Σ dec hiding (Ø ; _⋃_)

-- Nondeterministic finite automata with ε-step
-- section 2.2.3: Finite Automata
record ε-NFA : Set₁ where
  field
    Q     : Set
    δ     : Q → Σᵉ → DecSubset Q
    q₀    : Q
    F     : DecSubset Q
    Q?    : DecEq Q
    ∣Q∣   : ℕ
    It    : Vec Q ∣Q∣
    ∀q∈It : (q : Q) → (q ∈ⱽ It)

-- section 2.2.3: Finite Automata
module ε-NFA-Operations (N : ε-NFA) where
  open ε-NFA N
  open ≡-Reasoning

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
  (q , wᵉ) ⊢*₂ (q' , wᵉ')
    = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] Σ[ p ∈ Q ] Σ[ uᵉ ∈ Σᵉ* ]
      ((q , wᵉ) ⊢ᵏ n ─ (p , uᵉ) × (p , uᵉ) ⊢ᵏ m ─ (q' , wᵉ'))

  -- ε closure
  infix 7 _→εᵏ_─_
  _→εᵏ_─_ : Q → ℕ → Q → Set
  q →εᵏ zero  ─ q' = q ≡ q'
  q →εᵏ suc n ─ q' = Σ[ p ∈ Q ] ( p ∈ᵈ δ q E × p →εᵏ n ─ q' )
  

  infix 7 _→ε*_
  _→ε*_ : Q → Q → Set
  q →ε* q' = Σ[ n ∈ ℕ ] q →εᵏ n ─ q'

  →εᵏ-lem₁ : ∀ q n p q'
             → q →εᵏ n ─ p
             → q' ∈ᵈ δ p E
             → q →εᵏ suc n ─ q'
  →εᵏ-lem₁ q zero    .q q' refl q'∈δpE
    = q' , q'∈δpE , refl
  →εᵏ-lem₁ q (suc n)  p q' (p₁ , p∈δqE , prf) q'∈δpE
    = p₁ , p∈δqE , →εᵏ-lem₁ p₁ n p q' prf q'∈δpE

  →εᵏ-lem₂ : ∀ q n q'
             → q →εᵏ n ─ q'
             → Σ[ n₁ ∈ ℕ ] ( n₁ < ∣Q∣ × q →εᵏ n₁ ─ q' )
  →εᵏ-lem₂ q n q' prf = undefined

  open Vec-Rep Q? It ∀q∈It

  Dec-→ε* : ∀ q q' → Dec (q →ε* q')
  Dec-→ε* = undefined

  infix 6 _→ε*_⊢_
  _→ε*_⊢_ : Q → Σ → Q → Set
  q →ε* a ⊢ q' = Σ[ p ∈ Q ] ( q' ∈ᵈ δ p (α a) × q →ε* p )

  Dec-any→ε*⊢ : ∀ q a q' → Dec (any (λ p → q' ∈ᵈ δ p (α a) × q →ε* p) It)
  Dec-any→ε*⊢ q a q' = helper It
    where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (any (λ p → q' ∈ᵈ δ p (α a) × q →ε* p) ps)
      helper []       = no (λ z → z)
      helper (p ∷ ps) with q' ∈ᵈ? δ p (α a)
      helper (p ∷ ps) | true  with Dec-→ε* q p
      helper (p ∷ ps) | true  | yes q→ε*p = yes (inj₁ (refl , q→ε*p))
      helper (p ∷ ps) | true  | no  _     with helper ps
      helper (p ∷ ps) | true  | no  _     | yes prf₂ = yes (inj₂ prf₂)
      helper (p ∷ ps) | true  | no  prf₁  | no  prf₂ = no ¬any
        where
          ¬any : ¬ (true ≡ true × q →ε* p ⊎ any (λ p → q' ∈ᵈ δ p (α a) × q →ε* p) ps)
          ¬any (inj₁ (_ , prf₃)) = prf₁ prf₃
          ¬any (inj₂ any) = prf₂ any
      helper (p ∷ ps) | false with helper ps
      helper (p ∷ ps) | false | yes prf = yes (inj₂ prf)
      helper (p ∷ ps) | false | no  prf = no ¬any
        where
          ¬any : ¬ (false ≡ true × q →ε* p ⊎ any (λ p → q' ∈ᵈ δ p (α a) × q →ε* p) ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ prf₁) = prf prf₁

  Dec-→ε*⊢ : ∀ q a q' → Dec (q →ε* a ⊢ q')
  Dec-→ε*⊢ q a q' with Dec-any→ε*⊢ q a q'
  Dec-→ε*⊢ q a q' | yes prf = yes (Vec-any-lem₂ (λ p → q' ∈ᵈ δ p (α a) × q →ε* p) prf)
  Dec-→ε*⊢ q a q' | no  prf = no  (Vec-any-lem₄ (λ p → q' ∈ᵈ δ p (α a) × q →ε* p) prf)

  ∃q⊢a-q'? : ∀ {q a q'} → Dec (q →ε* a ⊢ q') → Bool
  ∃q⊢a-q'? (yes _) = true
  ∃q⊢a-q'? (no  _) = false


  _→ε*∈F : Q → Set
  q →ε*∈F = Σ[ p ∈ Q ] ( p ∈ᵈ F × q →ε* p )

  Dec-any→ε*∈F : ∀ q → Dec (any (λ p → p ∈ᵈ F × q →ε* p) It)
  Dec-any→ε*∈F q = helper It
    where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (any (λ p → p ∈ᵈ F × q →ε* p) ps)
      helper []       = no (λ z → z)
      helper (p ∷ ps) with p ∈ᵈ? F
      helper (p ∷ ps) | true  with Dec-→ε* q p
      helper (p ∷ ps) | true  | yes q→ε*p = yes (inj₁ (refl , q→ε*p))
      helper (p ∷ ps) | true  | no  _     with helper ps
      helper (p ∷ ps) | true  | no  _     | yes prf₂ = yes (inj₂ prf₂)
      helper (p ∷ ps) | true  | no  prf₁  | no  prf₂ = no ¬any
        where
          ¬any : ¬ (true ≡ true × q →ε* p ⊎ any (λ p₁ → p₁ ∈ᵈ F × q →ε* p₁) ps)
          ¬any (inj₁ (_ , prf₃)) = prf₁ prf₃
          ¬any (inj₂ any) = prf₂ any
      helper (p ∷ ps) | false with helper ps
      helper (p ∷ ps) | false | yes prf = yes (inj₂ prf)
      helper (p ∷ ps) | false | no  prf = no ¬any
        where
          ¬any : ¬ (false ≡ true × q →ε* p ⊎ any (λ p₁ → p₁ ∈ᵈ F × q →ε* p₁) ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ prf₁) = prf prf₁

  Dec-→ε*∈F : ∀ q → Dec (q →ε*∈F)
  Dec-→ε*∈F q with Dec-any→ε*∈F q
  Dec-→ε*∈F q | yes prf = yes (Vec-any-lem₂ (λ p → p ∈ᵈ F × q →ε* p) prf)
  Dec-→ε*∈F q | no  prf = no  (Vec-any-lem₄ (λ p → p ∈ᵈ F × q →ε* p) prf)

  ∃q∈F? : ∀ {q} → Dec (q →ε*∈F) → Bool
  ∃q∈F? (yes _) = true
  ∃q∈F? (no  _) = false
  
  

  {- below are the proofs of ⊢ᵏ ⇔ ⊢ᵏ₂ -}
  find-p : ∀ q wᵉ n q' wᵉ'
           → (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ')
           → Q
  find-p q ._ zero    .p  .uᵉ  (p , a , uᵉ , refl , prf₁ , (refl , refl))
    = q
  find-p q ._ (suc n)  q'  wᵉ' (p , a , uᵉ , refl , prf₁ , prf₂)
    = find-p p uᵉ n q' wᵉ' prf₂
  
  find-a : ∀ q wᵉ n q' wᵉ'
           → (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ')
           → Σᵉ
  find-a q ._ zero    .p  .uᵉ  (p , aᵉ , uᵉ , refl , prf₁ , (refl , refl))
    = aᵉ
  find-a q ._ (suc n)  q'  wᵉ' (p , aᵉ , uᵉ , refl , prf₁ , prf₂)
    = find-a p uᵉ n q' wᵉ' prf₂
  
  ⊢ᵏ₂-lem₈ : ∀ q wᵉ n q' wᵉ'
             → (prf : (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ'))
             → Σ[ p ∈ Q ] Σ[ a ∈ Σᵉ ]
               (p ≡ find-p q wᵉ n q' wᵉ' prf
                 × a ≡ find-a q wᵉ n q' wᵉ' prf
                 × (p , a , wᵉ') ⊢ (q' , wᵉ'))
  ⊢ᵏ₂-lem₈ q ._ zero    .p  .uᵉ  (p , a , uᵉ , refl , prf₁ , (refl , refl))
    = q , a , refl , refl , prf₁
  ⊢ᵏ₂-lem₈ q ._ (suc n)  q'  wᵉ' (p , a , uᵉ , refl , prf₁ , prf₂)
    = ⊢ᵏ₂-lem₈ p uᵉ n q' wᵉ' prf₂
  
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
             → Σ[ p ∈ Q ] Σ[ a ∈ Σᵉ ]
               (p ≡ find-p q wᵉ n q' wᵉ' prf
                 × a ≡ find-a q wᵉ n q' wᵉ' prf
                 × (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ'))
  ⊢ᵏ₂-lem₆ q wᵉ n q' wᵉ' prf
    = p , a , refl , refl , ⊢ᵏ₂-lem₇ q wᵉ n q' wᵉ' p a prf refl refl
    where
      p : Q
      p = find-p q wᵉ n q' wᵉ' prf
      a : Σᵉ
      a = find-a q wᵉ n q' wᵉ' prf
  
  ⊢ᵏ₂-lem₅ : ∀ q wᵉ n q' wᵉ'
             → (prf : (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ'))
             → Σ[ p ∈ Q ] Σ[ a ∈ Σᵉ ]
               (p ≡ find-p q wᵉ n q' wᵉ' prf
                 × a ≡ find-a q wᵉ n q' wᵉ' prf
                 × (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ')
                 × (p , a , wᵉ') ⊢ (q' , wᵉ'))
  ⊢ᵏ₂-lem₅ q wᵉ n q' wᵉ' prf with ⊢ᵏ₂-lem₆ q wᵉ n q' wᵉ' prf | ⊢ᵏ₂-lem₈ q wᵉ n q' wᵉ' prf
  ... | p₁ , a₁ , p₁≡p , a₁≡a , prf₁ |  p₂ , a₂ , p₂≡p , a₂≡a , prf₂
    = p₁ , a₁ , p₁≡p , a₁≡a , prf₁ , prf₂''
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
  ⊢ᵏ₂-lem₉ {q}  {._} {suc n} {p} {a} {q'} {wᵉ'} (p₁ , a₁ , u₁ , refl , prf₁ , prf₂) prf₃
    = p₁ , a₁ , u₁ , refl , prf₁ , ⊢ᵏ₂-lem₉ {p₁} {u₁} {n} {p} {a} {q'} {wᵉ'} prf₂ prf₃
  
  ⊢ᵏ₂-lem₃ : ∀ {q wᵉ n q' wᵉ'}
             → (q , wᵉ) ⊢ᵏ₂ n ─ (q' , wᵉ')
             → (q , wᵉ) ⊢ᵏ n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₃ {q} {wᵉ} {zero}  {.q} {.wᵉ} (refl , refl) = refl , refl
  ⊢ᵏ₂-lem₃ {q} {wᵉ} {suc n} {q'} {wᵉ'} (p , a , prf₁ , prf₂)
    = ⊢ᵏ₂-lem₉ {q} {wᵉ} {n} {p} {a} {q'} {wᵉ'} prf₁ prf₂

  ⊢ᵏ₂-lem₂ : ∀ {q wᵉ n q' wᵉ'}
             → (q , wᵉ) ⊢ᵏ n ─ (q' , wᵉ')
             → (q , wᵉ) ⊢ᵏ₂ n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₂ {q} {wᵉ} {zero}  {.q} {.wᵉ} (refl , refl)
    = refl , refl
  ⊢ᵏ₂-lem₂ {q} {wᵉ} {suc n} {q'} {wᵉ'} prf
    = ⊢ᵏ₂-lem₄ q wᵉ n q' wᵉ' prf

  ⊢ᵏ₂-lem₁ : ∀ {q wᵉ n q' wᵉ'}
             → (q , wᵉ) ⊢ᵏ n ─ (q' , wᵉ') ⇔ (q , wᵉ) ⊢ᵏ₂ n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₁ {q} {wᵉ} {n} {q'} {wᵉ'}
    = ⊢ᵏ₂-lem₂ {q} {wᵉ} {n} {q'} {wᵉ'} , ⊢ᵏ₂-lem₃ {q} {wᵉ} {n} {q'} {wᵉ'}
  {- above are the proofs of ⊢ᵏ ⇔ ⊢ᵏ₂ -}

  {- below are the proofs of ⊢* ⇔ ⊢*₂ -}
  ⊢*-lem₄ : ∀ q wᵉ n p uᵉ m q' wᵉ'
            → (q , wᵉ) ⊢ᵏ n ─ (p , uᵉ)
            → (p , uᵉ) ⊢ᵏ m ─ (q' , wᵉ')
            → (q , wᵉ) ⊢ᵏ n + m ─ (q' , wᵉ')
  ⊢*-lem₄ .p wᵉ zero     p .wᵉ m q'  wᵉ' (refl , refl) prf
    = prf
  ⊢*-lem₄  q wᵉ (suc n)  p  uᵉ m q'  wᵉ' (r , a , vᵉ , prf₁ , prf₂ , prf₃) prf₄
    = r , a , vᵉ , prf₁ , prf₂ , ⊢*-lem₄ r vᵉ n p uᵉ m q' wᵉ' prf₃ prf₄

  ⊢*-lem₃ : ∀ {q wᵉ q' wᵉ'}
            → (q , wᵉ) ⊢*  (q' , wᵉ')
            → (q , wᵉ) ⊢*₂ (q' , wᵉ')
  ⊢*-lem₃ {q} {wᵉ} {q'} {wᵉ'} (n , prf)
    = n , zero , q' , wᵉ' , prf , (refl , refl)
  
  ⊢*-lem₂ : ∀ {q wᵉ q' wᵉ'}
            → (q , wᵉ) ⊢*₂ (q' , wᵉ')
            → (q , wᵉ) ⊢*  (q' , wᵉ')
  ⊢*-lem₂ {q} {wᵉ} {q'} {wᵉ'} (n , m , p , uᵉ , prf₁ , prf₂)
    = n + m , ⊢*-lem₄ q wᵉ n p uᵉ m q' wᵉ' prf₁ prf₂
  
  ⊢*-lem₁ : ∀ {q wᵉ q' wᵉ'}
            → (q , wᵉ) ⊢* (q' , wᵉ') ⇔ (q , wᵉ) ⊢*₂ (q' , wᵉ')
  ⊢*-lem₁ = ⊢*-lem₃ , ⊢*-lem₂
  {- above are the proofs of ⊢* ⇔ ⊢*₂ -}
  
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
    Q     : Set
    Q?    : DecEq Q
    δ     : Q → Σ → DecSubset Q
    q₀    : Q
    F     : DecSubset Q
    ∣Q∣   : ℕ
    It    : Vec Q ∣Q∣
    ∀q∈It : ∀ q → q ∈ⱽ It

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

  open Vec-Rep {Q} {∣Q∣} Q? It ∀q∈It

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
    --Q? : DecEq Q
    δ  : Q → Σ → Q
    q₀ : Q
    F  : DecSubset Q
    _≋_ : (q q' : Q) → Set
    ≋-refl  : Reflexive _≋_
    ≋-sym   : Symmetric _≋_
    ≋-trans : Transitive _≋_
    ≋-subst : {q q' : Q} → (P : Q → Set) → q ≋ q' → P q → P q'
  
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
  δ₀-lem₅ : ∀ q w n q'
           → q' ∈ᵈ F
           → (q , w) ⊢ᵏ n ─ (q' , [])
           → δ* q w ∈ᵈ F
  δ₀-lem₅ q .[] zero    q' q'∈F (q≋q' , refl)
    = ≋-subst (λ q' → q' ∈ᵈ F) (≋-sym q≋q') q'∈F
  δ₀-lem₅ q ._  (suc n) q' q'∈F (p , a , u , refl , (refl , prf₁) , prf₂)
    = ≋-subst (λ p → δ* p u ∈ᵈ F) prf₁ (δ₀-lem₅ p u n q' q'∈F prf₂)

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
