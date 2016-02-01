{-
  Here the Automata and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 2.2: Regular sets, their generators, and their recognizers
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 10-01-2016
-}
open import Util
module Automata (Σ : Set) where

open import Data.List hiding (any ; all)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit hiding (_≤_ ; _≤?_)
open import Data.Empty
open import Data.Nat


open import Subset
open import Subset.DecidableSubset renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ)
open import Data.Vec hiding (_++_) renaming (_∈_ to _∈ⱽ_)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import Language Σ hiding (Ø ; _⋃_)

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
  (q , wᵉ) ⊢*₂ (q' , wᵉ') = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] Σ[ p ∈ Q ] Σ[ uᵉ ∈ Σᵉ* ]
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
  →εᵏ-lem₁ q zero    .q q' refl q'∈δpE = q' , q'∈δpE , refl
  →εᵏ-lem₁ q (suc n)  p q' (p₁ , p∈δqE , prf) q'∈δpE = p₁ , p∈δqE , →εᵏ-lem₁ p₁ n p q' prf q'∈δpE

  →εᵏ-lem₂ : ∀ q n q'
             → q →εᵏ n ─ q'
             → Σ[ n₁ ∈ ℕ ] ( n₁ < ∣Q∣ × q →εᵏ n₁ ─ q' )
  →εᵏ-lem₂ q n q' prf = undefined

  open Vec-Rep-Lemmas Q? It ∀q∈It

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
          ¬any : ¬ (true ≡ true × q →ε* p ⊎ any (λ p₁ → q' ∈ᵈ δ p₁ (α a) × q →ε* p₁) ps)
          ¬any (inj₁ (_ , prf₃)) = prf₁ prf₃
          ¬any (inj₂ any) = prf₂ any
      helper (p ∷ ps) | false with helper ps
      helper (p ∷ ps) | false | yes prf = yes (inj₂ prf)
      helper (p ∷ ps) | false | no  prf = no ¬any
        where
          ¬any : ¬ (false ≡ true × q →ε* p ⊎ any (λ p₁ → q' ∈ᵈ δ p₁ (α a) × q →ε* p₁) ps)
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
Lᵉᴺ nfa = λ w → Σ[ wᵉ ∈ Σᵉ* ] (w ≡ toΣ* wᵉ × Σ[ q ∈ Q ] (q ∈ᵈ F × (q₀ , wᵉ) ⊢* (q , [])))
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

  ⊢ᵏ₂-lem₉ : ∀ {q wᵉ n p a q' wᵉ'}
             → (q , wᵉ) ⊢ᵏ n ─ (p , a ∷ wᵉ')
             → (p , a , wᵉ') ⊢ (q' , wᵉ')
             → (q , wᵉ) ⊢ᵏ suc n ─ (q' , wᵉ')
  ⊢ᵏ₂-lem₉ {.p} {._} {zero}  {p} {a} {q'} {wᵉ'} (refl , refl) prf = q' , a , wᵉ' , refl , prf , (refl , refl)
  ⊢ᵏ₂-lem₉ {q}  {._} {suc n} {p} {a} {q'} {wᵉ'} (p₁ , a₁ , u₁ , refl , prf₁ , prf₂) prf₃ = p₁ , a₁ , u₁ , refl , prf₁ , ⊢ᵏ₂-lem₉ {p₁} {u₁} {n} {p} {a} {q'} {wᵉ'} prf₂ prf₃

  open Vec-Rep-Lemmas Q? It ∀q∈It

  _⊢_─_ : DecSubset Q → Σ → Q → Set
  qs ⊢ a ─ q' = ∀ p → p ∈ᵈ qs → q' ∈ᵈ δ p a

  Dec-all-δ : ∀ qs a q' → Dec (all (λ p → p ∈ᵈ qs → q' ∈ᵈ δ p a) It)
  Dec-all-δ qs a q' = helper It
    where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (all (λ p → p ∈ᵈ qs → q' ∈ᵈ δ p a) ps)
      helper []       = yes tt
      helper (p ∷ ps) with p ∈ᵈ? qs
      helper (p ∷ ps) | true  with q' ∈ᵈ? δ p a
      helper (p ∷ ps) | true  | true  with helper ps
      helper (p ∷ ps) | true  | true  | yes  allps = yes ((λ _ → refl) , allps)
      helper (p ∷ ps) | true  | true  | no  ¬allps = no  ¬all
        where
          ¬all : ¬ ((true ≡ true → true ≡ true) × all (λ p → p ∈ᵈ qs → q' ∈ᵈ δ p a) ps)
          ¬all (_ , all) = ¬allps all
      helper (p ∷ ps) | true  | false = no ¬all
        where
          ¬all : ¬ ((true ≡ true → false ≡ true) × all (λ p → p ∈ᵈ qs → q' ∈ᵈ δ p a) ps)
          ¬all (absurd , _) = ⊥-elim (Bool-lem₁₂ (absurd refl))
      helper (p ∷ ps) | false with helper ps
      helper (p ∷ ps) | false | yes  allps = yes ((λ ()) , allps)
      helper (p ∷ ps) | false | no  ¬allps = no  ¬all
        where
          ¬all : ¬ ((false ≡ true → q' ∈ᵈ δ p a) × all (λ p → p ∈ᵈ qs → q' ∈ᵈ δ p a) ps)
          ¬all (_ , all) = ¬allps all

  Dec-⊢ : ∀ qs a q' → Dec (qs ⊢ a ─ q')
  Dec-⊢ qs a q' with Dec-all-δ qs a q'
  ... | yes prf = yes (Vec-all-lem₂ (λ p → p ∈ᵈ qs → q' ∈ᵈ δ p a) prf)
  ... | no  prf = no  (Vec-all-lem₄ (λ p → p ∈ᵈ qs → q' ∈ᵈ δ p a) prf)

  _⊢_─ˢ_ : DecSubset Q → Σ → DecSubset Q → Set
  qs ⊢ a ─ˢ ps = Σ[ p ∈ Q ] ( p ∈ᵈ ps × qs ⊢ a ─ p )

  Dec-any-⊢? : ∀ qs a ps → Dec (any (λ p → p ∈ᵈ ps × qs ⊢ a ─ p) It)
  Dec-any-⊢? qs a ps = helper It
    where
      helper : {n : ℕ}(rs : Vec Q n) → Dec (any (λ p → p ∈ᵈ ps × qs ⊢ a ─ p) rs)
      helper []       = no (λ z → z)
      helper (r ∷ rs) with r ∈ᵈ? ps
      helper (r ∷ rs) | true  with Dec-⊢ qs a r
      helper (r ∷ rs) | true  | yes prf = yes (inj₁ (refl , prf))
      helper (r ∷ rs) | true  | no  prf with helper rs
      helper (r ∷ rs) | true  | no  prf | yes  anyrs = yes (inj₂ anyrs)
      helper (r ∷ rs) | true  | no  prf | no  ¬anyrs = no ¬any
        where
          ¬any : ¬ ((true ≡ true) × qs ⊢ a ─ r ⊎ any (λ p → p ∈ᵈ ps × qs ⊢ a ─ p) rs)
          ¬any (inj₁ (refl , qs⊢a-r)) = prf qs⊢a-r
          ¬any (inj₂ any) = ¬anyrs any
      helper (r ∷ rs) | false with helper rs
      helper (r ∷ rs) | false | yes  anyrs = yes (inj₂ anyrs)
      helper (r ∷ rs) | false | no  ¬anyrs = no ¬any
        where
          ¬any : ¬ ((false ≡ true) × qs ⊢ a ─ r ⊎ any (λ p → p ∈ᵈ ps × qs ⊢ a ─ p) rs)
          ¬any (inj₁ (() , qs⊢a-r))
          ¬any (inj₂ any) = ¬anyrs any
  

  Dec-⊢? : ∀ qs a ps → Dec (qs ⊢ a ─ˢ ps)
  Dec-⊢? qs a ps with Dec-any-⊢? qs a ps
  ... | yes prf = yes (Vec-any-lem₂ (λ p → p ∈ᵈ ps × qs ⊢ a ─ p) prf)
  ... | no  prf = no  (Vec-any-lem₄ (λ p → p ∈ᵈ ps × qs ⊢ a ─ p) prf)

  _⊢_─ : DecSubset Q → Σ → Set
  qs ⊢ a ─ = Σ[ ps ∈ DecSubset Q ] qs ⊢ a ─ˢ ps
  

  _∈F : DecSubset Q → Set
  qs ∈F = ∀ p → p ∈ᵈ qs → p ∈ᵈ F

  Dec-all-∈F : ∀ qs → Dec (all (λ p → p ∈ᵈ qs → p ∈ᵈ F) It)
  Dec-all-∈F qs = helper It
    where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (all (λ p → p ∈ᵈ qs → p ∈ᵈ F) ps)
      helper []       = yes tt
      helper (p ∷ ps) with p ∈ᵈ? qs
      helper (p ∷ ps) | true  with p ∈ᵈ? F
      helper (p ∷ ps) | true  | true  with helper ps
      helper (p ∷ ps) | true  | true  | yes  allps = yes ((λ _ → refl) , allps)
      helper (p ∷ ps) | true  | true  | no  ¬allps = no  ¬all
        where
          ¬all : ¬ ((true ≡ true → true ≡ true) × all (λ p → p ∈ᵈ qs → p ∈ᵈ F) ps)
          ¬all (_ , all) = ¬allps all
      helper (p ∷ ps) | true  | false = no ¬all
        where
          ¬all : ¬ ((true ≡ true → false ≡ true) × all (λ p → p ∈ᵈ qs → p ∈ᵈ F) ps)
          ¬all (absurd , _) = ⊥-elim (Bool-lem₁₂ (absurd refl))
      helper (p ∷ ps) | false with helper ps
      helper (p ∷ ps) | false | yes  allps = yes ((λ ()) , allps)
      helper (p ∷ ps) | false | no  ¬allps = no  ¬all
        where
          ¬all : ¬ ((false ≡ true → p ∈ᵈ F) × all (λ p → p ∈ᵈ qs → p ∈ᵈ F) ps)
          ¬all (_ , all) = ¬allps all

  Dec-∈F : ∀ qs → Dec (qs ∈F)
  Dec-∈F qs with Dec-all-∈F qs
  ... | yes prf = yes (Vec-all-lem₂ (λ p → p ∈ᵈ qs → p ∈ᵈ F) prf)
  ... | no  prf = no  (Vec-all-lem₄ (λ p → p ∈ᵈ qs → p ∈ᵈ F) prf)
  
                                  
  -- transitive closure of ⊢
  infix 7 _⊢*_
  _⊢*_ : (Q × Σ*) → (Q × Σ*) → Set
  (q , w) ⊢* (q' , w') = Σ[ n ∈ ℕ ] (q , w) ⊢ᵏ n ─ (q' , w')
  
  
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
    Q     : Set
    --Q?    : DecEq Q
    δ     : Q → Σ → Q
    q₀    : Q
    F     : DecSubset Q
    --∣Q∣   : ℕ
    --It    : Vec Q ∣Q∣
    --∀q∈It : ∀ q → q ∈ⱽ It
  
module DFA-Operations (D : DFA) where
  open DFA D

  -- a move from (q , aw) to (q' , w)
  infix 7 _⊢_
  _⊢_ : (Q × Σ × Σ*) → (Q × Σ*) → Set
  (q , a , w) ⊢ (q' , w') = w ≡ w' × q' ≡ δ q a

  
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


  δ* : Q → Σ* → Q
  δ* q []      = q
  δ* q (a ∷ w) = δ* (δ q a) w
  
  δ₀ : Σ* → Q
  δ₀ w = δ* q₀ w

  δ₀-lem₅ : ∀ q w n q'
           → q' ∈ᵈ F
           → (q , w) ⊢ᵏ n ─ (q' , [])
           → δ* q w ∈ᵈ F
  δ₀-lem₅ q .[] zero   .q  q'∈F (refl , refl) = q'∈F
  δ₀-lem₅ q ._  (suc n) q' q'∈F (p , a , u , refl , (refl , prf₁) , prf₂)
    = subst (λ p → δ* p u ∈ᵈ F) prf₁ (δ₀-lem₅ p u n q' q'∈F prf₂)

  δ₀-lem₃ : ∀ w
            → Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) )
            → δ₀ w ∈ᵈ F  
  δ₀-lem₃ w (q , q∈F , n , prf) = δ₀-lem₅ q₀ w n q q∈F prf

  δ₀-lem₆ : ∀ q w
            → δ* q w ∈ᵈ F
            → Σ[ q' ∈ Q ] ( q' ∈ᵈ F × Σ[ n ∈ ℕ ] (q , w) ⊢ᵏ n ─ (q' , []) )
  δ₀-lem₆ q []      prf = q  , prf , zero , (refl , refl)
  δ₀-lem₆ q (a ∷ w) prf with δ₀-lem₆ (δ q a) w prf
  ... | q' , q'∈F , n , prf₁ = q' , q'∈F , suc n , (δ q a , a , w , refl , (refl , refl) , prf₁)

  δ₀-lem₂ : ∀ w
            → δ₀ w ∈ᵈ F
            → Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) )
  δ₀-lem₂ w prf = δ₀-lem₆ q₀ w prf

  δ₀-lem₁ : ∀ w
            → δ₀ w ∈ᵈ F ⇔ Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) )
  δ₀-lem₁ w = δ₀-lem₂ w , δ₀-lem₃ w

  δ₀-lem₄ : ∀ w
            → ¬ δ₀ w ∈ᵈ F 
            → ¬ (Σ[ q ∈ Q ] ( q ∈ᵈ F × (q₀ , w) ⊢* (q , []) ))
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
