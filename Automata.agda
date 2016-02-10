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

  infix 7 _→εᵏ₂_─_
  _→εᵏ₂_─_ : Q → ℕ → Q → Set
  q →εᵏ₂ zero ─ q'  = q →εᵏ zero ─ q'
  q →εᵏ₂ suc n ─ q' = Σ[ p ∈ Q ] ( q →εᵏ n ─ p × q' ∈ᵈ δ p E ) 

  →εᵏ-lem₁ : ∀ q n p q'
             → q →εᵏ n ─ p
             → q' ∈ᵈ δ p E
             → q →εᵏ suc n ─ q'
  →εᵏ-lem₁ q zero    .q q' refl q'∈δpE
    = q' , q'∈δpE , refl
  →εᵏ-lem₁ q (suc n)  p q' (p₁ , p∈δqE , prf) q'∈δpE
    = p₁ , p∈δqE , →εᵏ-lem₁ p₁ n p q' prf q'∈δpE

  →εᵏ-lem : ∀ q n q'
            → q →εᵏ n ─ q' ⇔ q →εᵏ₂ n ─ q'
  →εᵏ-lem q n q' = lem₁ q n q' , lem₂ q n q'
    where
      lem₁ : ∀ q n q'
             → q →εᵏ n ─ q'
             → q →εᵏ₂ n ─ q'
      lem₁ q zero       .q  refl = refl
      lem₁ q (suc zero)  q' (.q' , p∈δqE , refl) = q , refl , p∈δqE
      lem₁ q (suc (suc n)) q' (p , p∈δqE , p→q') with lem₁ p (suc n) q' p→q'
      ... | p₁ , p→p₁ , q'∈δpE = p₁ , (p , p∈δqE , p→p₁) , q'∈δpE
      lem₂ : ∀ q n q'
             → q →εᵏ₂ n ─ q'
             → q →εᵏ n ─ q'
      lem₂ q zero    .q  refl = refl
      lem₂ q (suc n)  q' (p , q→p , q'∈δpE) = →εᵏ-lem₁ q n p q' q→p q'∈δpE

  →εᵏ-lem₂ : ∀ q n p m q'
             → q →εᵏ n ─ p
             → p →εᵏ m ─ q'
             → q →εᵏ n + m ─ q'
  →εᵏ-lem₂ .p zero    p m q' refl p→q' = p→q'
  →εᵏ-lem₂  q (suc n) p m q' (p₁ , p₁∈δqE , p₁→p) p→q'
    = p₁ , p₁∈δqE , →εᵏ-lem₂ p₁ n p m q' p₁→p p→q'

  →εᵏ-lem₃ : ∀ q n m q'
             → q →εᵏ n + m ─ q'
             → Σ[ p ∈ Q ] ( q →εᵏ n ─ p × p →εᵏ m ─ q' )
  →εᵏ-lem₃ q zero    m q' prf = q , refl , prf
  →εᵏ-lem₃ q (suc n) m q' (p , p∈δqE , p→q') with →εᵏ-lem₃ p n m q' p→q'
  ... | p₁ , p→p₁ , p₁→q' = p₁ , (p , p∈δqE , p→p₁) , p₁→q'
      

  open Vec-Rep Q? It ∀q∈It unique

  Dec-any-⋃-δqE : ∀ qs q' → Dec (any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q E) It)
  Dec-any-⋃-δqE qs q' = helper It
    where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q E) ps)
      helper []       = no (λ z → z)
      helper (p ∷ ps) with p ∈ᵈ? qs | q' ∈ᵈ? δ p E
      helper (p ∷ ps) | true  | true  = yes (inj₁ (refl , refl))
      helper (p ∷ ps) | true  | false with helper ps
      helper (p ∷ ps) | true  | false | yes prf₂ = yes (inj₂ prf₂)
      helper (p ∷ ps) | true  | false | no  prf₂ = no ¬any
        where
          ¬any : ¬ (true ≡ true × (false ≡ true) ⊎ any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q E) ps)
          ¬any (inj₁ (_ , ()))
          ¬any (inj₂ any) = prf₂ any
      helper (p ∷ ps) | false | q'∈?δqE with helper ps
      helper (p ∷ ps) | false | q'∈?δqE | yes prf = yes (inj₂ prf)
      helper (p ∷ ps) | false | q'∈?δqE | no  prf = no ¬any
        where
          ¬any : ¬ (false ≡ true × q'∈?δqE ≡ true ⊎ any (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q E) ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ prf₁) = prf prf₁

  Dec-⋃-δqE : ∀ qs q' → Dec (Σ[ q ∈ Q ] ( q ∈ᵈ qs × q' ∈ᵈ δ q E ))
  Dec-⋃-δqE qs q' with Dec-any-⋃-δqE qs q'
  Dec-⋃-δqE qs q' | yes prf = yes (Vec-any-lem₂ (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q E) prf)
  Dec-⋃-δqE qs q' | no  prf = no  (Vec-any-lem₄ (λ q → q ∈ᵈ qs × q' ∈ᵈ δ q E) prf)
  
  ⋃-δqE : DecSubset Q → DecSubset Q
  ⋃-δqE qs q' with Dec-⋃-δqE qs q'
  ... | yes _ = true
  ... | no  _ = false

  ε-path : Q → ℕ → DecSubset Q
  ε-path q zero    = ⟦ q ⟧ᵈ {{Q?}}
  ε-path q (suc n) = ε-path q n ⋃ᵈ ⋃-δqE (ε-path q n)

  ε-closure : Q → Subset Q
  ε-closure q = λ q' → Σ[ n ∈ ℕ ] ( q' ∈ᵈ ε-path q n )

  ε-closureᵏ : ℕ → Q → Subset Q
  ε-closureᵏ k q = λ q' → Σ[ n ∈ ℕ ] ( n ≤ k × q' ∈ᵈ ε-path q n )

  ε-lem₂ : ∀ q s j → s ∈ᵈ ε-path q j → q →εᵏ j ─ s
  ε-lem₂ q  s zero    s∈q0  with Q? q s
  ε-lem₂ q .q zero    s∈q0  | yes refl = refl
  ε-lem₂ q  s zero      ()  | no  _
  ε-lem₂ q  s (suc j) s∈qsj with s ∈ᵈ? ε-path q j | inspect (ε-path q j) s
  ε-lem₂ q  s (suc j) s∈qsj | true  | [ s∈qj ] = q , ∀qEq q , ε-lem₂ q s j s∈qj
  ε-lem₂ q  s (suc j) s∈qsj | false | [ s∉qj ] with Dec-⋃-δqE (ε-path q j) s
  ε-lem₂ q  s (suc j) s∈qsj | false | [ s∉qj ] | yes (p , p∈q , s∈δpE)
    = →εᵏ-lem₁ q j p s (ε-lem₂ q p j p∈q) s∈δpE
  ε-lem₂ q  s (suc j)    () | false | [ s∉qj ] | no  _
  

  ε-lem₁ : ∀ q s j → q →εᵏ j ─ s → s ∈ᵈ ε-path q j
  ε-lem₁ q .q zero    refl = ⟦a⟧-lem₁ Q? q
  ε-lem₁ q  s (suc j) prf with proj₁ (→εᵏ-lem q (suc j) s) prf
  ε-lem₁ q  s (suc j) prf | p , q→p , s∈δpE with s ∈ᵈ? ε-path q j
  ε-lem₁ q  s (suc j) prf | p , q→p , s∈δpE | true  = refl
  ε-lem₁ q  s (suc j) prf | p , q→p , s∈δpE | false with Dec-⋃-δqE (ε-path q j) s
  ε-lem₁ q  s (suc j) prf | p , q→p , s∈δpE | false | yes (p₁ , p∈q , s∈δqE) = refl
  ε-lem₁ q  s (suc j) prf | p , q→p , s∈δpE | false | no  ¬∃q with ε-lem₁ q p j q→p
  ε-lem₁ q  s (suc j) prf | p , q→p , s∈δpE | false | no  ¬∃q | p∈qj = ⊥-elim (¬∃q (p , p∈qj , s∈δpE))

  ε-path-lem₁ : ∀ q k → k ≡ zero → ε-path q k ≈ᵈ (⟦ q ⟧ᵈ {{Q?}})
  ε-path-lem₁ q .zero refl = ≈-refl
  
  size-helper : {n : ℕ} → (ps : Vec Q (suc n)) → Unique ps → DecSubset Q → ℕ
  size-helper (p ∷ [])     tt  qs with p ∈ᵈ? qs
  ... | true  = 1
  ... | false = 0
  size-helper (p ∷ x ∷ ps) (proj₁ , proj₂) qs with p ∈ᵈ? qs
  ... | true  = suc (size-helper (x ∷ ps) proj₂ qs)
  ... | false = size-helper (x ∷ ps) proj₂ qs

  size : DecSubset Q → ℕ
  size qs = size-helper It unique qs

  module Claim3 (q : Q) where
    ε3-lem₂ : ∀ j k → j ≥ k → j ≥ suc k → ∀ s → s ∈ᵈ ε-path q j → q →εᵏ j ─ s
    ε3-lem₂ j k j≥k j≥sk s s∈q = ε-lem₂ q s j s∈q
    
    ε3-lem₃ : ∀ r k → q →εᵏ suc k ─ r → r ∈ᵈ ε-path q (suc k)
    ε3-lem₃ r k q→k = ε-lem₁ q r (suc k) q→k

    ε3-lem₄ : ∀ r k → ε-path q k ≈ᵈ ε-path q (suc k) → q →εᵏ suc k ─ r → r ∈ᵈ ε-path q k
    ε3-lem₄ r k k≈suck q→k = proj₂ k≈suck r (ε3-lem₃ r k q→k)

    ε3-lem₅ : ∀ j n k → ε-path q k ≈ᵈ ε-path q (suc k) → j ∸ suc k ≡ n → j ≥ k → j ≥ suc k → ∀ r s → q →εᵏ suc k ─ r → r →εᵏ n ─ s → s ∈ᵈ ε-path q (j ∸ 1)
    ε3-lem₅ zero    n  k k≈suck prf  j≥k () r s q→r r→s
    ε3-lem₅ (suc j) ._ k k≈suck refl sj≥k (s≤s j≥k) r s q→r r→s
      = let q→kr = ε-lem₂ q r k (ε3-lem₄ r k k≈suck q→r) in
        subst (λ n → s ∈ᵈ ε-path q n) (ℕ-lem₅ j k j≥k) (ε-lem₁ q s (k + (j ∸ k)) (→εᵏ-lem₂ q k r (j ∸ k) s q→kr r→s))


    ε3-lem₆ : ∀ j n k → ε-path q k ≈ᵈ ε-path q (suc k) → j ∸ suc k ≡ n → j ≥ k → j ≥ suc k → ∀ s → s ∈ᵈ ε-path q j → s ∈ᵈ ε-path q (j ∸ 1)
    ε3-lem₆ zero n k k≈suck prf j≥k () s s∈qj
    ε3-lem₆ (suc j) n k k≈suck prf sj≥k (s≤s j≥k) s s∈qj with →εᵏ-lem₃ q (suc k) n s (subst (λ n → q →εᵏ n ─ s) (cong suc (ℕ-lem₆ j k n j≥k prf)) (ε-lem₂ q s (suc j) s∈qj))
    ... | r , q→r , r→s = ε3-lem₅ (suc j) n k k≈suck prf sj≥k (s≤s j≥k) r s q→r r→s
    

    ε3-lem₇ : ∀ j n k → ε-path q k ≈ᵈ ε-path q (suc k) → j ∸ suc k ≡ n → j ≥ k → j ≥ suc k → ε-path q j ≈ᵈ ε-path q (j ∸ 1)
    ε3-lem₇ j n k k≈suck prf j≥k j≥sk = lem₁ , lem₂ j j≥sk
      where
        lem₁ : ε-path q j ⊆ᵈ ε-path q (j ∸ 1)
        lem₁ = ε3-lem₆ j n k k≈suck prf j≥k j≥sk
        lem₂ : ∀ j → j ≥ suc k → ε-path q j ⊇ᵈ ε-path q (j ∸ 1)
        lem₂ zero () s s∈sq-1
        lem₂ (suc j) j≥sk s s∈sq-1 = Bool-lem₆ _ _ s∈sq-1 --inj₁ s∈sq-1

    ε3-lem₈ : ∀ j n k → j ∸ k ≡ n → j ≥ k → ε-path q k ≈ᵈ ε-path q (suc k) → ε-path q k ≈ᵈ ε-path q j
    ε3-lem₈  j zero   k prf j≥k k≈sk with ℕ-lem₇ j k j≥k prf
    ε3-lem₈ .k zero   k prf j≥k k≈sk | refl = ≈-refl
    ε3-lem₈ zero    (suc n) k prf j≥k k≈sk = ε-path-lem₁ q k (ℕ-lem₃ k j≥k)
    ε3-lem₈ (suc j) (suc .j) zero    refl z≤n k≈sk = ≈-trans IH (≈-sym lem7)
      where
        IH : (⟦ q ⟧ᵈ {{Q?}}) ≈ᵈ ε-path q j
        IH = ε3-lem₈ j j zero refl z≤n k≈sk
        lem7 : ε-path q j ⋃ᵈ ⋃-δqE (ε-path q j) ≈ᵈ ε-path q j
        lem7 = ε3-lem₇ (suc j) j zero k≈sk refl z≤n (s≤s z≤n)
    ε3-lem₈ (suc j) (suc n) (suc k) prf (s≤s j≥k) k≈sk
      = ≈-trans IH (≈-sym lem7)
      where
        IH : ε-path q k ⋃ᵈ ⋃-δqE (ε-path q k) ≈ᵈ ε-path q j
        IH = ε3-lem₈ j n (suc k) (ℕ-lem₉ j k n j≥k prf) (ℕ-lem₈ j k n j≥k prf) k≈sk
        lem7 : ε-path q j ⋃ᵈ ⋃-δqE (ε-path q j) ≈ᵈ ε-path q j
        lem7 = ε3-lem₇ (suc j) n (suc k) k≈sk (ℕ-lem₉ j k n j≥k prf) (s≤s j≥k) (s≤s (ℕ-lem₈ j k n j≥k prf))


    ε3-lem₁ : ∀ j k → ε-path q k ≈ᵈ ε-path q (suc k) → j ≥ k → ε-path q k ≈ᵈ ε-path q j
    ε3-lem₁ j k k≈suck j≥k = ε3-lem₈ j (j ∸ k) k refl j≥k k≈suck

    ε3-lem₉ : ∀ j → ε-path q j ⊆ᵈ ε-path q (suc j)
    ε3-lem₉ j s s∈qj = Bool-lem₆ _ _ s∈qj

    ε3-lem₁₀ : ∀ j k → j ≤ k → ε-path q j ⊆ᵈ ε-path q k
    ε3-lem₁₀ j zero     j≤k s s∈qj with ℕ-lem₃ j j≤k
    ε3-lem₁₀ .zero zero j≤k s s∈qj | refl = s∈qj
    ε3-lem₁₀ zero (suc k) j≤k s s∈qj = Bool-lem₆ _ _ (ε3-lem₁₀ zero k z≤n s s∈qj)
    ε3-lem₁₀ (suc j) (suc k) (s≤s j≤k) s s∈jsq with s ∈ᵈ? ε-path q j | inspect (ε-path q j) s
    ε3-lem₁₀ (suc j) (suc k) (s≤s j≤k) s s∈jsq | true  | [ s∈qj ] = Bool-lem₆ _ _ (ε3-lem₁₀ j k j≤k s s∈qj)
    ε3-lem₁₀ (suc j) (suc k) (s≤s j≤k) s s∈jsq | false | [ s∉qj ] with Dec-⋃-δqE (ε-path q j) s
    ε3-lem₁₀ (suc j) (suc k) (s≤s j≤k) s s∈jsq | false | [ s∉qj ] | yes (p , p∈q , s∈δqE) with Dec-⋃-δqE (ε-path q k) s
    ε3-lem₁₀ (suc j) (suc k) (s≤s j≤k) s s∈jsq | false | [ s∉qj ] | yes (p , p∈q , s∈δqE) | yes _   = Bool-lem₁₀ true (s ∈ᵈ? ε-path q k) refl 
    ε3-lem₁₀ (suc j) (suc k) (s≤s j≤k) s s∈jsq | false | [ s∉qj ] | yes (p , p∈q , s∈δqE) | no  ¬∃q = ⊥-elim (¬∃q (p , ε3-lem₁₀ j k j≤k p p∈q , s∈δqE))
    ε3-lem₁₀ (suc j) (suc k) (s≤s j≤k) s    () | false | [ s∉qj ] | no  _


    ε-clos-lem₁ : ∀ k → ε-path q k ≈ᵈ ε-path q (suc k) → ε-closure q ≈ ε-closureᵏ k q
    ε-clos-lem₁ k prf = lem₁ k prf , lem₂ k prf
      where
        lem₁ : ∀ k → ε-path q k ≈ᵈ ε-path q (suc k) → ε-closure q ⊆ ε-closureᵏ k q
        lem₁ k εqk≈εqsk s (n , s∈qn) with n ≤? k
        lem₁ k εqk≈εqsk s (n , s∈qn) | yes n≤k = n , n≤k , s∈qn
        lem₁ k εqk≈εqsk s (n , s∈qn) | no  n≥k = k , ℕ-lem₁₀ k , proj₂ (ε3-lem₁ n k εqk≈εqsk (ℕ-lem₁₄ n k (ℕ-lem₁₃ n k n≥k))) s s∈qn
        lem₂ : ∀ k → ε-path q k ≈ᵈ ε-path q (suc k) → ε-closure q ⊇ ε-closureᵏ k q
        lem₂ k εqk≈εqsk s (n , n≤k , s∈qn) = n , s∈qn


    -- Claim 4
    ε4-lem₄ : ∀ qs → qs ≈ᵈ ø → size qs ≡ 0
    ε4-lem₄ qs qs≈ø = helper It unique
      where
        helper : {n : ℕ} → (ps : Vec Q (suc n)) → (uni : Unique ps) → size-helper ps uni qs ≡ 0
        helper (p ∷ [])     uni with p ∈ᵈ? qs | inspect qs p
        ... | true  | [ p∈qs ] = ⊥-elim (Bool-lem₉ refl (proj₁ qs≈ø p p∈qs))
        ... | false | [ p∉qs ] = refl
        helper (p ∷ x ∷ ps) uni with p ∈ᵈ? qs | inspect qs p
        ... | true  | [ p∈qs ] = ⊥-elim (Bool-lem₉ refl (proj₁ qs≈ø p p∈qs))
        ... | false | [ p∉qs ] = helper (x ∷ ps) (proj₂ uni)

    ε4-lem₃ : ∀ qs → Σ[ q ∈ Q ] q ∈ᵈ qs → size qs > 0
    ε4-lem₃ qs (q , q∈qs) = helper It unique (∀q∈It q) q∈qs
      where
        helper : {n : ℕ} → (ps : Vec Q (suc n)) → (uni : Unique ps) → q ∈ⱽ ps → q ∈ᵈ qs → size-helper ps uni qs > 0
        helper ( x ∷ [])      uni q∈ps q∈qs with It-lem₇ (x ∷ []) q q∈ps
        helper (.q ∷ [])      uni q∈ps q∈qs | inj₁ refl with q ∈ᵈ? qs
        helper (.q ∷ [])      uni q∈ps q∈qs | inj₁ refl | true  = s≤s z≤n
        helper (.q ∷ [])      uni q∈ps   () | inj₁ refl | false
        helper ( x ∷ [])      uni q∈ps q∈qs | inj₂ ()
        helper ( x ∷ x₁ ∷ ps) uni q∈ps q∈qs with It-lem₇ (x ∷ x₁ ∷ ps) q q∈ps
        helper (.q ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₁ refl  with q ∈ᵈ? qs
        helper (.q ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₁ refl  | true = s≤s z≤n
        helper (.q ∷ x₁ ∷ ps) uni q∈ps   () | inj₁ refl  | false
        helper ( x ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₂ q∈xps with x ∈ᵈ? qs
        helper ( x ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₂ q∈xps | true  = ℕ-lem₁₁ (size-helper (x₁ ∷ ps) (proj₂ uni) qs)
        helper ( x ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₂ q∈xps | false = helper (x₁ ∷ ps) (proj₂ uni) q∈xps q∈qs
        

    ε4-lem₂ : size (ε-path q 0) ≡ 1
    ε4-lem₂ = helper₂ It unique (∀q∈It q) (⟦a⟧-lem₁ Q? q)
      where
        helper₁ : {n : ℕ}(ps : Vec Q (suc n))(uni : Unique ps)
                  → ¬ q ∈ⱽ ps
                  → q ∈ᵈ (ε-path q 0)
                  → size-helper ps uni (ε-path q 0) ≡ 0
        helper₁ ( x ∷ [])      uni q∉ps q∈qs with x ∈ᵈ? (ε-path q 0) | inspect (ε-path q 0) x
        helper₁ ( x ∷ [])      uni q∉ps q∈qs | true  | [ x∈qs ] with Q? q x
        helper₁ (.q ∷ [])      uni q∉ps q∈qs | true  | [ x∈qs ] | yes refl = ⊥-elim (q∉ps here)
        helper₁ ( x ∷ [])      uni q∉ps q∈qs | true  | [   () ] | no  _
        helper₁ ( x ∷ [])      uni q∉ps q∈qs | false | [ x∈qs ] = refl
        helper₁ ( x ∷ x₁ ∷ ps) uni q∉ps q∈qs with x ∈ᵈ? (ε-path q 0) | inspect (ε-path q 0) x
        helper₁ ( x ∷ x₁ ∷ ps) uni q∉ps q∈qs | true  | [ x∈qs ] with Q? q x
        helper₁ (.q ∷ x₁ ∷ ps) uni q∉ps q∈qs | true  | [ x∈qs ] | yes refl = ⊥-elim (q∉ps here)
        helper₁ ( x ∷ x₁ ∷ ps) uni q∉ps q∈qs | true  | [   () ] | no  _
        helper₁ ( x ∷ x₁ ∷ ps) uni q∉ps q∈qs | false | [ x∈qs ] = helper₁ (x₁ ∷ ps) (proj₂ uni) (It-lem₈ q∉ps) q∈qs
        
        helper₂ : {n : ℕ}(ps : Vec Q (suc n))(uni : Unique ps)
                 → q ∈ⱽ ps
                 → q ∈ᵈ (ε-path q 0)
                 → size-helper ps uni (ε-path q 0) ≡ 1
        helper₂ ( x ∷ [])      uni q∈ps q∈qs with It-lem₇ (x ∷ []) q q∈ps
        helper₂ (.q ∷ [])      uni q∈ps q∈qs | inj₁ refl with q ∈ᵈ? (ε-path q 0)
        helper₂ (.q ∷ [])      uni q∈ps q∈qs | inj₁ refl | true  = refl
        helper₂ (.q ∷ [])      uni q∈ps   () | inj₁ refl | false
        helper₂ ( x ∷ [])      uni q∈ps q∈qs | inj₂ ()
        helper₂ ( x ∷ x₁ ∷ ps) uni q∈ps q∈qs with It-lem₇ (x ∷ x₁ ∷ ps) q q∈ps
        helper₂ (.q ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₁ refl  with q ∈ᵈ? (ε-path q 0)
        helper₂ (.q ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₁ refl  | true
          = let q∉ps = It-lem₅ (q ∷ x₁ ∷ ps) uni q q∈ps refl in
            let other = helper₁ (x₁ ∷ ps) (proj₂ uni) q∉ps (⟦a⟧-lem₁ Q? q) in
            cong suc other
        helper₂ (.q ∷ x₁ ∷ ps) uni q∈ps   () | inj₁ refl  | false
        helper₂ ( x ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₂ q∈xps with x ∈ᵈ? (ε-path q 0) | inspect (ε-path q 0) x
        helper₂ ( x ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₂ q∈xps | true  | [ x∈qs ] with Q? q x
        helper₂ (.q ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₂ q∈xps | true  | [ x∈qs ] | yes refl
          = let q∉ps = It-lem₅ (q ∷ x₁ ∷ ps) uni q q∈ps refl in
            let other = helper₁ (x₁ ∷ ps) (proj₂ uni) q∉ps (⟦a⟧-lem₁ Q? q) in
            cong suc other
        helper₂ ( x ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₂ q∈xps | true  | [   () ] | no  _
        helper₂ ( x ∷ x₁ ∷ ps) uni q∈ps q∈qs | inj₂ q∈xps | false | [ x∈qs ] = helper₂ (x₁ ∷ ps) (proj₂ uni) q∈xps q∈qs
  

    ε4-lem₅ : ∀ j → ¬ (ε-path q (suc j) ≈ᵈ ε-path q j) → ¬ ε-path q (suc j) ⊆ᵈ ε-path q j
    ε4-lem₅ j ¬j≈j-1 j⊆j-1 with ε3-lem₉ j
    ... | j⊇j-1 = ⊥-elim (¬j≈j-1 (j⊆j-1 , j⊇j-1))


    ε4-lem₉ : ∀ j → q ∈ᵈ ε-path q j
    ε4-lem₉ zero    = ⟦a⟧-lem₁ Q? q
    ε4-lem₉ (suc j) = Bool-lem₆ _ _ (ε4-lem₉ j)

    -- NOT constructive
    ε4-lem₆ : ∀ j → ¬ ε-path q (suc j) ⊆ᵈ ε-path q j → Σ[ p ∈ Q ] ( p ∈ᵈ ε-path q (suc j) × p ∉ᵈ ε-path q j )
    ε4-lem₆ j ¬⊆ with ¬∀≡∃¬ ¬⊆
    ε4-lem₆ j ¬⊆ | p , prf with p ∈ᵈ? ε-path q j | inspect (ε-path q j) p
    ε4-lem₆ j ¬⊆ | p , prf | true  | [ p∈qj ] = ⊥-elim (prf (λ _ → refl))
    ε4-lem₆ j ¬⊆ | p , prf | false | [ p∉qj ] with p ∈ᵈ? ⋃-δqE (ε-path q j) | inspect (⋃-δqE (ε-path q j)) p
    ε4-lem₆ j ¬⊆ | p , prf | false | [ p∉qj ] | true  | [ p∈⋃qj ]
      = p , Bool-lem₁₀ (p ∈ᵈ? ⋃-δqE (ε-path q j)) (p ∈ᵈ? ε-path q j) p∈⋃qj , Subset.DecidableSubset.∈-lem₂ {Q} {p} {ε-path q j} p∉qj
    ε4-lem₆ j ¬⊆ | p , prf | false | [ p∉qj ] | false | [ p∉⋃qj ]
      = ⊥-elim (prf (λ z → z))

    ε4-lem₁₁ : ∀ j → {n : ℕ}(ps : Vec Q (suc n))(uni : Unique ps)
              → size-helper ps uni (ε-path q (suc j)) ≥ size-helper ps uni (ε-path q j)
    ε4-lem₁₁ j (p ∷ []) uni with p ∈ᵈ? ⋃-δqE (ε-path q j) | p ∈ᵈ? (ε-path q j)
    ε4-lem₁₁ j (p ∷ []) uni | true  | true  = s≤s z≤n
    ε4-lem₁₁ j (p ∷ []) uni | true  | false = z≤n
    ε4-lem₁₁ j (p ∷ []) uni | false | true  = s≤s z≤n
    ε4-lem₁₁ j (p ∷ []) uni | false | false = z≤n
    ε4-lem₁₁ j (p ∷ x ∷ ps) uni with p ∈ᵈ? ⋃-δqE (ε-path q j) | p ∈ᵈ? (ε-path q j)
    ε4-lem₁₁ j (p ∷ x ∷ ps) uni | true  | true  = s≤s (ε4-lem₁₁ j (x ∷ ps) (proj₂ uni))
    ε4-lem₁₁ j (p ∷ x ∷ ps) uni | true  | false = ℕ-lem₁₅ (ε4-lem₁₁ j (x ∷ ps) (proj₂ uni))
    ε4-lem₁₁ j (p ∷ x ∷ ps) uni | false | true  = s≤s (ε4-lem₁₁ j (x ∷ ps) (proj₂ uni))
    ε4-lem₁₁ j (p ∷ x ∷ ps) uni | false | false = ε4-lem₁₁ j (x ∷ ps) (proj₂ uni)

    ε4-lem₁₀ : ∀ j → {n : ℕ}(ps : Vec Q (suc n))(uni : Unique ps)
              → ∀ p → p ∈ᵈ ε-path q (suc j) → p ∉ᵈ ε-path q j → p ∈ⱽ ps
              → size-helper ps uni (ε-path q (suc j)) > size-helper ps uni (ε-path q j)
    ε4-lem₁₀ j ( p ∷ [])     uni r r∈qsj r∈qj r∈ps with It-lem₇ (p ∷ []) r r∈ps
    ε4-lem₁₀ j (.r ∷ []) uni r r∈qsj r∈qj r∈ps | inj₁ refl with r ∈ᵈ? ⋃-δqE (ε-path q j) | r ∈ᵈ? (ε-path q j)
    ε4-lem₁₀ j (.r ∷ []) uni r r∈qsj r∈qj r∈ps | inj₁ refl | true  | true  = ⊥-elim (r∈qj refl)
    ε4-lem₁₀ j (.r ∷ []) uni r r∈qsj r∈qj r∈ps | inj₁ refl | true  | false = s≤s z≤n
    ε4-lem₁₀ j (.r ∷ []) uni r r∈qsj r∈qj r∈ps | inj₁ refl | false | true  = ⊥-elim (r∈qj refl)
    ε4-lem₁₀ j (.r ∷ []) uni r    () r∈qj r∈ps | inj₁ refl | false | false 
    ε4-lem₁₀ j ( p ∷ []) uni r r∈qsj r∈qj r∈ps | inj₂ ()
    ε4-lem₁₀ j ( p ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps with It-lem₇ (p ∷ x ∷ ps) r r∈ps
    ε4-lem₁₀ j (.r ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps | inj₁ refl with r ∈ᵈ? ⋃-δqE (ε-path q j) | r ∈ᵈ? (ε-path q j)
    ε4-lem₁₀ j (.r ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps | inj₁ refl | true  | true
      = ⊥-elim (r∈qj refl)
    ε4-lem₁₀ j (.r ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps | inj₁ refl | true  | false
      = let IH = ε4-lem₁₁ j (x ∷ ps) (proj₂ uni) in ℕ-lem₁₆ IH
    ε4-lem₁₀ j (.r ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps | inj₁ refl | false | true
      = ⊥-elim (r∈qj refl)
    ε4-lem₁₀ j (.r ∷ x ∷ ps) uni r    () r∈qj r∈ps | inj₁ refl | false | false
    ε4-lem₁₀ j ( p ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps | inj₂ r∈xps with p ∈ᵈ? ⋃-δqE (ε-path q j) | p ∈ᵈ? (ε-path q j)
    ε4-lem₁₀ j ( p ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps | inj₂ r∈xps | true  | true 
      = s≤s (ε4-lem₁₀ j (x ∷ ps) (proj₂ uni) r r∈qsj r∈qj r∈xps)
    ε4-lem₁₀ j ( p ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps | inj₂ r∈xps | true  | false 
      = let IH = (ε4-lem₁₀ j (x ∷ ps) (proj₂ uni) r r∈qsj r∈qj r∈xps) in ℕ-lem₁₅ IH
    ε4-lem₁₀ j ( p ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps | inj₂ r∈xps | false | true  
      = s≤s (ε4-lem₁₀ j (x ∷ ps) (proj₂ uni) r r∈qsj r∈qj r∈xps)
    ε4-lem₁₀ j ( p ∷ x ∷ ps) uni r r∈qsj r∈qj r∈ps | inj₂ r∈xps | false | false 
      = ε4-lem₁₀ j (x ∷ ps) (proj₂ uni) r r∈qsj r∈qj r∈xps

    ε4-lem₁₃ : ∀ i → (suc (suc i)) ≥ 1
               → ∀ p → p ∈ᵈ ε-path q (suc (suc i)) → ¬ p ∈ᵈ ε-path q (suc i)
               → ¬ (ε-path q (suc (suc i)) ≈ᵈ ε-path q (suc i))
               → ¬ (ε-path q (suc i) ≈ᵈ ε-path q i)
    ε4-lem₁₃ i ssi≥1 p p∈ssi p∉si ¬i+2≈i+1 i+1≈i with p ∈ᵈ? (ε-path q (suc i)) | inspect (ε-path q (suc i)) p | Dec-⋃-δqE (ε-path q i ⋃ᵈ ⋃-δqE (ε-path q i)) p
    ε4-lem₁₃ i ssi≥1 p p∈ssi p∉si ¬i+2≈i+1 i+1≈i | true  | [ p∈qsi ] | _  = ⊥-elim (p∉si refl)
    ε4-lem₁₃ i ssi≥1 p p∈ssi p∉si ¬i+2≈i+1 i+1≈i | false | [ p∉qsi ] | yes (p₁ , p₁∈si , p∈δp₁E) with Dec-⋃-δqE (ε-path q i) p
    ε4-lem₁₃ i ssi≥1 p p∈ssi p∉si ¬i+2≈i+1 i+1≈i | false | [ p∉qsi ] | yes (p₁ , p₁∈si , p∈δp₁E) | yes (p₂ , p₂∈i , p∈δp₂E)
      = ⊥-elim (Bool-lem₂ (subst (λ r → r ≡ false) (Bool-lem₁ (ε-path q i p)) p∉qsi))
    ε4-lem₁₃ i ssi≥1 p p∈ssi p∉si ¬i+2≈i+1 i+1≈i | false | [ p∉qsi ] | yes (p₁ , p₁∈si , p∈δp₁E) | no ¬∃p
      = let p₁∈i = proj₁ i+1≈i p₁ p₁∈si in ⊥-elim (¬∃p (p₁ , p₁∈i , p∈δp₁E))
    ε4-lem₁₃ i ssi≥1 p    () p∉si ¬i+2≈i+1 i+1≈i | false | [ p∉qsi ] | no  _

    
    ε4-lem₁ : ∀ i → i ≥ 1 → ¬ (ε-path q i ≈ᵈ ε-path q (i ∸ 1)) → size (ε-path q i) ≥ suc i
    ε4-lem₁ zero          ()        ¬i≈i-1 
    ε4-lem₁ (suc zero)    (s≤s z≤n) ¬i≈i-1
      = let ¬⊆ = ε4-lem₅ 0 ¬i≈i-1 in
        let p , (p∈qsj , p∉qj) = ε4-lem₆ 0 ¬⊆ in
        let prf = ε4-lem₁₀ 0 It unique p p∈qsj p∉qj (∀q∈It p) in
        subst (λ n → suc n ≤ size (ε-path q (suc zero))) ε4-lem₂ prf
    ε4-lem₁ (suc (suc i)) i≥1 ¬i≈i-1
      = let ¬⊆ = ε4-lem₅ (suc i) ¬i≈i-1 in
        let p , (p∈qsj , p∉qj) = ε4-lem₆ (suc i) ¬⊆ in
        let prf = ε4-lem₁₀ (suc i) It unique p p∈qsj p∉qj (∀q∈It p) in
        let IH = ε4-lem₁ (suc i) (s≤s z≤n) (ε4-lem₁₃ i i≥1 p p∈qsj p∉qj ¬i≈i-1) in ℕ-lem₁₇ IH prf
        

    ε4-lem₁₂ : ∀ j → size (ε-path q j) ≤ suc ∣Q∣-1
    ε4-lem₁₂ j = helper It unique
      where
        helper : {n : ℕ}(ps : Vec Q (suc n))(uni : Unique ps)
                 → size-helper ps uni (ε-path q j) ≤ suc n
        helper (p ∷ []) uni with p ∈ᵈ? ε-path q j
        helper (p ∷ []) uni | true  = s≤s z≤n
        helper (p ∷ []) uni | false = z≤n
        helper (p ∷ x ∷ ps) uni with p ∈ᵈ? ε-path q j
        helper (p ∷ x ∷ ps) uni | true  = s≤s (helper (x ∷ ps) (proj₂ uni))
        helper (p ∷ x ∷ ps) uni | false = ℕ-lem₁₅ (helper (x ∷ ps) (proj₂ uni))


    open DSub-VSub Q? It ∀q∈It unique

    ε-clos-lem₃ : ε-path q ∣Q∣-1 ≈ᵈ (ε-path q (suc ∣Q∣-1)) -- ≥ suc suc ∣Q∣-1
    ε-clos-lem₃ with Dec-≈ (ε-path q (suc ∣Q∣-1)) (ε-path q ∣Q∣-1)
    ... | yes prf = ≈-sym prf
    ... | no  prf = let prf₁ = ε4-lem₁ (suc ∣Q∣-1) (s≤s z≤n) prf in
                    ⊥-elim (ℕ-lem₁₈ (ε4-lem₁₂ (suc ∣Q∣-1)) prf₁)

    ε-clos-lem₂ : ∀ q' → q' ∈ ε-closure q ⇔ q' ∈ᵈ ε-path q ∣Q∣-1
    ε-clos-lem₂ q' = lem₁ , lem₂
      where
        lem₁ : q' ∈ ε-closure q → q' ∈ᵈ ε-path q ∣Q∣-1
        lem₁ (n , q'∈qn) = let εq≈εqᵏ = ε-clos-lem₁ ∣Q∣-1 ε-clos-lem₃ in
                           let (n₁ , n₁≤∣Q∣-1 , q'∈ᵈqn₁) = proj₁ εq≈εqᵏ q' (n , q'∈qn) in
                           let εn₁⊆ε∣Q∣-1 = ε3-lem₁₀ n₁ ∣Q∣-1 n₁≤∣Q∣-1 in
                           εn₁⊆ε∣Q∣-1 q' q'∈ᵈqn₁
        lem₂ : q' ∈ᵈ ε-path q ∣Q∣-1 → q' ∈ ε-closure q
        lem₂ prf = ∣Q∣-1 , prf

    ε-clos-lem₄ : ∀ q' → q' ∉ᵈ ε-path q ∣Q∣-1 → q' ∉ ε-closure q
    ε-clos-lem₄ q' q'∉ε q'∈ε = q'∉ε (proj₁ (ε-clos-lem₂ q') q'∈ε)


  Dec-ε-closure : ∀ q q' → Dec (q' ∈ ε-closure q)
  Dec-ε-closure q q' with q' ∈ᵈ? ε-path q ∣Q∣-1 | inspect (λ q' → q' ∈ᵈ? ε-path q ∣Q∣-1) q'
  Dec-ε-closure q q' | true  | [ q'∈ε ] = yes (proj₂ (Claim3.ε-clos-lem₂ q q') q'∈ε)
  Dec-ε-closure q q' | false | [ q'∉ε ] = no  ((Claim3.ε-clos-lem₄ q q') (Subset.DecidableSubset.∈-lem₂ {Q} {q'} {ε-path q ∣Q∣-1} q'∉ε))
  

  →ε*-lem₁ : ∀ q q' → q →ε* q' ⇔ q' ∈ ε-closure q
  →ε*-lem₁ q q' = lem₁ , lem₂
    where
      lem₁ : q →ε* q' → q' ∈ ε-closure q
      lem₁ (n , prf) = n , ε-lem₁ q q' n prf
      lem₂ : q' ∈ ε-closure q → q →ε* q'
      lem₂ (n , prf) = n , ε-lem₂ q q' n prf

  →ε*-lem₂ : ∀ q q' → q' ∉ ε-closure q → ¬ q →ε* q'
  →ε*-lem₂ q q' q'∉ε q→q' = q'∉ε (proj₁ (→ε*-lem₁ q q') q→q')
  
  Dec-→ε* : ∀ q q' → Dec (q →ε* q')
  Dec-→ε* q q' with Dec-ε-closure q q'
  ... | yes prf = yes (proj₂ (→ε*-lem₁ q q') prf)
  ... | no  prf = no  (→ε*-lem₂ q q' prf)

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
