{-
  Here the Automata and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 2.2: Regular sets, their generators, and their recognizers
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung
  Version 15-03-2016
-}
open import Util
module DFA (Σ : Set)(dec : DecEq Σ) where

open import Data.List hiding (any ; all) 
open import Data.Bool
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset
  renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; Ø to Øᵈ ; _⋃_ to _⋃ᵈ_ ; _⋂_ to _⋂ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ
                 ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv ; ≈-refl to ≈ᵈ-refl ; ≈-trans to ≈ᵈ-trans ; ≈-sym to ≈ᵈ-sym)
open import Quotient
open import Data.Vec hiding (_++_) renaming (_∈_ to _∈ⱽ_ ; tail to tailⱽ)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import Language Σ dec


-- Deterministic finite automata
-- section 2.2.3: Finite Automata
record DFA : Set₁ where
  field
    Q  : Set
    δ  : Q → Σ → Q
    q₀ : Q
    F  : DecSubset Q
    _≋_ : (q q' : Q) → Set
    ≋-isEquiv : IsEquivalence _≋_
    δ-lem   : ∀ {q} {p} a → q ≋ p → δ q a ≋ δ p a
    F-lem   : ∀ {q} {p}   → q ≋ p → q ∈ᵈ F → p ∈ᵈ F
  
module DFA-Operations (D : DFA) where
  open DFA D
  open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)
  
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



module DFA-Properties (D : DFA) where
  open DFA D
  open DFA-Operations D
  open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)


  δ*-lem : ∀ {q q'} → q ≋ q' → ∀ w → δ* q w ≋ δ* q' w
  δ*-lem q≋q' []      = q≋q'
  δ*-lem {q} {q'} q≋q' (a ∷ w) = δ*-lem (δ-lem a q≋q') w

  -- Reachable from q₀
  Reachable : Q → Set
  Reachable q = Σ[ w ∈ Σ* ] (q₀ , w) ⊢* (q , [])

  q₀-reach : Reachable q₀
  q₀-reach = [] , (zero , ≋-refl , refl)

  data Qᴿ : Set where
    reach : ∀ q → Reachable q → Qᴿ

  reach-lem : ∀ {q w a n q'}
              → (q , w) ⊢ᵏ n ─ (q' , [])
              → (q , w ++ a ∷ []) ⊢ᵏ suc n ─ (δ q' a , [])
  reach-lem {q} {.[]} {a} {n = zero}  {q'} (q≋q' , refl)
    = δ q a , a , [] , refl , (refl , ≋-refl) , (δ-lem a q≋q' , refl)
  reach-lem {q} {._}  {a} {n = suc n} {q'} (p , b , u , refl , (refl , prf₁) , prf₂)
    = p , b , u ++ a ∷ [] , refl , (refl , prf₁) , reach-lem {p} {u} {a} {n} {q'} prf₂

  ⊢ᵏ-lem : ∀ {s q q'} → q ≋ q'
           → ∀ w n
           → (s , w) ⊢ᵏ n ─ (q , [])
           → (s , w) ⊢ᵏ n ─ (q' , [])
  ⊢ᵏ-lem q≋q' .[] zero    (s≋q , refl)
    = ≋-trans s≋q q≋q' , refl
  ⊢ᵏ-lem q≋q' ._  (suc n) (p , a , u , refl , (refl , prf₁) , prf₂)
    = p , a , u , refl , (refl , prf₁) , ⊢ᵏ-lem q≋q' u n prf₂
  

  -- easy
  reach-lem₁ : ∀ {q a} → Reachable q → Reachable (δ q a)
  reach-lem₁ {q} {a} (w , n , prf) = w ++ a ∷ [] , suc n , reach-lem {q₀} {w} {a} {n} {q} prf

  reach-lem₂ : ∀ {q q'} → q ≋ q' → Reachable q → Reachable q'
  reach-lem₂ q≋q' (w , n , prf) = w , n , ⊢ᵏ-lem q≋q' w n prf

  reach-lem₃ : ∀ {q a p} → p ≋ δ q a → Reachable q → Reachable p
  reach-lem₃ p≋δqa prf = reach-lem₂ (≋-sym p≋δqa) (reach-lem₁ prf)

  -- Equivalence states
  infix 0 _∼_
  _∼_ : Q → Q → Set
  q ∼ q' = ∀ w → δ* q w ∈ᵈ F ⇔ δ* q' w ∈ᵈ F

  ∼-lem₁ : ∀ {q q'} → q ≋ q' → q ∼ q'
  ∼-lem₁ {q} {q'} q≋q'
    = λ w → ((λ δ*qw∈F → F-lem {δ* q w} {δ* q' w} (δ*-lem q≋q' w) δ*qw∈F) , (λ δ*q'w∈F → F-lem {δ* q' w} {δ* q w} (δ*-lem (≋-sym {q} {q'} q≋q') w) δ*q'w∈F))

  ∼-lem₂ : ∀ {q q' a} → q ∼ q' → δ q a ∼ δ q' a
  ∼-lem₂ {q} {q'} {a} q∼q' = λ w → q∼q' (a ∷ w)

  -- there are several algorithms
  -- 1) Table-filling algorithm
  -- 2) ?
  postulate Dec-∼ : ∀ q q' → Dec (q ∼ q')

  ∼-refl : Reflexive _∼_
  ∼-refl = λ _ → (λ x → x) , (λ x → x)

  ∼-sym : Symmetric _∼_
  ∼-sym q∼q' = λ w → let (a , b) = q∼q' w in b , a

  ∼-trans : Transitive _∼_
  ∼-trans q∼q' q'∼q'' = λ w → let (a , b) = q∼q' w in 
                              let (c , d) = q'∼q'' w in 
                              (λ x → c (a x)) , (λ x → b (d x))

  ∼-isEquiv : IsEquivalence _∼_
  ∼-isEquiv = record { refl = ∼-refl ; sym = ∼-sym ; trans = ∼-trans }

  quot : QuotientSet
  quot = record {Q = Q ; _∼_ = _∼_ ; Dec-∼ = Dec-∼ ; ∼-isEquiv = ∼-isEquiv }


All-Reachable-States : DFA → Set
All-Reachable-States D = ∀ q → Reachable q
  where
    open DFA D
    open DFA-Properties D
