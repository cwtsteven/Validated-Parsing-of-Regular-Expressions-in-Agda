{-
  Here the Automata and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 2.2: Regular sets, their generators, and their recognizers
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 27-02-2016
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
                 ; _≈_ to _≈ᵈ_ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; ≈-refl to ≈ᵈ-refl ; ≈-trans to ≈ᵈ-trans ; ≈-sym to ≈ᵈ-sym)
open import QuotientSet
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
    Dec-≋ : ∀ q q' → Dec (q ≋ q')
    ≋-isEquiv : IsEquivalence _≋_
    δ-lem   : ∀ {q} {p} a → q ≋ p → δ q a ≋ δ p a
    F-lem   : ∀ {q} {p}   → q ≋ p → q ∈ᵈ F → p ∈ᵈ F
    Q?  : DecEq Q
    ∣Q∣-1 : ℕ
    It  : Vec Q (suc ∣Q∣-1)
    ∀q∈It : ∀ q → q ∈ⱽ It
    unique : Unique It
  
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

  -- remember!!
  postulate ∣Σ∣-1 : ℕ
  postulate Σ-It : Vec Σ (suc ∣Σ∣-1)
  postulate ∀a∈Σ-It : ∀ a → a ∈ⱽ Σ-It
  postulate unique-Σ : Unique Σ-It

  open DFA D
  open DFA-Operations D
  open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)

  -- Reachable from q₀
  Reachable : Q → Set
  Reachable q = Σ[ w ∈ Σ* ] (q₀ , w) ⊢* (q , [])

  Step : Q → Q → Set
  Step q q' = Σ[ a ∈ Σ ] ( q' ≋ δ q a )

  Dec-any-Step : ∀ q q' → Dec (any (λ a → q' ≋ δ q a) Σ-It)
  Dec-any-Step q q' = helper Σ-It
    where
      helper : {n : ℕ}(as : Vec Σ n) → Dec (any (λ a → q' ≋ δ q a) as)
      helper []       = no (λ z → z)
      helper (a ∷ as) with Dec-≋ q' (δ q a)
      helper (a ∷ as) | yes q'≋δqa = yes (inj₁ q'≋δqa)
      helper (a ∷ as) | no  q'≠δqa with helper as
      helper (a ∷ as) | no  q'≠δqa | yes prf₂ = yes (inj₂ prf₂)
      helper (a ∷ as) | no  q'≠δqa | no  prf₂ = no ¬any
        where
          ¬any : ¬ (q' ≋ δ q a ⊎ any (λ a → q' ≋ δ q a) as)
          ¬any (inj₁ q'≋δqa) = ⊥-elim (q'≠δqa q'≋δqa)
          ¬any (inj₂ any) = prf₂ any


  Dec-Step : ∀ q q' → Dec (Step q q')
  Dec-Step q q' with Dec-any-Step q q'
  Dec-Step q q' | yes prf = yes (Vec-any-lem₂ (λ a → q' ≋ δ q a) prf)
    where open Vec-Rep dec Σ-It ∀a∈Σ-It unique-Σ
  Dec-Step q q' | no  prf = no  (Vec-any-lem₄ (λ a → q' ≋ δ q a) prf)
    where open Vec-Rep dec Σ-It ∀a∈Σ-It unique-Σ

  open Vec-Rep Q? It ∀q∈It unique

  Dec-any-⋃-δqa : ∀ qs q' → Dec (any (λ q → q ∈ᵈ qs × Step q q') It)
  Dec-any-⋃-δqa qs q' = helper It
     where
      helper : {n : ℕ}(ps : Vec Q n) → Dec (any (λ q → q ∈ᵈ qs × Step q q') ps)
      helper [] = no (λ z → z)
      helper (p ∷ ps) with p ∈ᵈ? qs | Dec-Step p q'
      helper (p ∷ ps) | true  | yes prf  = yes (inj₁ (refl , prf))
      helper (p ∷ ps) | true  | no  prf with helper ps
      helper (p ∷ ps) | true  | no  prf | yes prf₂ = yes (inj₂ prf₂)
      helper (p ∷ ps) | true  | no  prf | no  prf₂ = no ¬any
        where
          ¬any : ¬ (true ≡ true × Step p q' ⊎ any (λ q → q ∈ᵈ qs × Step q q') ps)
          ¬any (inj₁ (_ , prf')) = ⊥-elim (prf prf')
          ¬any (inj₂ any) = prf₂ any
      helper (p ∷ ps) | false | step? with helper ps
      helper (p ∷ ps) | false | step? | yes prf = yes (inj₂ prf)
      helper (p ∷ ps) | false | step? | no  prf = no ¬any
        where
          ¬any : ¬ (false ≡ true × Step p q' ⊎ any (λ q → q ∈ᵈ qs × Step q q') ps)
          ¬any (inj₁ (() , _))
          ¬any (inj₂ prf₁) = prf prf₁
          
  Dec-⋃-δqa : ∀ qs q' → Dec (Σ[ q ∈ Q ] ( q ∈ᵈ qs × Step q q' ))
  Dec-⋃-δqa qs q' with Dec-any-⋃-δqa qs q'
  Dec-⋃-δqa qs q' | yes prf = yes (Vec-any-lem₂ (λ q → q ∈ᵈ qs × Step q q') prf)
  Dec-⋃-δqa qs q' | no  prf = no  (Vec-any-lem₄ (λ q → q ∈ᵈ qs × Step q q') prf)

  ⋃-δqa : DecSubset Q → DecSubset Q
  ⋃-δqa qs q' with Dec-⋃-δqa qs q'
  ... | yes _ = true
  ... | no  _ = false
  
  n-path : Q → ℕ → DecSubset Q
  n-path q zero    = ⟦ q ⟧ᵈ {{Q?}}
  n-path q (suc n) = n-path q n ⋃ᵈ ⋃-δqa (n-path q n)

  Qᵣ : Q → Subset Q
  Qᵣ q = λ q' → Σ[ n ∈ ℕ ] ( q' ∈ᵈ n-path q n )

  Q₀ᵣ : Subset Q
  Q₀ᵣ = Qᵣ q₀

  -- needs to prove

  Dec-Qᵣ : ∀ p q → Dec (p ∈ Qᵣ q)
  Dec-Qᵣ = undefined

  -- needs to prove
  Qᵣ-lem : ∀ q → Reachable q ⇔ q ∈ Q₀ᵣ
  Qᵣ-lem = undefined

  
  -- Equivalence states
  infix 0 _∼_
  _∼_ : Q → Q → Set
  q ∼ q' = ∀ w → δ* q w ∈ᵈ F ⇔ δ* q' w ∈ᵈ F

  ∼-Equiv : IsEquivalence _∼_
  ∼-Equiv = undefined

  -- Equivalence classes
  infix 0 ⟪_⟫
  ⟪_⟫ : Q → (Q → Set)
  ⟪ p ⟫ = λ q → q ∼ p
  

  ∼-lem₁ : ∀ p q → (p ∼ q) ⇔ (⟪ p ⟫ ≈ ⟪ q ⟫)
  ∼-lem₁ = undefined

All-Reachable-States : DFA → Set
All-Reachable-States D = ∀ q → Reachable q
  where
    open DFA D
    open DFA-Properties D



{-
record All-Reachable-States (D : DFA) : Set₁ where
  field
    Qᴹ   : DecSubset (DFA.Q D)
    all-reachable : ∀ q → q ∈ᵈ Qᴹ ⇔ DFA-Properties.Reachable D q
    δ    : (q : DFA.Q D) → q ∈ᵈ Qᴹ → Σ → Σ[ q' ∈ DFA.Q D ] q' ∈ᵈ Qᴹ
    q₀   : DFA.Q D
    F    : DecSubset (DFA.Q D)
    F⊆Qᴹ : F ⊆ᵈ Qᴹ
-}
