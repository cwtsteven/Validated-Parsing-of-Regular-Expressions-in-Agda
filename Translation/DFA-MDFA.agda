{-
  Here the translation from DFA-MDFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung
  Version 15-03-2016
-}
open import Util
module Translation.DFA-MDFA (Σ : Set)(dec : DecEq Σ) where

open import Data.Bool
open import Data.List
open import Data.Nat
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (Σ ; map)
open import Data.Sum
open import Data.Empty
open import Data.Vec renaming (_∈_ to _∈ⱽ_) hiding ( _++_ )
open import Induction.Nat

open import Subset
open import Subset.DecidableSubset
  renaming (_∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to Øᵈ ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep
open import DFA Σ dec
open import Quotient
open import Language Σ dec

module Remove-Inaccessible-States (dfa : DFA) where
  open DFA dfa
  open DFA-Operations dfa
  open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)
  
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


remove-inaccessible-states : DFA → DFA
remove-inaccessible-states D = R
  where
    open DFA D
    open DFA-Properties D
    open Remove-Inaccessible-States D
    open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)
    Q' : Set
    Q' = Qᴿ
    
    δ' : Q' → Σ → Q'
    δ' (reach q prf) a = reach (δ q a) (reach-lem₁ prf)
    
    q₀' : Q'
    q₀' = reach q₀ q₀-reach
    
    F' : DecSubset Q'
    F' (reach q prf) = q ∈ᵈ? F
    
    _≋'_ : Q' → Q' → Set
    (reach q prf) ≋' (reach q' prf') = q ≋ q'
    
    ≋'-refl : Reflexive _≋'_
    ≋'-refl {reach q prf} = ≋-refl
    
    ≋'-sym : Symmetric _≋'_
    ≋'-sym {reach q prf} {reach q' prf'} q≋q' = ≋-sym q≋q'
    
    ≋'-trans : Transitive _≋'_
    ≋'-trans {reach q prf} {reach q' prf'} {reach q'' prf''} q≋q' q'≋q'' = ≋-trans q≋q' q'≋q''
    
    ≋'-isEquiv : IsEquivalence {A = Q'} _≋'_
    ≋'-isEquiv = record { refl = λ {q} → ≋'-refl {q} ; sym = λ {q} {q'} → ≋'-sym {q} {q'} ; trans = λ {q} {q'} {q''} → ≋'-trans {q} {q'} {q''} }

    δ'-lem : ∀ {q q'} a → q ≋' q' → δ' q a ≋' δ' q' a
    δ'-lem {reach q r-q} {reach q' r-q'} a q≋'q' = δ-lem a q≋'q'

    F'-lem : ∀ {q q'}   → q ≋' q' → q ∈ᵈ F' → q' ∈ᵈ F'
    F'-lem {reach q r-q} {reach q' r-q'} q≋'q' q∈F' = F-lem q≋'q' q∈F'

    R : DFA
    R = record { Q = Q'
               ; δ = δ'
               ; q₀ = q₀'
               ; F = F'
               ; _≋_ = _≋'_
               ; ≋-isEquiv = ≋'-isEquiv
               ; δ-lem = λ {q} {q'} → δ'-lem {q} {q'}
               ; F-lem = λ {q} {q'} → F'-lem {q} {q'}
               }


module Quotient-Construct (dfa : DFA) where
  open DFA dfa
  open DFA-Operations dfa
  open DFA-Properties dfa
  open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)
  
  -- States Equivalence
  infix 0 _∼_
  _∼_ : Q → Q → Set
  p ∼ q = ∀ w → δ* p w ∈ᵈ F ⇔ δ* q w ∈ᵈ F

  -- Distinquishable states
  infix 0 _≠_
  _≠_ : Q → Q → Set
  p ≠ q = Σ[ w ∈ Σ* ] (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F)

  ≠-lem : ∀ {p q} → (¬ (p ∼ q)) ⇔ (p ≠ q)

  ≠-lem₁ : ∀ {p q} → ¬ (p ≠ q) → p ∼ q

  ≠-lem₃ : ∀ {p q} → p ∼ q → ¬ (p ≠ q)

  ≠-lem₂ : ∀ {p q w} → (δ* p w ∈ᵈ F ⇔ δ* q w ∈ᵈ F) ⇔ ¬ (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F)

  module TableFillingAlgorithm where

    postulate ∣Q∣-1 : ℕ
    postulate Q? : DecEq Q
    postulate It : Vec Q (suc ∣Q∣-1)
    postulate ∀q∈It : ∀ q → q ∈ⱽ It
    postulate unique : Unique It

    open import RelationTable
    
    open Table-Construction Q Q? ∣Q∣-1 It ∀q∈It unique

    Size : ℕ
    Size = suc ∣Q∣-1 * suc ∣Q∣-1

    size-helper : {n : ℕ} → (ps : Vec (Q × Q) (suc n)) → Unique ps → DecSubset (Q × Q) → ℕ
    size-helper (p ∷ [])     tt  qs with p ∈ᵈ? qs
    ... | true  = 1
    ... | false = 0
    size-helper (p ∷ x ∷ ps) (proj₁ , proj₂) qs with p ∈ᵈ? qs
    ... | true  = suc (size-helper (x ∷ ps) proj₂ qs)
    ... | false = size-helper (x ∷ ps) proj₂ qs

    -- size of a subset
    size : DecSubset (Q × Q) → ℕ
    size qs = size-helper table unique-table qs
    

    basis : ∀ {n} → Vec (Q × Q) n → DecSubset (Q × Q)
    basis [] = Øᵈ
    basis ((p , q) ∷ t) with p ∈ᵈ? F | q ∈ᵈ? F
    ... | true  | true  = basis t
    ... | true  | false = ⟦ p , q ⟧ᵈ {{Dec-Pair}} ⋃ᵈ basis t
    ... | false | true  = ⟦ p , q ⟧ᵈ {{Dec-Pair}} ⋃ᵈ basis t
    ... | false | false = basis t

    Basis : DecSubset (Q × Q)
    Basis = basis table
    
    Basis-lem : ∀ p q → (p , q) ∈ᵈ Basis → p ≠ q
    Basis-lem p q prf = helper p q table prf
      where
        helper : ∀ {n} p q → (it : Vec (Q × Q) n) → (p , q) ∈ᵈ basis it → p ≠ q
        helper p q []              ()
        helper p q ((p₁ , q₁) ∷ t) prf with p₁ ∈ᵈ? F | inspect F p₁ | q₁ ∈ᵈ? F | inspect F q₁
        helper p q ((p₁ , q₁) ∷ t) prf | true  | [ p₁∈F ] | true  | [ q₁∈F ] = helper p q t prf
        helper p q ((p₁ , q₁) ∷ t) prf | true  | [ p₁∈F ] | false | [ q₁∉F ] with Q? p₁ p | Q? q₁ q
        helper p q ((.p , .q) ∷ t) prf | true  | [ p₁∈F ] | false | [ q₁∉F ] | yes refl | yes refl = [] , (inj₁ (p₁∈F , Subset.DecidableSubset.∈-lem₂ {Q} {q} {F} q₁∉F))
        helper p q ((p₁ , q₁) ∷ t) prf | true  | [ p₁∈F ] | false | [ q₁∉F ] | no  _    | _        = helper p q t prf
        helper p q ((.p , q₁) ∷ t) prf | true  | [ p₁∈F ] | false | [ q₁∉F ] | yes refl | no  _    = helper p q t prf
        helper p q ((p₁ , q₁) ∷ t) prf | false | [ p₁∉F ] | true  | [ q₁∈F ] with Q? p₁ p | Q? q₁ q
        helper p q ((.p , .q) ∷ t) prf | false | [ p₁∉F ] | true  | [ q₁∈F ] | yes refl | yes refl = [] , (inj₂ (Subset.DecidableSubset.∈-lem₂ {Q} {p} {F} p₁∉F , q₁∈F))
        helper p q ((p₁ , q₁) ∷ t) prf | false | [ p₁∉F ] | true  | [ q₁∈F ] | no  _    | _        = helper p q t prf
        helper p q ((.p , q₁) ∷ t) prf | false | [ p₁∉F ] | true  | [ q₁∈F ] | yes refl | no  _    = helper p q t prf
        helper p q ((p₁ , q₁) ∷ t) prf | false | [ p₁∈F ] | false | [ q₁∉F ] = helper p q t prf

    postulate ⟦pq⟧-lem : ∀ p q qs → (p , q) ∈ᵈ ⟦ p , q ⟧ᵈ {{Dec-Pair}} ⋃ᵈ qs
    --⟦pq⟧-lem p q = {!!}

    postulate Basis-lem₂ : ∀ p q → (δ* p [] ∈ᵈ F × δ* q [] ∉ᵈ F ⊎ δ* p [] ∉ᵈ F × δ* q [] ∈ᵈ F) → (p , q) ∈ᵈ Basis
    {-
    Basis-lem₂ p q (inj₁ (p∈F , q∉F)) = helper table unique-table (∀ab∈table p q)
      where
        helper : ∀ {n} → (it : Vec (Q × Q) n) → Unique it → (p , q) ∈ⱽ it → (p , q) ∈ᵈ basis it
        helper [] unique ()
        helper ((p₁ , q₁) ∷ []) unique s∈it with It-lem ((p₁ , q₁) ∷ []) (p , q) s∈it
        helper ((.p , .q) ∷ []) unique s∈it | inj₁ refl with p ∈ᵈ? F | inspect F p | q ∈ᵈ? F | inspect F q
        helper ((.p , .q) ∷ []) unique s∈it | inj₁ refl | true  | [ p∈F ] | true  | [ q∈F ] = ⊥-elim (q∉F q∈F)
        helper ((.p , .q) ∷ []) unique s∈it | inj₁ refl | true  | [ p∈F ] | false | [ q∉F ] = ⟦pq⟧-lem p q Øᵈ
        helper ((.p , .q) ∷ []) unique s∈it | inj₁ refl | false | [ p∉F ] | _     | [ _   ] = ⊥-elim (Subset.DecidableSubset.∈-lem₂ {Q} {p} {F} p∉F p∈F)
        helper ((p₁ , q₁) ∷ []) unique s∈it | inj₂ ()
        helper ((p₁ , q₁) ∷ (p₂ , q₂) ∷ it) unique s∈it with It-lem ((p₁ , q₁) ∷ (p₂ , q₂) ∷ it) (p , q) s∈it
        helper ((.p , .q) ∷ (p₂ , q₂) ∷ it) unique s∈it | inj₁ refl with p ∈ᵈ? F | inspect F p | q ∈ᵈ? F | inspect F q
        helper ((.p , .q) ∷ (p₂ , q₂) ∷ it) unique s∈it | inj₁ refl | true  | [ p∈F ] | true  | [ q∈F ] = ⊥-elim (q∉F q∈F)
        helper ((.p , .q) ∷ (p₂ , q₂) ∷ it) unique s∈it | inj₁ refl | true  | [ p∈F ] | false | [ q∉F ] = ⟦pq⟧-lem p q (basis ((p₂ , q₂) ∷ it))
        helper ((.p , .q) ∷ (p₂ , q₂) ∷ it) unique s∈it | inj₁ refl | false | [ p∉F ] | _     | [ _   ] = ⊥-elim (Subset.DecidableSubset.∈-lem₂ {Q} {p} {F} p∉F p∈F)
        helper ((p₁ , q₁) ∷ (p₂ , q₂) ∷ it) unique s∈it | inj₂ s∈qs with p₁ ∈ᵈ? F | inspect F p₁ | q₁ ∈ᵈ? F | inspect F q₁
        helper ((p₁ , q₁) ∷ (p₂ , q₂) ∷ it) unique s∈it | inj₂ s∈qs | true  | [ p∈F ] | true  | [ q∈F ] = helper ((p₂ , q₂) ∷ it) (proj₂ unique) s∈qs
        helper ((p₁ , q₁) ∷ (p₂ , q₂) ∷ it) unique s∈it | inj₂ s∈qs | true  | [ p∈F ] | false | [ q∉F ] = {!!}
        helper ((p₁ , q₁) ∷ (p₂ , q₂) ∷ it) unique s∈it | inj₂ s∈qs | false | [ p∉F ] | true  | [ _   ] = {!!}
        helper ((p₁ , q₁) ∷ (p₂ , q₂) ∷ it) unique s∈it | inj₂ s∈qs | false | [ p∉F ] | false | [ _   ] = helper ((p₂ , q₂) ∷ it) (proj₂ unique) s∈qs
    Basis-lem₂ p q (inj₂ (p∉F , q∈F)) = {!!}-}

    
    postulate Dec-mark : ∀ p q qs → Dec (Σ[ a ∈ Σ ] ( (δ p a , δ q a) ∈ᵈ qs × (δ p a ∈ᵈ F × δ q a ∉ᵈ F ⊎ δ p a ∉ᵈ F × δ q a ∈ᵈ F) ))


    one-step : DecSubset (Q × Q) → DecSubset (Q × Q)
    one-step qs (p , q) with (p , q) ∈ᵈ? qs
    ... | true  = true
    ... | false with Dec-mark p q qs
    ...   | yes _ = true
    ...   | no  _ = false

    steps : DecSubset (Q × Q) → ℕ → DecSubset (Q × Q)
    steps qs zero    = Øᵈ
    steps qs (suc n) = steps (one-step qs) n

    Steps : ℕ → DecSubset (Q × Q)
    Steps n = steps Basis n

    steps-lem : ∀ p q qs → (p , q) ∈ᵈ qs → (p , q) ∈ᵈ one-step qs
    steps-lem p q qs prf with (p , q) ∈ᵈ? one-step qs | inspect (λ s → s ∈ᵈ? one-step qs) (p , q) 
    steps-lem p q qs prf | true  | [ eq ] = refl
    steps-lem p q qs prf | false | [ eq ] with (p , q) ∈ᵈ? qs
    steps-lem p q qs prf | false | [ () ] | true
    steps-lem p q qs  () | false | [ eq ] | false

    -- reasonable
    postulate steps-lem₂ : ∀ p q → (p , q) ∈ᵈ Basis → (p , q) ∈ᵈ Steps Size
    --steps-lem₂ p q prf = {!!}

    Steps-lem : ∀ n p q → (p , q) ∈ᵈ Steps n → p ≠ q
    Steps-lem = helper Basis
      where
        helper : ∀ qs n p q → (p , q) ∈ᵈ steps qs n → p ≠ q
        helper qs zero    p q ()
        helper qs (suc n) p q prf = helper (one-step qs) n p q prf
        

    D-States : Subset (Q × Q)
    D-States (p , q) = Σ[ n ∈ ℕ ] ( (p , q) ∈ᵈ Steps n )

    D-Statesᵏ : ℕ → Subset (Q × Q)
    D-Statesᵏ k (p , q) = Σ[ n ∈ ℕ ] ( n ≤ k × (p , q) ∈ᵈ Steps n )

    -- similar to ε-closure
    postulate q1-lem₁ : ∀ k → Steps k ≈ᵈ Steps (suc k) → D-States ≈ D-Statesᵏ k
    --q1-lem₁ = {!!}

    -- similar to ε-closure
    postulate q2-lem₁ : ∀ p q → (p , q) ∈ D-States ⇔ (p , q) ∈ᵈ Steps Size
    --q2-lem₁ = {!!}

    q2-lem₂ : ∀ p q → (p , q) ∉ᵈ Steps Size → (p , q) ∉ D-States
    q2-lem₂ p q prf s∈D = ⊥-elim (prf (proj₁ (q2-lem₁ p q) s∈D))

    Dec-D-States : ∀ p q → Dec ((p , q) ∈ D-States)
    Dec-D-States p q with (p , q) ∈ᵈ? Steps Size | inspect (λ s → s ∈ᵈ? Steps Size) (p , q)
    ... | true  | [ eq ] = yes (proj₂ (q2-lem₁ p q) eq)
    ... | false | [ eq ] = no
                             (q2-lem₂ p q
                              (Subset.DecidableSubset.∈-lem₂ {Q × Q} {p , q} {Steps Size} eq))

    D-States-lem : ∀ p q → (p ≠ q) ⇔ (p , q) ∈ D-States
    D-States-lem p q = lem₁ , lem₂
      where
        postulate lem₄ : (p , q) ∉ᵈ Steps Size → ¬ (p ≠ q)
        --lem₄ prf ([]    , p≠q) = prf (steps-lem₂ p q (Basis-lem₂ p q p≠q))
        --lem₄ prf (a ∷ w , p≠q) = {!!}

        lem₃ : p ≠ q → (p , q) ∈ᵈ Steps Size
        lem₃ prf with (p , q) ∈ᵈ? Steps Size | inspect (λ s → s ∈ᵈ? Steps Size) (p , q)
        lem₃ prf | true  | _      = refl
        lem₃ prf | false | [ eq ] = ⊥-elim (lem₄ (Subset.DecidableSubset.∈-lem₂ {Q × Q} {p , q} {Steps Size} eq) prf)
  
        lem₁ : p ≠ q → (p , q) ∈ D-States
        lem₁ prf = proj₂ (q2-lem₁ p q) (lem₃ prf)

        lem₂ : (p , q) ∈ D-States → p ≠ q
        lem₂ (n , prf) = Steps-lem n p q prf


    D-States-lem₂ : ∀ p q → (p , q) ∉ D-States → ¬ (p ≠ q)
    D-States-lem₂ p q prf p≠q = ⊥-elim (prf (proj₁ (D-States-lem p q) p≠q))

  open TableFillingAlgorithm

  -- there are several algorithms
  -- 1) Table-filling algorithm
  -- 2) Myhill-Nerode Theorem (Partition refinement)
  postulate Dec-≠ : ∀ p q → Dec (p ≠ q)
  --Dec-≠ p q with Dec-D-States p q
  --... | yes prf = yes (proj₂ (D-States-lem p q) prf)
  --... | no  prf = no  (D-States-lem₂ p q prf)
  

  Dec-∼ : ∀ p q → Dec (p ∼ q)
  Dec-∼ p q with Dec-≠ p q
  ... | yes p≠q = no (proj₂ ≠-lem p≠q)
  ... | no ¬p≠q = yes (≠-lem₁ ¬p≠q)

  ≠-lem₁ {p} {q} ¬p≠q w = let lem₁ = ¬∃-∀¬ (λ w → (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F)) ¬p≠q in
                              proj₂ (≠-lem₂ {p} {q} {w}) (lem₁ w)

  ≠-lem₂ {p} {q} {w} = lem₁ {p} {q} {w} , lem₂ {p} {q} {w}
    where
      lem₁ : ∀ {p q w} → (δ* p w ∈ᵈ F ⇔ δ* q w ∈ᵈ F) → ¬ (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F)
      lem₁ prf₁ (inj₁ (prf₂ , prf₃)) = ⊥-elim (prf₃ (proj₁ prf₁ prf₂))
      lem₁ prf₁ (inj₂ (prf₂ , prf₃)) = ⊥-elim (prf₂ (proj₂ prf₁ prf₃))

      lem₂ : ∀ {p q w} → ¬ (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F) → (δ* p w ∈ᵈ F ⇔ δ* q w ∈ᵈ F)
      lem₂ {p} {q} {w} prf = left {p} {q} {w} prf , right {p} {q} {w} prf
        where
          left : ∀ {p q w} → ¬ (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F) → (δ* p w ∈ᵈ F → δ* q w ∈ᵈ F)
          left {p} {q} {w} prf₁ prf₂ with δ* q w ∈ᵈ? F
          left {p} {q} {w} prf₁ prf₂ | true  = refl
          left {p} {q} {w} prf₁ prf₂ | false = ⊥-elim (prf₁ (inj₁ (prf₂ , (λ x → Bool-lem₁₂ x))))

          right : ∀ {p q w} → ¬ (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F) → (δ* q w ∈ᵈ F → δ* p w ∈ᵈ F)
          right {p} {q} {w} prf₁ prf₂ with δ* p w ∈ᵈ? F
          right {p} {q} {w} prf₁ prf₂ | true  = refl
          right {p} {q} {w} prf₁ prf₂ | false = ⊥-elim (prf₁ (inj₂ ((λ x → Bool-lem₁₂ x), prf₂)))

  ≠-lem₃ {p} {q} p∼q (w , inj₁ (prf₁ , prf₂)) = prf₂ (proj₁ (p∼q w) prf₁)
  ≠-lem₃ {p} {q} p∼q (w , inj₂ (prf₁ , prf₂)) = prf₁ (proj₂ (p∼q w) prf₂)

  ≠-lem = lem₁ , lem₂
    where
      lem₁ : ∀ {p q} → ¬ (p ∼ q) → p ≠ q
      lem₁ {p} {q} ¬p∼q with Dec-≠ p q
      ... | yes p≠q  = p≠q
      ... | no  ¬p≠q = let lem₁ = ¬∃-∀¬ (λ w → (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F)) ¬p≠q in
                       let lem₂ = λ w → (proj₂ (≠-lem₂ {p} {q} {w})) (lem₁ w) in
                       ⊥-elim (¬p∼q lem₂)

      lem₂ : ∀ {p q} → p ≠ q → ¬ (p ∼ q)
      lem₂ {p} {q} (w , inj₁ (prf₁ , prf₂)) prf₃ = ⊥-elim (prf₂ ((proj₁ (prf₃ w)) prf₁))
      lem₂ {p} {q} (w , inj₂ (prf₁ , prf₂)) prf₃ = ⊥-elim (prf₁ ((proj₂ (prf₃ w)) prf₂))
      

  ∼-lem₁ : ∀ {q q'} → q ≋ q' → q ∼ q'
  ∼-lem₁ {q} {q'} q≋q'
    = λ w → ((λ δ*qw∈F → F-lem {δ* q w} {δ* q' w} (δ*-lem q≋q' w) δ*qw∈F) , (λ δ*q'w∈F → F-lem {δ* q' w} {δ* q w} (δ*-lem (≋-sym {q} {q'} q≋q') w) δ*q'w∈F))

  ∼-lem₂ : ∀ {q q' a} → q ∼ q' → δ q a ∼ δ q' a
  ∼-lem₂ {q} {q'} {a} q∼q' = λ w → q∼q' (a ∷ w)
  

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


  open Quot-Properties quot renaming (_≋_ to _≋'_)
  
  Q' : Set
  Q' = Quot-Set

  δ' : Q' → Σ → Q'
  δ' (class qs (q , prf)) a = class (⟪ δ q a ⟫) (δ q a , IsEquivalence.refl ≈ᵈ-isEquiv)

  q₀' : Q'
  q₀' = class (⟪ q₀ ⟫) (q₀ , IsEquivalence.refl ≈ᵈ-isEquiv)

  F' : DecSubset Quot-Set
  F' (class qs (q , _)) = q ∈ᵈ? F
  
  δ'-lem : ∀ {q q'} a → q ≋' q' → δ' q a ≋' δ' q' a
  δ'-lem {class qs (q , qs≈⟪q⟫)} {class qs' (q' , qs'≈⟪q'⟫)} a q≋'q'
    = ∼-lem₂ {q} {q'} {a} q≋'q'
  

  F'-lem : ∀ {q q'} → q ≋' q' → q ∈ᵈ F' → q' ∈ᵈ F'
  F'-lem {class qs (q , qs≈⟪q⟫)} {class qs' (q' , qs'≈⟪q'⟫)} q≋'q' q∈F
    = (proj₁ (q≋'q' [])) q∈F
      

quotient-construction : DFA → DFA
quotient-construction D
  = record { Q = Q'
           ; δ = δ'
           ; q₀ = q₀'
           ; F = F'
           ; _≋_ = Quot-Properties._≋_ quot
           ; ≋-isEquiv = Quot-Properties.≋-isEquiv quot
           ; δ-lem = λ {q q'} → δ'-lem {q} {q'}
           ; F-lem = λ {q q'} → F'-lem {q} {q'}
           }
  where
    open DFA D
    open DFA-Operations D
    open DFA-Properties D
    open Quotient-Construct D


minimise : DFA → DFA
minimise dfa = M 
  where
    M : DFA
    M = (quotient-construction ∘ remove-inaccessible-states) dfa
