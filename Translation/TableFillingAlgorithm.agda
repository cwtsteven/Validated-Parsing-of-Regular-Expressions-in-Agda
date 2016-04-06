{-
  This module contains the algorithm to determines the decidability of _∼_, however this module has not been completed. 

  Steven Cheung
  Version 06-04-2016
-}
open import Util
open import DFA
module Translation.TableFillingAlgorithm (Σ : Set)(dec : DecEq Σ)(dfa : DFA Σ dec) where

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
open import Data.Vec hiding (_++_) renaming (_∈_ to _∈ⱽ_ ; tail to tailⱽ)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import Language Σ dec
open import MinimalDFA Σ dec

open DFA.DFA Σ dec dfa
open DFA.DFA-Operations Σ dec dfa

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

open Irreducibility dfa

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
                                                                                      
-- seems true
postulate Basis-lem₂ : ∀ p q → (δ* p [] ∈ᵈ F × δ* q [] ∉ᵈ F ⊎ δ* p [] ∉ᵈ F × δ* q [] ∈ᵈ F) → (p , q) ∈ᵈ Basis

-- can be decided by iterating the set of alphabets
postulate Dec-mark : ∀ p q qs → Dec (Σ[ a ∈ Σ ] ( (δ p a , δ q a) ∈ᵈ qs × (δ p a ∈ᵈ F × δ q a ∉ᵈ F ⊎ δ p a ∉ᵈ F × δ q a ∈ᵈ F) ))


one-step : DecSubset (Q × Q) → DecSubset (Q × Q)
one-step qs (p , q) with (p , q) ∈ᵈ? qs
... | true  = true
... | false with Dec-mark p q qs
...   | yes _ = true
...   | no  _ = false
              
steps : DecSubset (Q × Q) → ℕ → DecSubset (Q × Q)
steps qs zero    = qs
steps qs (suc n) = one-step qs ⋃ᵈ steps (one-step qs) n

Steps : ℕ → DecSubset (Q × Q)
Steps n = steps Basis n
                
steps-lem : ∀ p q qs → (p , q) ∈ᵈ qs → (p , q) ∈ᵈ one-step qs
steps-lem p q qs prf with (p , q) ∈ᵈ? one-step qs | inspect (λ s → s ∈ᵈ? one-step qs) (p , q) 
steps-lem p q qs prf | true  | [ eq ] = refl
steps-lem p q qs prf | false | [ eq ] with (p , q) ∈ᵈ? qs
steps-lem p q qs prf | false | [ () ] | true
steps-lem p q qs  () | false | [ eq ] | false


steps-lem₂ : ∀ p q → (p , q) ∈ᵈ Basis → (p , q) ∈ᵈ Steps Size
steps-lem₂ p q prf with (p , q) ∈ᵈ? Basis
steps-lem₂ p q prf | true  = refl
steps-lem₂ p q ()  | false

steps-lem₄ : ∀ qs p₂ q₂ → (∀ p q → (p , q) ∈ᵈ qs → p ≠ q) → (p₂ , q₂) ∈ᵈ one-step qs → p₂ ≠ q₂
steps-lem₄ qs p₂ q₂ f prf with (p₂ , q₂) ∈ᵈ? qs | inspect (λ s → s ∈ᵈ? qs) (p₂ , q₂)
steps-lem₄ qs p₂ q₂ f prf | true  | [ s∈qs ] = f p₂ q₂ s∈qs
steps-lem₄ qs p₂ q₂ f prf | false | [ s∈qs ] with Dec-mark p₂ q₂ qs
steps-lem₄ qs p₂ q₂ f prf | false | [ s∈qs ] | yes (a , prf₂ , prf₃) = a ∷ [] , prf₃
steps-lem₄ qs p₂ q₂ f  () | false | [ s∈qs ] | no  _

Steps-lem : ∀ n p q → (p , q) ∈ᵈ Steps n → p ≠ q
Steps-lem n p q prf = helper Basis n p q (Basis-lem) prf
  where
    helper : ∀ qs n p q → (∀ p q → (p , q) ∈ᵈ qs → p ≠ q) → (p , q) ∈ᵈ steps qs n → p ≠ q
    helper qs zero    p q f prf₁ = f p q prf₁
    helper qs (suc n) p q f prf₁ with (p , q) ∈ᵈ? one-step qs | inspect (λ s → s ∈ᵈ? one-step qs) (p , q)
    helper qs (suc n) p q f prf₁ | true  | [ eq ] = steps-lem₄ qs p q f eq
    helper qs (suc n) p q f prf₁ | false | [ eq ] = helper (one-step qs) n p q (λ p₂ q₂ x → steps-lem₄ qs p₂ q₂ f x) prf₁
    

D-States : Subset (Q × Q)
D-States (p , q) = Σ[ n ∈ ℕ ] ( (p , q) ∈ᵈ Steps n )

D-Statesᵏ : ℕ → Subset (Q × Q)
D-Statesᵏ k (p , q) = Σ[ n ∈ ℕ ] ( n ≤ k × (p , q) ∈ᵈ Steps n )


-- similar to ε-closure
postulate q1-lem₁ : ∀ k → Steps k ≈ᵈ Steps (suc k) → D-States ≈ D-Statesᵏ k


-- similar to ε-closure
postulate q2-lem₁ : ∀ p q → (p , q) ∈ D-States ⇔ (p , q) ∈ᵈ Steps Size


q2-lem₂ : ∀ p q → (p , q) ∉ᵈ Steps Size → (p , q) ∉ D-States
q2-lem₂ p q prf s∈D = ⊥-elim (prf (proj₁ (q2-lem₁ p q) s∈D))


Dec-D-States : ∀ p q → Dec ((p , q) ∈ D-States)
Dec-D-States p q with (p , q) ∈ᵈ? Steps Size | inspect (λ s → s ∈ᵈ? Steps Size) (p , q)
... | true  | [ eq ] = yes (proj₂ (q2-lem₁ p q) eq)
... | false | [ eq ] = no
                       (q2-lem₂ p q
                       (Subset.DecidableSubset.∈-lem₂ {Q × Q} {p , q} {Steps Size} eq))


D-States-lem : ∀ p q → (p ≠ q) ⇔ (p , q) ∈ D-States
D-States-lem p q = lem₁ p q , lem₂ p q
  where
    mutual
      lem₃ : ∀ p q w → (p , q) ∉ D-States → (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F) → ⊥
      lem₃ p q []      prf prf₁ = prf (Size , steps-lem₂ p q (Basis-lem₂ p q prf₁))
      lem₃ p q (a ∷ w) prf prf₁ = prf (Size , lem' p q Size (rs∈Steps Size))
        where
          r : Q
          r = δ p a
          s : Q
          s = δ q a 
          r≠s : δ p a ≠ δ q a
          r≠s = w , prf₁
          postulate rs∈Steps : ∀ n → (r , s) ∈ᵈ steps Basis (suc n)
          --rs∈Steps = lem₁ r s r≠s
          postulate lem' : ∀ p q n → (δ p a , δ q a) ∈ᵈ steps Basis (suc n) → (p , q) ∈ᵈ steps Basis n
  
      lem₁ : ∀ p q → p ≠ q → (p , q) ∈ D-States
      lem₁ p q prf with Dec-D-States p q
      lem₁ p q prf | yes x = x
      lem₁ p q (w , prf) | no ¬x = ⊥-elim (lem₃ p q w ¬x prf)
                                                      

      lem₂ : ∀ p q → (p , q) ∈ D-States → p ≠ q
      lem₂ p q (n , prf) = Steps-lem n p q prf


D-States-lem₂ : ∀ p q → (p , q) ∉ D-States → ¬ (p ≠ q)
D-States-lem₂ p q prf p≠q = ⊥-elim (prf (proj₁ (D-States-lem p q) p≠q))
