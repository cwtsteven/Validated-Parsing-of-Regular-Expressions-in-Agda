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
open import Data.Vec
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ⱽ_) hiding (_∉_)


open import Subset
open import Subset.DecidableSubset
  renaming (_∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to Øᵈ ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep
open import DFA Σ dec
open import MinimalDFA Σ dec
open import Quotient
open import Language Σ dec


remove-unreachable-states : DFA → DFA
remove-unreachable-states D = R
  where
    open DFA D
    open DFA-Properties D
    open Remove-Unreachable-States D
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
  p ∼ q = ∀ w → δ* p w ∈ᵈ F Util.⇔ δ* q w ∈ᵈ F

  open Irreducibility dfa

  
  ≠-lem : ∀ {p q} → (¬ (p ∼ q)) Util.⇔ (p ≠ q)

  ≠-lem₁ : ∀ {p q} → ¬ (p ≠ q) → p ∼ q

  ≠-lem₂ : ∀ {p q w} → (δ* p w ∈ᵈ F Util.⇔ δ* q w ∈ᵈ F) ⇔ ¬ (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F)
  
  ≠-lem₃ : ∀ {p q} → p ∼ q → ¬ (p ≠ q)
  
  ≠-lem₁ {p} {q} ¬p≠q w = let lem₁ = ¬∃-∀¬ (λ w → (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F)) ¬p≠q in
                              proj₂ (≠-lem₂ {p} {q} {w}) (lem₁ w)

  ≠-lem₂ {p} {q} {w} = lem₁ {p} {q} {w} , lem₂ {p} {q} {w}
    where
      lem₁ : ∀ {p q w} → (δ* p w ∈ᵈ F Util.⇔ δ* q w ∈ᵈ F) → ¬ (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F)
      lem₁ prf₁ (inj₁ (prf₂ , prf₃)) = ⊥-elim (prf₃ (proj₁ prf₁ prf₂))
      lem₁ prf₁ (inj₂ (prf₂ , prf₃)) = ⊥-elim (prf₂ (proj₂ prf₁ prf₃))

      lem₂ : ∀ {p q w} → ¬ (δ* p w ∈ᵈ F × δ* q w ∉ᵈ F ⊎ δ* p w ∉ᵈ F × δ* q w ∈ᵈ F) → (δ* p w ∈ᵈ F Util.⇔ δ* q w ∈ᵈ F)
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
      


  Dec-∼ : ∀ p q → Dec (p ∼ q)
  Dec-∼ p q with Dec-≠ p q
  ... | yes p≠q = no (proj₂ ≠-lem p≠q)
  ... | no ¬p≠q = yes (≠-lem₁ ¬p≠q)

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
  Q' = Q/~

  δ' : Q' → Σ → Q'
  δ' (class qs (q , prf)) a = class (⟪ δ q a ⟫) (δ q a , IsEquivalence.refl ≈ᵈ-isEquiv)

  q₀' : Q'
  q₀' = class (⟪ q₀ ⟫) (q₀ , IsEquivalence.refl ≈ᵈ-isEquiv)

  F' : DecSubset Q/~
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
    M = (quotient-construction ∘ remove-unreachable-states) dfa
