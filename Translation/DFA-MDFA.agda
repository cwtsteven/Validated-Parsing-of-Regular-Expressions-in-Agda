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
open import Data.Empty
open import Data.Vec renaming (_∈_ to _∈ⱽ_)

open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep
open import DFA Σ dec
open import Quotient

remove-inaccessible-states : DFA → DFA
remove-inaccessible-states D = R
  where
    open DFA D
    open DFA-Properties D
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
  open Quot-Properties quot renaming (_≋_ to _≋'_)
  
  Q' : Set
  Q' = Quot-Set

  δ' : Q' → Σ → Q'
  δ' (class qs (q , prf)) a = class (⟪ δ q a ⟫) (δ q a , IsEquivalence.refl ≈ᵈ-isEquiv)

  q₀' : Q'
  q₀' = class (⟪ q₀ ⟫) (q₀ , IsEquivalence.refl ≈ᵈ-isEquiv)

  F' : DecSubset Quot-Set
  F' (class qs (q , _)) = q ∈ᵈ? F
  
  p∼q⇔⟪p⟫≈⟪q⟫ : ∀ {p q} → (p ∼ q) ⇔ class (⟪ p ⟫) (p , IsEquivalence.refl ≈ᵈ-isEquiv) ≋' class ⟪ q ⟫ (q , IsEquivalence.refl ≈ᵈ-isEquiv)
  p∼q⇔⟪p⟫≈⟪q⟫ = lem₁ , lem₂
    where
      lem₁ : ∀ {p q} → p ∼ q → ⟪ p ⟫ ≈ᵈ ⟪ q ⟫
      lem₁ p∼q = lem₁-⊆ p∼q , lem₁-⊇ p∼q
        where
          lem₁-⊆ : ∀ {p} {q} → p ∼ q → ⟪ p ⟫ ⊆ᵈ ⟪ q ⟫
          lem₁-⊆ {p} {q} p∼q x x∈⟪p⟫ with Dec-∼ x q
          lem₁-⊆ {p} {q} p∼q x x∈⟪p⟫ | yes _    = refl
          lem₁-⊆ {p} {q} p∼q x x∈⟪p⟫ | no  ¬x∼q with Dec-∼ x p
          lem₁-⊆ {p} {q} p∼q x x∈⟪p⟫ | no  ¬x∼q | yes x∼p
            = ⊥-elim (¬x∼q (IsEquivalence.trans ∼-isEquiv x∼p p∼q))
          lem₁-⊆ {p} {q} p∼q x ()    | no  ¬x∼q | no  ¬x∼p

          lem₁-⊇ : ∀ {p} {q} → p ∼ q → ⟪ p ⟫ ⊇ᵈ ⟪ q ⟫
          lem₁-⊇ {p} {q} p∼q x x∈⟪q⟫ with Dec-∼ x p
          lem₁-⊇ {p} {q} p∼q x x∈⟪q⟫ | yes _    = refl
          lem₁-⊇ {p} {q} p∼q x x∈⟪q⟫ | no  ¬x∼o with Dec-∼ x q
          lem₁-⊇ {p} {q} p∼q x x∈⟪q⟫ | no  ¬x∼p | yes x∼q
            = ⊥-elim (¬x∼p (IsEquivalence.trans ∼-isEquiv x∼q (IsEquivalence.sym ∼-isEquiv p∼q)))
          lem₁-⊇ {p} {q} p∼q x ()    | no  ¬x∼p | no  ¬x∼q

      lem₂ : ∀ {p q} → ⟪ p ⟫ ≈ᵈ ⟪ q ⟫ → p ∼ q
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ with p ∈ᵈ? ⟪ q ⟫ | inspect (λ p → p ∈ᵈ? ⟪ q ⟫) p
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ | true  | [ p∈⟪q⟫ ] with Dec-∼ p q
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ | true  | [ p∈⟪q⟫ ] | yes p∼q = p∼q
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ | true  | [   ()  ] | no  _ 
      lem₂ {p} {q} ⟪p⟫≈⟪q⟫ | false | [ p∉⟪q⟫ ] = ⊥-elim ((Subset.DecidableSubset.∈-lem₂ {Q} {p} {⟪ q ⟫} p∉⟪q⟫) ((proj₁ ⟪p⟫≈⟪q⟫) p (⟪⟫-lem p)))


  
  δ'-lem : ∀ {q q'} a → q ≋' q' → δ' q a ≋' δ' q' a
  δ'-lem {class qs (q , qs≈⟪q⟫)} {class qs' (q' , qs'≈⟪q'⟫)} a q≋'q'
    = let ⟪q⟫≈⟪q'⟫ = IsEquivalence.trans ≈ᵈ-isEquiv (IsEquivalence.trans ≈ᵈ-isEquiv (IsEquivalence.sym ≈ᵈ-isEquiv qs≈⟪q⟫) q≋'q') qs'≈⟪q'⟫ in
      let q∼q' = (proj₂ p∼q⇔⟪p⟫≈⟪q⟫) ⟪q⟫≈⟪q'⟫ in
      let δqa∼δq'a = ∼-lem₂ {q} {q'} {a} q∼q' in
      proj₁ p∼q⇔⟪p⟫≈⟪q⟫ δqa∼δq'a


  F'-lem : ∀ {q q'} → q ≋' q' → q ∈ᵈ F' → q' ∈ᵈ F'
  F'-lem {class qs (q , qs≈⟪q⟫)} {class qs' (q' , qs'≈⟪q'⟫)} q≋'q' q∈F
    = let q∼q' = (proj₂ p∼q⇔⟪p⟫≈⟪q⟫) (IsEquivalence.trans ≈ᵈ-isEquiv
                                          (IsEquivalence.trans ≈ᵈ-isEquiv
                                           (IsEquivalence.sym ≈ᵈ-isEquiv qs≈⟪q⟫) q≋'q')
                                          qs'≈⟪q'⟫)
      in (proj₁ (q∼q' [])) q∈F
      


quotient-construction : DFA → DFA
quotient-construction D
  = record { Q = Q'
           ; δ = δ'
           ; q₀ = q₀'
           ; F = F'
           ; _≋_ = Quot-Properties._≋_ quot
           ; ≋-isEquiv = Quot-Properties.≋-isEquiv quot
           ; δ-lem = δ'-lem
           ; F-lem = F'-lem
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
