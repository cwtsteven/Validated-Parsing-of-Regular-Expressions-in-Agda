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

open import Function
open import Relation.Binary
open import Relation.Nullary
open import Data.Product hiding (Σ ; map)

open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
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
    
    Dec-≋' : ∀ q q' → Dec (q ≋' q')
    Dec-≋' (reach q prf) (reach q' prf') = Dec-≋ q q'
    
    ≋'-refl : Reflexive _≋'_
    ≋'-refl {reach q prf} = ≋-refl
    
    ≋'-sym : Symmetric _≋'_
    ≋'-sym {reach q prf} {reach q' prf'} q≋q' = ≋-sym q≋q'
    
    ≋'-trans : Transitive _≋'_
    ≋'-trans {reach q prf} {reach q' prf'} {reach q'' prf''} q≋q' q'≋q'' = ≋-trans q≋q' q'≋q''
    
    ≋'-isEquiv : IsEquivalence {A = Q'} _≋'_
    ≋'-isEquiv = record { refl = λ {q} → ≋'-refl {q} ; sym = λ {q} {q'} → ≋'-sym {q} {q'} ; trans = λ {q} {q'} {q''} → ≋'-trans {q} {q'} {q''} }

    R : DFA
    R = record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' ; _≋_ = _≋'_ ; Dec-≋ = Dec-≋' ; ≋-isEquiv = ≋'-isEquiv ; δ-lem = undefined ; F-lem = undefined }
    

quotient-construction : DFA → DFA
quotient-construction D
  = record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' ; _≋_ = _≋'_ ; Dec-≋ = Dec-≋' ; ≋-isEquiv = ≋'-isEquiv ; δ-lem = undefined ; F-lem = undefined }
  where
    open DFA D
    open DFA-Operations D
    open DFA-Properties D
    open Quot-Properties quot
    open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)

    Q' : Set
    Q' = Quot-Set

    δ' : Q' → Σ → Q'
    δ' (class qs (q , prf)) a = class (⟪ δ q a ⟫) (δ q a , IsEquivalence.refl ≈ᵈ-isEquiv)

    q₀' : Q'
    q₀' = class (⟪ q₀ ⟫) (q₀ , IsEquivalence.refl ≈ᵈ-isEquiv)

    F' : DecSubset Q'
    F' (class qs (q , prf)) = q ∈ᵈ? F

    _≋'_ : Q' → Q' → Set
    (class qs (q , prf)) ≋' (class qs' (q' , prf')) = qs ≈ᵈ qs'

    open Decidable-≈ {Q} {undefined} (undefined) (undefined) (undefined) (undefined)

    Dec-≋' : ∀ q q' → Dec (q ≋' q')
    Dec-≋' (class qs (q , prf)) (class qs' (q' , prf')) = Dec-≈ qs qs'

    ≋'-refl : Reflexive _≋'_
    ≋'-refl {class qs (q , prf)} = IsEquivalence.refl ≈ᵈ-isEquiv
    
    ≋'-sym : Symmetric _≋'_
    ≋'-sym {class qs (q , prf)} {class qs' (q' , prf')} q≋q' = IsEquivalence.sym ≈ᵈ-isEquiv q≋q'
    
    ≋'-trans : Transitive _≋'_
    ≋'-trans {class qs (q , prf)} {class qs' (q' , prf')} {class qs'' (q'' , prf'')} q≋q' q'≋q'' = IsEquivalence.trans ≈ᵈ-isEquiv q≋q' q'≋q''
    
    ≋'-isEquiv : IsEquivalence {A = Q'} _≋'_
    ≋'-isEquiv = record { refl = λ {q} → ≋'-refl {q} ; sym = λ {q} {q'} → ≋'-sym {q} {q'} ; trans = λ {q} {q'} {q''} → ≋'-trans {q} {q'} {q''} }

minimise : DFA → DFA
minimise dfa = M 
  where
    M : DFA
    M = (quotient-construction ∘ remove-inaccessible-states) dfa
