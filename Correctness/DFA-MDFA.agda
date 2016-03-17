{-
  This module contains the following proofs:
    ∀dfa∈DFA. L(dfa) ≈ L(minimise dfa)

  Steven Cheung
  Version 15-03-2016
-}
open import Util
module Correctness.DFA-MDFA (Σ : Set)(dec : DecEq Σ) where

open import Function
open import Data.List hiding (any)
open import Data.Bool
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
open Deprecated-inspect-on-steroids renaming (inspect to inspect')
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Vec renaming (_∈_ to _∈ⱽ_)

open import Subset renaming (Ø to ø)
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep
open import Language Σ dec
open import DFA Σ dec
open import Translation.DFA-MDFA Σ dec
open import Quotient

module Remove-Inaccessible-States (dfa : DFA) where
  rdfa : DFA
  rdfa = remove-inaccessible-states dfa

  open DFA dfa
  open DFA-Operations dfa
  open DFA-Properties dfa
  open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)

  open DFA rdfa renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; ≋-isEquiv to ≋₁-isEquiv)
  open DFA-Operations rdfa renaming (_⊢ᵏ_─_ to _⊢ᵏ₁_─_)
  
  lem₁ : ∀ q w n q'
         → (reachable-q  : Reachable q)
         → (reachable-q' : Reachable q')
         → (prf : (q , w) ⊢ᵏ n ─ (q' , []))
         → (reach q reachable-q , w) ⊢ᵏ₁ n ─ (reach q' reachable-q' , [])
  lem₁ q .[] zero   q' reachable-q reachable-q' (q≋q' , refl) = q≋q' , refl
  lem₁ q ._ (suc n) q' reachable-q reachable-q' (p , a , u , refl , (refl , prf₁) , prf₂)
    = reach p reachable-p , a , u , refl , (refl , prf₁) , lem₁ p u n q' reachable-p reachable-q' prf₂
      where
        reachable-p : Reachable p
        reachable-p = reach-lem₃ prf₁ reachable-q


  Lᴰ⊆Lᴿ : Lᴰ dfa ⊆ Lᴰ rdfa
  Lᴰ⊆Lᴿ w (q , q∈F , (n , prf)) = reach q (w , (n , prf)) , q∈F , (n , lem₁ q₀ w n q q₀-reach (w , n , prf) prf)

  lem₂ : ∀ q w n q'
         → (reachable-q  : Reachable q)
         → (reachable-q' : Reachable q')
         → (reach q reachable-q , w) ⊢ᵏ₁ n ─ (reach q' reachable-q' , [])
         → (q , w) ⊢ᵏ n ─ (q' , [])
  lem₂ q .[] zero    q' reachable-q reachable-q' (q≋q' , refl) = q≋q' , refl
  lem₂ q ._  (suc n) q' reachable-q reachable-q' (reach p reachable-p , a , u , refl , (refl , prf₁) , prf₂)
    = p , a , u , refl , (refl , prf₁) , lem₂ p u n q' reachable-p reachable-q' prf₂

  Lᴰ⊇Lᴿ : Lᴰ dfa ⊇ Lᴰ rdfa
  Lᴰ⊇Lᴿ w (reach q reachable-q , q∈F , (n , prf)) = q , q∈F , (n , lem₂ q₀ w n q q₀-reach reachable-q prf)


  Lᴰ≈Lᴿ : Lᴰ dfa ≈ Lᴰ (remove-inaccessible-states dfa)
  Lᴰ≈Lᴿ = Lᴰ⊆Lᴿ , Lᴰ⊇Lᴿ



module Quotient-Construction (dfa : DFA) where
  rdfa : DFA
  rdfa = remove-inaccessible-states dfa

  qdfa : DFA
  qdfa = quotient-construction rdfa

  open DFA rdfa
  open DFA-Operations rdfa
  open DFA-Properties rdfa
  open Quot-Properties quot
  open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)

  open DFA qdfa renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; _≋_ to _≋₁_ ; ≋-isEquiv to ≋₁-isEquiv ; δ-lem to δ₁-lem ; F-lem to F₁-lem)
  open DFA-Operations qdfa renaming (δ* to δ₁* ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_ ; δ₀-lem₁ to δ₀₁-lem₁)

  lem₁ : ∀ q w n q'
         → (q , w) ⊢ᵏ n ─ (q' , [])
         → (class (⟪ q ⟫) (q , IsEquivalence.refl ≈ᵈ-isEquiv) , w) ⊢ᵏ₁ n ─ (class (⟪ q' ⟫) (q' , IsEquivalence.refl ≈ᵈ-isEquiv) , [])
  lem₁ q .[] zero  q' (q≋q' , refl)
    = (proj₁ ∼iff≈)(∼-lem q≋q') , refl
  lem₁ q ._ (suc n) q' (p , a , u , refl , (refl , prf₁) , prf₂)
    = class (⟪ p ⟫) (p , IsEquivalence.refl ≈ᵈ-isEquiv) , a , u , refl
      , (refl , (proj₁ ∼iff≈) (∼-lem prf₁))
      , lem₁ p u n q' prf₂

  Lᴿ⊆Lᴹ : Lᴰ rdfa ⊆ Lᴰ qdfa
  Lᴿ⊆Lᴹ w (q , q∈F , n , prf) = class (⟪ q ⟫) (q , IsEquivalence.refl ≈ᵈ-isEquiv) , q∈F , n , lem₁ q₀ w n q prf

  lem₂ : ∀ qs q w
         → (⟪q⟫≈qs : qs ≈ᵈ ⟪ q ⟫)
         → (δ₁* (class qs (q , ⟪q⟫≈qs))) w ≋₁ (class (⟪ δ* q w ⟫) (δ* q w , IsEquivalence.refl ≈ᵈ-isEquiv))
  lem₂ qs q []      ⟪q⟫≈qs = ⟪q⟫≈qs
  lem₂ qs q (a ∷ w) ⟪q⟫≈qs = lem₂ (⟪ δ q a ⟫) (δ q a) w (IsEquivalence.refl ≈ᵈ-isEquiv)

  Lᴿ⊇Lᴹ : Lᴰ rdfa ⊇ Lᴰ qdfa
  Lᴿ⊇Lᴹ w w∈Lᴰ = let prf₁ = (proj₂ (δ₀₁-lem₁ w)) w∈Lᴰ in
                 let prf₂ = F₁-lem (lem₂ ⟪ q₀ ⟫ q₀ w (IsEquivalence.refl ≈ᵈ-isEquiv)) prf₁
                 in (proj₁ (δ₀-lem₁ w)) prf₂

  Lᴿ≈Lᴹ : Lᴰ rdfa ≈ Lᴰ qdfa
  Lᴿ≈Lᴹ = Lᴿ⊆Lᴹ , Lᴿ⊇Lᴹ


{- ∀dfa∈DFA. L(dfa) ≈ L(minimise dfa) -}
module Minimise where
  Lᴰ≈Lᴹ : ∀ dfa → Lᴰ dfa ≈ Lᴰ (minimise dfa)
  Lᴰ≈Lᴹ dfa = IsEquivalence.trans ≈-isEquiv (Remove-Inaccessible-States.Lᴰ≈Lᴿ dfa) (Quotient-Construction.Lᴿ≈Lᴹ dfa)
    

module Reachable-Proof (dfa : DFA) where
  rdfa : DFA
  rdfa = remove-inaccessible-states dfa

  open DFA dfa
  open DFA-Properties dfa
  open DFA-Operations dfa

  open DFA rdfa renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; ≋-isEquiv to ≋₁-isEquiv)
  open DFA-Operations rdfa renaming (_⊢ᵏ_─_ to _⊢ᵏ₁_─_)

  IsAllReachable : All-Reachable-States rdfa
  IsAllReachable (reach q (w , n , prf)) = w , (n , Remove-Inaccessible-States.lem₁ dfa q₀ w n q q₀-reach (w , n , prf) prf)



-- Now, we have to prove that Minimal D cannot be collapsed further
module Minimal-Definition (dfa : DFA) where
  mdfa : DFA
  mdfa = minimise dfa
  open DFA mdfa renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; _≋_ to _≋₁_ ; ≋-isEquiv to ≋₁-isEquiv ; δ-lem to δ₁-lem ; F-lem to F₁-lem)
  open DFA-Operations mdfa renaming (δ* to δ₁* ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_ ; δ₀-lem₁ to δ₀₁-lem₁)
  open DFA-Properties mdfa
  open Quot-Properties (DFA-Properties.quot mdfa)

  Minimal : Set
  Minimal = (p q : Q₁) → p ∼ q → p ≋₁ q


module Minimal-Proof (dfa : DFA) where
  mdfa₁ : DFA
  mdfa₁ = minimise dfa
  open DFA mdfa₁ renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; _≋_ to _≋₁_ ; ≋-isEquiv to ≋₁-isEquiv)
  open DFA-Operations mdfa₁ renaming (δ* to δ₁*)
  open DFA-Properties mdfa₁ renaming (quot to quot₁ ; reach to reach₁)
  open Quot-Properties quot₁ renaming (class to class₁ ; ⟪_⟫ to ⟪_⟫₁)
  
  open Minimal-Definition mdfa₁ renaming (mdfa to mdfa₂)

  open DFA mdfa₂ renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; _≋_ to _≋₂_ ; ≋-isEquiv to ≋₂-isEquiv)
  open DFA-Operations mdfa₂ renaming (δ* to δ₂*)
  open DFA-Properties mdfa₂ renaming (quot to quot₂ ; reach to reach₂)
  open Quot-Properties quot₂ renaming (class to class₂ ; ⟪_⟫ to ⟪_⟫₂)

  IsMinimal : Minimal
  IsMinimal (class₂ ps (p , ps≈⟪p⟫)) (class₂ qs (q , qs≈⟪q⟫)) p∼q = undefined
    where
      prf₁ : ∀ w → δ₂* (Quot-Properties.class ps (p , ps≈⟪p⟫)) w ≋₂ Quot-Properties.class undefined (undefined , undefined)
      prf₁ = λ w → undefined
      
