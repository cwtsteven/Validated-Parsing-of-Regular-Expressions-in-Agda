{-
  This module contains the following proofs:
    ∀dfa∈DFA. L(dfa) ≈ L(minimise dfa)
    ∀dfa∈DFA. minimise(dfa) is minimal

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
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _∉_ to _∉ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep
open import Language Σ dec
open import DFA Σ dec
open import Translation.DFA-MDFA Σ dec
open import Quotient

module Remove-Inaccessible-States-Proof (dfa : DFA) where
  rdfa : DFA
  rdfa = remove-inaccessible-states dfa

  open DFA dfa
  open DFA-Operations dfa
  open DFA-Properties dfa
  open Remove-Inaccessible-States dfa
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



module Quotient-Construction-Proof (dfa : DFA) where
  rdfa : DFA
  rdfa = remove-inaccessible-states dfa

  qdfa : DFA
  qdfa = quotient-construction rdfa

  open DFA rdfa
  open DFA-Operations rdfa
  open DFA-Properties rdfa
  open Quotient-Construct rdfa
  open Quot-Properties quot using (class ; ⟪_⟫)
  open IsEquivalence ≋-isEquiv renaming (refl to ≋-refl ; sym to ≋-sym ; trans to ≋-trans)

  open DFA qdfa renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; _≋_ to _≋₁_ ; ≋-isEquiv to ≋₁-isEquiv ; δ-lem to δ₁-lem ; F-lem to F₁-lem)
  open DFA-Operations qdfa renaming (δ* to δ₁* ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_ ; δ₀-lem₁ to δ₀₁-lem₁)

  lem₁ : ∀ q w n q'
         → (q , w) ⊢ᵏ n ─ (q' , [])
         → (class (⟪ q ⟫) (q , IsEquivalence.refl ≈ᵈ-isEquiv) , w) ⊢ᵏ₁ n ─ (class (⟪ q' ⟫) (q' , IsEquivalence.refl ≈ᵈ-isEquiv) , [])
  lem₁ q .[] zero  q' (q≋q' , refl)
    = ∼-lem₁ q≋q' , refl
  lem₁ q ._ (suc n) q' (p , a , u , refl , (refl , prf₁) , prf₂)
    = class (⟪ p ⟫) (p , IsEquivalence.refl ≈ᵈ-isEquiv) , a , u , refl
      , (refl , ∼-lem₁ prf₁) , lem₁ p u n q' prf₂

  Lᴿ⊆Lᴹ : Lᴰ rdfa ⊆ Lᴰ qdfa
  Lᴿ⊆Lᴹ w (q , q∈F , n , prf) = class (⟪ q ⟫) (q , IsEquivalence.refl ≈ᵈ-isEquiv) , q∈F , n , lem₁ q₀ w n q prf

  lem₂ : ∀ qs q w
         → (⟪q⟫≈qs : qs ≈ᵈ ⟪ q ⟫)
         → (δ₁* (class qs (q , ⟪q⟫≈qs))) w ≋₁ (class (⟪ δ* q w ⟫) (δ* q w , IsEquivalence.refl ≈ᵈ-isEquiv))
  lem₂ qs q []      ⟪q⟫≈qs = λ w → (λ x → x) , (λ x → x)
  lem₂ qs q (a ∷ w) ⟪q⟫≈qs = lem₂ (⟪ δ q a ⟫) (δ q a) w (IsEquivalence.refl ≈ᵈ-isEquiv)

  Lᴿ⊇Lᴹ : Lᴰ rdfa ⊇ Lᴰ qdfa
  Lᴿ⊇Lᴹ w w∈Lᴰ = let prf₁ = (proj₂ (δ₀₁-lem₁ w)) w∈Lᴰ in
                 let prf₂ = F₁-lem {δ₁* (class ⟪ q₀ ⟫ (q₀ , IsEquivalence.refl ≈ᵈ-isEquiv)) w} {class ⟪ δ* q₀ w ⟫ (δ* q₀ w , IsEquivalence.refl ≈ᵈ-isEquiv)}
                            (lem₂ ⟪ q₀ ⟫ q₀ w (IsEquivalence.refl ≈ᵈ-isEquiv)) prf₁
                 in (proj₁ (δ₀-lem₁ w)) prf₂

  Lᴿ≈Lᴹ : Lᴰ rdfa ≈ Lᴰ qdfa
  Lᴿ≈Lᴹ = Lᴿ⊆Lᴹ , Lᴿ⊇Lᴹ


{- ∀dfa∈DFA. L(dfa) ≈ L(minimise dfa) -}
module Minimise where
  Lᴰ≈Lᴹ : ∀ dfa → Lᴰ dfa ≈ Lᴰ (minimise dfa)
  Lᴰ≈Lᴹ dfa = IsEquivalence.trans ≈-isEquiv (Remove-Inaccessible-States-Proof.Lᴰ≈Lᴿ dfa) (Quotient-Construction-Proof.Lᴿ≈Lᴹ dfa)



All-Reachable-States : DFA → Set
All-Reachable-States dfa = ∀ q → Reachable q
  where
    open DFA dfa
    open DFA-Properties dfa
    open Remove-Inaccessible-States dfa


Irreducible : DFA → Set
Irreducible dfa = ∀ p q → ¬ p ≋ q → p ≠ q
  where
    open DFA dfa
    open DFA-Properties dfa
    open Quotient-Construct dfa


Minimal : DFA → Set
Minimal dfa = All-Reachable-States dfa × Irreducible dfa


{-
-- Now, we have to prove that Minimal D cannot be collapsed further
Minimal : ∀ dfa → Set
Minimal dfa = (p q : Q₁) → p ∼ q → p ≋₁ q
  where
    mdfa : DFA
    mdfa = quotient-construction dfa
    open DFA mdfa renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; _≋_ to _≋₁_ ; ≋-isEquiv to ≋₁-isEquiv ; δ-lem to δ₁-lem ; F-lem to F₁-lem)
    open DFA-Operations mdfa renaming (δ* to δ₁* ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_ ; δ₀-lem₁ to δ₀₁-lem₁)
    open DFA-Properties mdfa
    open Quot-Properties (DFA-Properties.quot mdfa)
-}


module Reachable-Proof (dfa : DFA) where
  rdfa : DFA
  rdfa = remove-inaccessible-states dfa

  open DFA dfa
  open DFA-Properties dfa
  open DFA-Operations dfa
  open Remove-Inaccessible-States dfa
  
  IsAllReachable : All-Reachable-States rdfa
  IsAllReachable (reach q (w , n , prf)) = w , (n , Remove-Inaccessible-States-Proof.lem₁ dfa q₀ w n q q₀-reach (w , n , prf) prf)


module Minimal-Proof (dfa : DFA) where
  --open DFA dfa
  --open DFA-Properties dfa
  --open DFA-Operations dfa
  --open Quot-Properties quot 

  rdfa : DFA
  rdfa = remove-inaccessible-states dfa

  open DFA rdfa
  open DFA-Operations rdfa
  open DFA-Properties rdfa
  open Quotient-Construct rdfa
  open Quot-Properties quot

  IsAllReachable-rdfa : All-Reachable-States rdfa
  IsAllReachable-rdfa = Reachable-Proof.IsAllReachable dfa

  mdfa : DFA
  mdfa = quotient-construction rdfa

  open DFA mdfa renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; _≋_ to _≋₁_ ; ≋-isEquiv to ≋₁-isEquiv ; F-lem to F₁-lem)
  open DFA-Operations mdfa renaming (δ* to δ₁* ; _⊢ᵏ_─_ to _⊢ᵏ₁_─_)
  open DFA-Properties mdfa
  open Remove-Inaccessible-States dfa renaming (Reachable to Reachable₁ ; reach to reach₁ ; Qᴿ to Qᴿ₁)
  open Quotient-Construct mdfa
    renaming (_≠_ to _≠₁_ ; quot to quot₁ ; _∼_ to _∼₁_ ; ∼-lem₁ to ∼-lem₁₁ ; ≠-lem to ≠-lem₁' ; ≠-lem₁ to ≠-lem₁₁' ; Dec-≠ to Dec-≠₁)
  
  reachable-lem₁ : ∀ p ps w n q qs
                   → (ps≈⟪p⟫ : ps ≈ᵈ ⟪ p ⟫)
                   → (qs≈⟪q⟫ : qs ≈ᵈ ⟪ q ⟫)
                   → (p , w) ⊢ᵏ n ─ (q , [])
                   → (class ps (p , ps≈⟪p⟫) , w) ⊢ᵏ₁ n ─ (class qs (q , qs≈⟪q⟫) , [])
  reachable-lem₁ p ps .[] zero   q qs ps≈⟪p⟫ qs≈⟪q⟫ (p≋q , refl) = ∼-lem₁ p≋q , refl
  reachable-lem₁ p ps ._ (suc n) q qs ps≈⟪p⟫ qs≈⟪q⟫ (p₁ , a , u , refl , (refl , prf₁) , prf₂)
    = class (⟪ p₁ ⟫) (p₁ , IsEquivalence.refl ≈ᵈ-isEquiv)
      , a , u , refl , (refl , ∼-lem₁ prf₁)
      , reachable-lem₁ p₁ (⟪ p₁ ⟫) u n q qs (IsEquivalence.refl ≈ᵈ-isEquiv) qs≈⟪q⟫ prf₂

  IsAllReachable-mdfa : All-Reachable-States mdfa
  IsAllReachable-mdfa (class qs (q , qs≈⟪q⟫))
    = let (w , n , prf) = IsAllReachable-rdfa q
      in (w , n , reachable-lem₁ q₀ (⟪ q₀ ⟫) w n q qs (IsEquivalence.refl ≈ᵈ-isEquiv) qs≈⟪q⟫ prf)

  irreducible-lem₂ : ∀ {p ps q qs}
                     → (ps≈⟪p⟫ : ps ≈ᵈ ⟪ p ⟫)
                     → (qs≈⟪q⟫ : qs ≈ᵈ ⟪ q ⟫)
                     → p ≠ q
                     → (class ps (p , ps≈⟪p⟫)) ≠₁ (class qs (q , qs≈⟪q⟫))
  irreducible-lem₂ {p} {ps} {q} {qs} ps≈⟪p⟫ qs≈⟪q⟫ (w , inj₁ (prf₁ , prf₂))
    = let aa = Quotient-Construction-Proof.lem₂ dfa ps p w ps≈⟪p⟫ in
      let bb = Quotient-Construction-Proof.lem₂ dfa qs q w qs≈⟪q⟫ in
      w , inj₁ (F₁-lem {class ⟪ δ* p w ⟫ (δ* p w , IsEquivalence.refl ≈ᵈ-isEquiv)} {δ₁* (class ps (p , ps≈⟪p⟫)) w}
                       (IsEquivalence.sym ≋₁-isEquiv {δ₁* (class ps (p , ps≈⟪p⟫)) w} {class ⟪ δ* p w ⟫ (δ* p w , IsEquivalence.refl ≈ᵈ-isEquiv)} aa) prf₁
               , (λ prf →
                      prf₂
                      (F₁-lem {δ₁* (class qs (q , qs≈⟪q⟫)) w}
                       {class ⟪ δ* q w ⟫ (δ* q w , IsEquivalence.refl ≈ᵈ-isEquiv)} bb
                       prf)))
  irreducible-lem₂ {p} {ps} {q} {qs} ps≈⟪p⟫ qs≈⟪q⟫ (w , inj₂ (prf₁ , prf₂))
    = let aa = Quotient-Construction-Proof.lem₂ dfa ps p w ps≈⟪p⟫ in
      let bb = Quotient-Construction-Proof.lem₂ dfa qs q w qs≈⟪q⟫ in
      w , inj₂ ((λ prf →
                      prf₁
                      (F₁-lem {δ₁* (class ps (p , ps≈⟪p⟫)) w}
                       {class ⟪ δ* p w ⟫ (δ* p w , IsEquivalence.refl ≈ᵈ-isEquiv)} aa
                       prf))
                 , F₁-lem {class ⟪ δ* q w ⟫ (δ* q w , IsEquivalence.refl ≈ᵈ-isEquiv)} {δ₁* (class qs (q , qs≈⟪q⟫)) w}
                       (IsEquivalence.sym ≋₁-isEquiv {δ₁* (class qs (q , qs≈⟪q⟫)) w} {class ⟪ δ* q w ⟫ (δ* q w , IsEquivalence.refl ≈ᵈ-isEquiv)} bb) prf₂)

  irreducible-lem₁ : ∀ {p ps q qs}
                     → (ps≈⟪p⟫ : ps ≈ᵈ ⟪ p ⟫)
                     → (qs≈⟪q⟫ : qs ≈ᵈ ⟪ q ⟫)
                     → ¬ (class ps (p , ps≈⟪p⟫)) ≋₁ (class qs (q , qs≈⟪q⟫))
                     → ¬ (p ∼ q)
  irreducible-lem₁ {p} {ps} {q} {qs} ps≈⟪p⟫ qs≈⟪q⟫ prf p∼q = prf p∼q

  IsIrreducible : Irreducible mdfa -- → ¬ p ≋ q → p ≠ q
  IsIrreducible (class ps (p , ps≈⟪p⟫)) (class qs (q , qs≈⟪q⟫)) ¬p≋q
    = let aa = irreducible-lem₁ ps≈⟪p⟫ qs≈⟪q⟫ ¬p≋q in
      let bb = proj₁ ≠-lem aa in
      irreducible-lem₂ ps≈⟪p⟫ qs≈⟪q⟫ bb

  IsMinimal : Minimal mdfa
  IsMinimal = IsAllReachable-mdfa , IsIrreducible


IsMinimal : ∀ dfa → Minimal (minimise dfa)
IsMinimal dfa = Minimal-Proof.IsMinimal dfa


{-

module Minimal-Proof (dfa : DFA) where
  open DFA dfa
  open DFA-Operations dfa
  open DFA-Properties dfa
  open Quot-Properties quot

  mdfa₁ : DFA
  mdfa₁ = minimise dfa
  open DFA mdfa₁ renaming (Q to Q₁ ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; _≋_ to _≋₁_ ; ≋-isEquiv to ≋₁-isEquiv ; F-lem to F₁-lem)
  open DFA-Operations mdfa₁ renaming (δ* to δ₁*)
  open DFA-Properties mdfa₁ renaming (Reachable to Reachable₁ ; quot to quot₁ ; reach to reach₁ ; Qᴿ to Qᴿ₁ ; _∼_ to _∼₁_)
  open Quot-Properties quot₁ renaming (class to class₁ ; ⟪_⟫ to ⟪_⟫₁)

  mdfa₂ : DFA
  mdfa₂ = quotient-construction mdfa₁
  open DFA mdfa₂ renaming (Q to Q₂ ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; _≋_ to _≋₂_ ; ≋-isEquiv to ≋₂-isEquiv ; F-lem to F₂-lem)
  open DFA-Operations mdfa₂ renaming (δ* to δ₂*)
  open DFA-Properties mdfa₂ renaming (Reachable to Reachable₂ ; quot to quot₂ ; reach to reach₂ ; Qᴿ to Qᴿ₂ ; _∼_ to _∼₂_)
  open Quot-Properties quot₂ renaming (class to class₂ ; ⟪_⟫ to ⟪_⟫₂)

  lem : ∀ qs q w
        → (qs≈⟪q⟫ : qs ≈ᵈ ⟪ q ⟫₁)
        → δ₂* (class₁ qs (q , qs≈⟪q⟫)) w ≋₂ class₁ ⟪ δ₁* q w ⟫₁ (δ₁* q w , IsEquivalence.refl ≈ᵈ-isEquiv)
  lem qs q []      ⟪q⟫≈qs = ⟪q⟫≈qs
  lem qs q (a ∷ w) ⟪q⟫≈qs = lem (⟪ δ₁ q a ⟫₁) (δ₁ q a) w (IsEquivalence.refl ≈ᵈ-isEquiv)

  lem' : ∀ {q}
         → q ∈ᵈ F₁ ⇔ class₁ (⟪ q ⟫₁) (q , IsEquivalence.refl ≈ᵈ-isEquiv) ∈ᵈ F₂
  lem' = (λ prf → prf) , (λ prf → prf)

  IsMinimal : Minimal mdfa₁
  IsMinimal (class₁ ps (p , ps≈⟪p⟫)) (class₁ qs (q , qs≈⟪q⟫)) ⟪p⟫∼⟪q⟫
    = let lem₁ : ∀ w → (δ₂* (class₁ ps (p , ps≈⟪p⟫)) w) ∈ᵈ F₂ ⇔ (δ₂* (class₁ qs (q , qs≈⟪q⟫)) w) ∈ᵈ F₂
          lem₁ = ⟪p⟫∼⟪q⟫ in
      let lem₂ : ∀ w → (δ₂* (class₁ ps (p , ps≈⟪p⟫)) w) ∈ᵈ F₂ ⇔ class₁ ⟪ δ₁* p w ⟫₁ (δ₁* p w , IsEquivalence.refl ≈ᵈ-isEquiv) ∈ᵈ F₂
          lem₂ w = (λ prf → F₂-lem (lem ps p w ps≈⟪p⟫) prf) , (λ prf → F₂-lem (IsEquivalence.sym ≋₂-isEquiv (lem ps p w ps≈⟪p⟫)) prf) in
      let lem₃ : ∀ w → (δ₂* (class₁ qs (q , qs≈⟪q⟫)) w) ∈ᵈ F₂ ⇔ class₁ ⟪ δ₁* q w ⟫₁ (δ₁* q w , IsEquivalence.refl ≈ᵈ-isEquiv) ∈ᵈ F₂
          lem₃ w = (λ prf → F₂-lem (lem qs q w qs≈⟪q⟫) prf) , (λ prf → F₂-lem (IsEquivalence.sym ≋₂-isEquiv (lem qs q w qs≈⟪q⟫)) prf) in
      let lem₄ : ∀ w → class₁ ⟪ δ₁* p w ⟫₁ (δ₁* p w , IsEquivalence.refl ≈ᵈ-isEquiv) ∈ᵈ F₂ ⇔ class₁ ⟪ δ₁* q w ⟫₁ (δ₁* q w , IsEquivalence.refl ≈ᵈ-isEquiv) ∈ᵈ F₂
          lem₄ w = (λ prf → proj₁ (lem₃ w) (proj₁ (lem₁ w) (proj₂ (lem₂ w) prf))) , (λ prf → proj₁ (lem₂ w) (proj₂ (lem₁ w) (proj₂ (lem₃ w) prf))) in
      let lem₅ : ∀ w → δ₁* p w ∈ᵈ F₁ ⇔ δ₁* q w ∈ᵈ F₁
          lem₅ w = (λ prf → proj₂ (lem' {δ₁* q w}) (proj₁ (lem₄ w) (proj₁ (lem' {δ₁* p w}) prf)))
                 , (λ prf → proj₂ (lem' {δ₁* p w}) (proj₂ (lem₄ w) (proj₁ (lem' {δ₁* q w}) prf))) in
      let lem₆ : p ∼₁ q
          lem₆ = lem₅ in
      let lem₇ : ⟪ p ⟫₁ ≈ᵈ ⟪ q ⟫₁
          lem₇ = proj₁ (Quotient-Construct.p∼q⇔⟪p⟫≈⟪q⟫ mdfa₁) lem₆ in
      IsEquivalence.trans ≈ᵈ-isEquiv (IsEquivalence.trans ≈ᵈ-isEquiv ps≈⟪p⟫ lem₇) (IsEquivalence.sym ≈ᵈ-isEquiv qs≈⟪q⟫)
-}
