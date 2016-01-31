open import Util
module Subset.VectorRep where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Vec
open import Data.Empty

∈-lem₁ : {A : Set}(a x : A){n : ℕ} → (as : Vec A n) → a ∈ x ∷ as → ¬ a ∈ as → a ≡ x
∈-lem₁ x .x as here a∉as         = refl
∈-lem₁ a  x as (there a∈as) a∉as = ⊥-elim (a∉as a∈as)

infix 4 _∈?_
_∈?_ : {A : Set}(a : A){n : ℕ} → (as : Vec A n) → {{dec : DecEq A}} → Dec (a ∈ as)
(a ∈? [])        {{dec}} = no (λ ())
(a ∈? ( x ∷ as)) {{dec}} with dec a x
(a ∈? (.a ∷ as)) {{dec}} | yes refl = yes here
(a ∈? ( x ∷ as)) {{dec}} | no  _    with (a ∈? as) {{dec}}
(a ∈? ( x ∷ as)) {{dec}} | no  _    | yes a∈as = yes (there a∈as)
(a ∈? ( x ∷ as)) {{dec}} | no  a≢x  | no  a∉as = no (λ a∈xas →  a≢x (∈-lem₁ a x as a∈xas a∉as))


∈-lem₂ : {A B : Set}{n : ℕ}(decA : DecEq A)(decB : DecEq B)(f : A → B) → (a : A)(as : Vec A n) → (a ∈ as) → (f a ∈ map f as)
∈-lem₂ decA decB f a ._ here               = here
∈-lem₂ decA decB f a (y ∷ as) (there a∈as) = there (∈-lem₂ decA decB f a as a∈as)

∈-lem₃ : {A : Set}{n m : ℕ}(dec : DecEq A)(a : A)(as : Vec A n)(bs : Vec A m) → a ∈ as ++ bs → a ∈ as ⊎ a ∈ bs
∈-lem₃ dec a []        bs a∈asbs = inj₂ a∈asbs
∈-lem₃ dec x (.x ∷ as) bs here = inj₁ here
∈-lem₃ dec a ( x ∷ as) bs (there a∈asbs) with ∈-lem₃ dec a as bs a∈asbs
∈-lem₃ dec a ( x ∷ as) bs (there a∈asbs) | inj₁ a∈as = inj₁ (there a∈as)
∈-lem₃ dec a ( x ∷ as) bs (there a∈asbs) | inj₂ a∈bs = inj₂ a∈bs

∈-lem₄ : {A : Set}{n m : ℕ}(dec : DecEq A)(a : A)(as : Vec A n)(bs : Vec A m) → a ∈ as → a ∈ as ++ bs
∈-lem₄ dec x (.x ∷ as) bs here = here
∈-lem₄ dec a ( x ∷ as) bs (there a∈as) = there (∈-lem₄ dec a as bs a∈as)

∈-lem₅ : {A : Set}{n m : ℕ}(dec : DecEq A)(a : A)(as : Vec A n)(bs : Vec A m) → a ∈ bs → a ∈ as ++ bs
∈-lem₅ dec a []        bs a∈bs = a∈bs
∈-lem₅ dec a ( x ∷ as) bs a∈bs with dec a x
∈-lem₅ dec a (.a ∷ as) bs a∈bs | yes refl = here
∈-lem₅ dec a ( x ∷ as) bs a∈bs | no  _    = there (∈-lem₅ dec a as bs a∈bs)

∈-lem₆ : {A : Set}{n m : ℕ}(dec : DecEq A)(a : A)(as : Vec A n)(bs : Vec A m) → a ∈ as ⊎ a ∈ bs → a ∈ as ++ bs
∈-lem₆ dec a as bs (inj₁ a∈as) = ∈-lem₄ dec a as bs a∈as
∈-lem₆ dec a as bs (inj₂ a∈bs) = ∈-lem₅ dec a as bs a∈bs

apply : {A : Set}{n : ℕ}(P : A → Set) → Vec A n → Set
apply P []       = ⊥
apply P (a ∷ as) = P a ⊎ apply P as

apply-lem₁ : {A : Set}{n : ℕ}(as : Vec A n) → ∀ P → apply P as → Σ[ a ∈ A ] P a
apply-lem₁ []       P    ()
apply-lem₁ (a ∷ as) P (inj₁ Pa)    = a , Pa
apply-lem₁ (a ∷ as) P (inj₂ apply) = apply-lem₁ as P apply

apply-lem₂ : {A : Set}{n : ℕ}(as : Vec A n) → ∀ P → Σ[ a ∈ A ] (P a × a ∈ as) → apply P as
apply-lem₂ []       P (a , Pa , ())
apply-lem₂ (x ∷ as) P (.x , Pa , here)      = inj₁ Pa
apply-lem₂ (x ∷ as) P (a , Pa , there a∈as) = inj₂ (apply-lem₂ as P (a , Pa , a∈as))


module Vec-Rep-Lemmas {A : Set}{n : ℕ}(dec : DecEq A)(It : Vec A n)(∀a∈It : ∀ a → a ∈ It) where

  Vec-Rep-lem₃ : ∀ P → Σ[ a ∈ A ] P a → apply P It
  Vec-Rep-lem₃ P (a , Pa) = apply-lem₂ It P (a , Pa , ∀a∈It a)

  Vec-Rep-lem₂ : ∀ P → apply P It → Σ[ a ∈ A ] P a
  Vec-Rep-lem₂ P apply = apply-lem₁ It P apply

  Vec-Rep-lem₁ : ∀ P → apply P It ⇔ Σ[ a ∈ A ] P a
  Vec-Rep-lem₁ P = Vec-Rep-lem₂ P , Vec-Rep-lem₃ P

  Vec-Rep-lem₄ : ∀ P → ¬ (apply P It) → ¬ (Σ[ a ∈ A ] P a)
  Vec-Rep-lem₄ P ¬apply prf = ¬apply (Vec-Rep-lem₃ P prf)
