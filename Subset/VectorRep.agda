open import Util
module Subset.VectorRep where

open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Vec
open import Data.Unit
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



any : {A : Set}{n : ℕ}(P : A → Set) → Vec A n → Set
any P []       = ⊥
any P (a ∷ as) = P a ⊎ any P as

any-lem₁ : {A : Set}{n : ℕ}(as : Vec A n) → ∀ P → any P as → Σ[ a ∈ A ] P a
any-lem₁ []       P    ()
any-lem₁ (a ∷ as) P (inj₁ Pa)    = a , Pa
any-lem₁ (a ∷ as) P (inj₂ apply) = any-lem₁ as P apply

any-lem₂ : {A : Set}{n : ℕ}(as : Vec A n) → ∀ P → Σ[ a ∈ A ] (P a × a ∈ as) → any P as
any-lem₂ []       P ( a , Pa , ())
any-lem₂ (a ∷ as) P (.a , Pa , here)       = inj₁ Pa
any-lem₂ (a ∷ as) P ( x , Pa , there a∈as) = inj₂ (any-lem₂ as P (x , Pa , a∈as))



all : {A : Set}{n : ℕ}(P : A → Set) → Vec A n → Set
all P []       = ⊤
all P (a ∷ as) = P a × all P as

all-lem₁ : {A : Set}{n : ℕ}(as : Vec A n) → ∀ P → all P as → (∀ a → a ∈ as → P a)
all-lem₁ []       P tt                    = λ a ()
all-lem₁ (a ∷ as) P (Pa , allas) .a  here = Pa
all-lem₁ (a ∷ as) P (Pa , allas)  a₁ (there a₁∈as) = all-lem₁ as P allas a₁ a₁∈as

all-lem₂ : {A : Set}{n : ℕ}(as : Vec A n) → ∀ P → (∀ a → P a) → all P as
all-lem₂ []       P ∀aPa = tt
all-lem₂ (a ∷ as) P ∀aPa = ∀aPa a , all-lem₂ as P ∀aPa

module Vec-Rep-Lemmas {A : Set}{n : ℕ}(dec : DecEq A)(It : Vec A n)(∀a∈It : ∀ a → a ∈ It) where

  Vec-any-lem₃ : ∀ P → Σ[ a ∈ A ] P a → any P It
  Vec-any-lem₃ P (a , Pa) = any-lem₂ It P (a , Pa , ∀a∈It a)

  Vec-any-lem₂ : ∀ P → any P It → Σ[ a ∈ A ] P a
  Vec-any-lem₂ P any = any-lem₁ It P any

  Vec-any-lem₁ : ∀ P → any P It ⇔ Σ[ a ∈ A ] P a
  Vec-any-lem₁ P = Vec-any-lem₂ P , Vec-any-lem₃ P

  Vec-any-lem₄ : ∀ P → ¬ (any P It) → ¬ (Σ[ a ∈ A ] P a)
  Vec-any-lem₄ P ¬any prf = ¬any (Vec-any-lem₃ P prf)

  Vec-all-lem₃ : ∀ P → (∀ a → P a) → all P It
  Vec-all-lem₃ P = all-lem₂ It P

  Vec-all-lem₂ : ∀ P → all P It → (∀ a → P a)
  Vec-all-lem₂ P all a = all-lem₁ It P all a (∀a∈It a)

  Vec-all-lem₁ : ∀ P → all P It ⇔ (∀ a → P a)
  Vec-all-lem₁ P = Vec-all-lem₂ P , Vec-all-lem₃ P

  Vec-all-lem₄ : ∀ P → ¬ (all P It) → ¬ (∀ a → P a)
  Vec-all-lem₄ P ¬allP ∀aPa = ¬allP (Vec-all-lem₃ P ∀aPa)

  module Powerset where
  
    data Sub A : Set where
      keep : A → Sub A
      kick : A → Sub A
  
    powerset : {A : Set} → Vec A n → Vec (Vec (Sub A) n) (2 ^ n)
    powerset = undefined

    --∀qs∈powerset : {A : Set} → 
