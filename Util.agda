{-
  This module contains some miscellaneous definitions and proofs that will be used.

  Steven Cheung 2015.
  Version 26-11-2015
-}
module Util where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat

open ≡-Reasoning

postulate undefined : ∀ {α} → {A : Set α} → A


-- Decidable Equality
DecEq : (A : Set) → Set
DecEq A = (x y : A) → Dec (x ≡ y)


-- List lemma
++-assoc : {A : Set}(xs ys zs : List A)
           → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc [] ys zs       = refl
++-assoc (x ∷ xs) ys zs with xs ++ (ys ++ zs) | (xs ++ ys) ++ zs | ++-assoc xs ys zs
... | ws | .ws | refl = refl


List-lem₅ : {A : Set}{xs ys ys' zs : List A}
            → xs ≡ ys ++ zs
            → ys ≡ ys'
            → xs ≡ ys' ++ zs
List-lem₅ {A} {xs} {ys} {ys'} {zs} xs≡yszs ys≡ys'
  = begin
    xs        ≡⟨ xs≡yszs ⟩
    ys ++ zs  ≡⟨ cong (λ ys → ys ++ zs) ys≡ys' ⟩
    ys' ++ zs
    ∎

List-lem₄ : {A : Set}{xs xs' ys ys' zs : List A}
            → xs ≡ ys ++ zs
            → xs' ≡ ys' ++ zs
            → ys ≡ ys'
            → xs ≡ xs'
List-lem₄ {A} {xs} {xs'} {ys} {ys'} {zs} xs≡yszs xs'≡ys'zs ys≡ys'
  = begin
    xs        ≡⟨ List-lem₅ xs≡yszs ys≡ys' ⟩
    ys' ++ zs ≡⟨ sym xs'≡ys'zs ⟩
    xs'
    ∎

List-lem₃ : {A B : Set}(f : A → B)(xs ys : List A)
            → Data.List.map f (xs ++ ys) ≡ Data.List.map f xs ++ Data.List.map f ys
List-lem₃ f []       ys = refl
List-lem₃ f (x ∷ xs) ys = cong (λ xs → f x ∷ xs) (List-lem₃ f xs ys)


List-lem₂ : {A : Set}(xs : List A)
            → xs ++ [] ≡ xs
List-lem₂ []       = refl
List-lem₂ (x ∷ xs) = cong (_∷_ x) (List-lem₂ xs)


List-lem₁ : {A : Set}(y : A)(xs ys : List A)
            → xs ++ y ∷ ys ≡ (xs ∷ʳ y) ++ ys
List-lem₁ y xs ys
  = ++-assoc xs Data.List.[ y ] ys
