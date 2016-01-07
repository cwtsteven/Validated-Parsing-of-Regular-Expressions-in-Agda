{-
  Here the Language and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 0.2: Set of Strings
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 9-12-2015
-}

module Language (Σ : Set) where

open import Level renaming (zero to lzero ; suc to lsuc ; _⊔_ to _⊔ˡ_)
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Unit
open import Data.Nat

open import Util
open import Subset renaming (Ø to ø ; ⟦_⟧ to ⟦_⟧₁ ; _⋃_ to _⊎_)

open ≡-Reasoning

-- Set of strings over Σ
-- section 0.2.2: Languages
Σ* : Set
Σ* = List Σ

-- Language as a subset of Σ*
-- section 0.2.2: Languages
Language : Set₁
Language = Subset Σ*

-- Null set
Ø : Language
Ø = ø

-- Set of empty string
⟦ε⟧ : Language
⟦ε⟧ = ⟦ [] ⟧₁

-- Set of single alphabet
⟦_⟧ : Σ → Language
⟦ a ⟧ = ⟦ a ∷ [] ⟧₁


{- Here we define the operations on language -}

-- Union
-- section 0.2.3: Operations on Languages
infix 11 _⋃_
_⋃_ : Language → Language → Language
as ⋃ bs = as ⊎ bs

-- Concatenation
-- section 0.2.3: Operations on Languages
infix 12 _•_
_•_ : Language → Language → Language
L₁ • L₂ = λ w → Σ[ u ∈ Σ* ] Σ[ v ∈ Σ* ] (u ∈ L₁ × v ∈ L₂ × w ≡ u ++ v)

-- Closure
-- section 0.2.3: Operations on Languages
infix 6 _^_
_^_ : Language → ℕ → Language
L ^ zero    = ⟦ε⟧
L ^ (suc n) = L • (L ^ n)

infix 13 _⋆
_⋆ : Language → Language
L ⋆ = λ w → Σ[ n ∈ ℕ ] w ∈ (L ^ n)


{- Here we define the set of alphabet containing ε -}

-- Set of alphabet with ε
data Σᵉ : Set where
 E : Σᵉ
 α : Σ → Σᵉ

-- Set of strings over Σᵉ
Σᵉ* : Set
Σᵉ* = List Σᵉ

-- Transform a word over Σ to a word over Σᵉ
toΣᵉ* : Σ* → Σᵉ*
toΣᵉ* = Data.List.map α

-- Transform a word over Σᵉ to a word over Σ*
toΣ* : Σᵉ* → Σ*
toΣ* []         = []
toΣ* (E   ∷ xs) = toΣ* xs
toΣ* (α a ∷ xs) = a ∷ toΣ* xs

-- w ≡ u ++ v ⊢ toΣᵉ* w ≡ toΣᵉ* u ++ toΣᵉ* v
Σᵉ*-lem₁ : ∀ {w u v}
           → w ≡ u ++ v
           → toΣᵉ* w ≡ toΣᵉ* u ++ toΣᵉ* v
Σᵉ*-lem₁ {w} {u} {v} w≡uv
  = begin
    toΣᵉ* w             ≡⟨ cong toΣᵉ* w≡uv ⟩
    toΣᵉ* (u ++ v)      ≡⟨ List-lem₃ α u v ⟩
    toΣᵉ* u ++ toΣᵉ* v
    ∎

Σᵉ*-lem₁' : ∀ {wᵉ uᵉ vᵉ}
            → wᵉ ≡ uᵉ ++ vᵉ
            → toΣ* wᵉ ≡ toΣ* uᵉ ++ toΣ* vᵉ
Σᵉ*-lem₁' = undefined 

-- toΣᵉ* w ≡ [] ⊢ w ≡ []
Σᵉ*-lem₂ : ∀ {w}
           → toΣᵉ* w ≡ []
           → w ≡ []
Σᵉ*-lem₂ {[]}       refl = refl
Σᵉ*-lem₂ {(x ∷ xs)} ()

-- w ≡ toΣ* (toΣᵉ* w)
Σᵉ*-lem₃ : ∀ w
           → w ≡ toΣ* (toΣᵉ* w)
Σᵉ*-lem₃ []       = refl
Σᵉ*-lem₃ (x ∷ xs) = cong (λ w → x ∷ w) (Σᵉ*-lem₃ xs)

-- toΣ* (E ∷ w) ≡ toΣ* w
Σᵉ*-lem₄ : ∀ w
           → toΣ* (E ∷ w) ≡ toΣ* w
Σᵉ*-lem₄ w = refl

Σᵉ*-lem₅ : ∀ {x y xs b u}
           → x ∷ y ∷ xs ≡ toΣ* (α b ∷ u)
           → y ∷ xs ≡ toΣ* u
Σᵉ*-lem₅ {x} {y} {xs} {b} {u} prf = cong tail prf

Σᵉ*-lem₆ : ∀ {xs ys}
           → toΣ* xs ++ toΣ* ys ≡ toΣ* (xs ++ ys)
Σᵉ*-lem₆ {[]}       {ys} = refl   
Σᵉ*-lem₆ {α a ∷ xs} {ys} = cong (λ xs → a ∷ xs) (Σᵉ*-lem₆ {xs} {ys})
Σᵉ*-lem₆ {E   ∷ xs} {ys} = Σᵉ*-lem₆ {xs} {ys}

Σᵉ*-lem₇ : ∀ {w}
           → toΣ* (w ∷ʳ E) ≡ toΣ* w
Σᵉ*-lem₇ {[]}       = refl
Σᵉ*-lem₇ {α a ∷ xs} = cong (λ xs → a ∷ xs) (Σᵉ*-lem₇ {xs})
Σᵉ*-lem₇ {E   ∷ xs} = Σᵉ*-lem₇ {xs}
                    

-- Decidable Equality of Σᵉ
DecEq-Σᵉ : DecEq Σ → DecEq Σᵉ
DecEq-Σᵉ dec E     E      = yes refl
DecEq-Σᵉ dec E     (α  _) = no (λ ())
DecEq-Σᵉ dec (α a) E      = no (λ ())
DecEq-Σᵉ dec (α a) (α  b) with dec a b
DecEq-Σᵉ dec (α a) (α .a) | yes refl = yes refl
DecEq-Σᵉ dec (α a) (α  b) | no ¬a≡b  = no  (λ p → ¬σa≡σb ¬a≡b p)
 where
  lem : {a b : Σ} → α a ≡ α b → a ≡ b
  lem refl = refl
  ¬σa≡σb : ¬ (a ≡ b) → ¬ (α a ≡ α b)
  ¬σa≡σb ¬a≡b σa≡σb = ¬a≡b (lem σa≡σb)
