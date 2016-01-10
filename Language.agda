{-
  Here the Language and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 0.2: Set of Strings
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 07-01-2016
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
infix 11 _^_
_^_ : Language → ℕ → Language
L ^ zero    = ⟦ε⟧
L ^ (suc n) = L • (L ^ n)

infix 13 _⋆
_⋆ : Language → Language
L ⋆ = λ w → Σ[ n ∈ ℕ ] w ∈ L ^ n


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

Σᵉ*-lem₁ : ∀ {w u}
           → toΣ* w ++ toΣ* u ≡ toΣ* (w ++ u)
Σᵉ*-lem₁ {[]}       {ys} = refl   
Σᵉ*-lem₁ {α a ∷ xs} {ys} = cong (λ xs → a ∷ xs) (Σᵉ*-lem₁ {xs} {ys})
Σᵉ*-lem₁ {E   ∷ xs} {ys} = Σᵉ*-lem₁ {xs} {ys}


Σᵉ*-lem₂ : ∀ {w}
           → toΣ* (w ∷ʳ E) ≡ toΣ* w
Σᵉ*-lem₂ {[]}       = refl
Σᵉ*-lem₂ {α a ∷ xs} = cong (λ xs → a ∷ xs) (Σᵉ*-lem₂ {xs})
Σᵉ*-lem₂ {E   ∷ xs} = Σᵉ*-lem₂ {xs}

Σᵉ*-lem₃ : ∀ w u uᵉ v vᵉ vᵉ₁
           → w ≡ u ++ v
           → u ≡ toΣ* uᵉ
           → v ≡ toΣ* vᵉ
           → vᵉ ≡ E ∷ vᵉ₁
           → w ≡ toΣ* (uᵉ ++ E ∷ vᵉ₁)
Σᵉ*-lem₃ w u uᵉ v vᵉ vᵉ₁ w≡uv u≡uᵉ v≡vᵉ vᵉ≡Evᵉ₁
  = begin
    w                         ≡⟨ w≡uv ⟩
    u ++ v                    ≡⟨ cong (λ u → u ++ v) u≡uᵉ ⟩
    toΣ* uᵉ ++ v              ≡⟨ cong (λ v → toΣ* uᵉ ++ v) v≡vᵉ ⟩
    toΣ* uᵉ ++ toΣ* vᵉ        ≡⟨ cong (λ v → toΣ* uᵉ ++ toΣ* v) vᵉ≡Evᵉ₁ ⟩
    toΣ* uᵉ ++ toΣ* (E ∷ vᵉ₁) ≡⟨ Σᵉ*-lem₁ {uᵉ} {E ∷ vᵉ₁} ⟩
    toΣ* (uᵉ ++ E ∷ vᵉ₁)
    ∎

Σᵉ*-lem₄ : ∀ wᵉ uᵉ vᵉ
           → wᵉ ≡ uᵉ ++ E ∷ vᵉ
           → toΣ* wᵉ ≡ toΣ* uᵉ ++ toΣ* vᵉ
Σᵉ*-lem₄ wᵉ uᵉ vᵉ wᵉ≡uv = begin
                          toΣ* wᵉ             ≡⟨ cong toΣ* wᵉ≡uv ⟩
                          toΣ* (uᵉ ++ E ∷ vᵉ) ≡⟨ sym (Σᵉ*-lem₁ {uᵉ} {E ∷ vᵉ}) ⟩
                          toΣ* uᵉ ++ toΣ* vᵉ
                          ∎

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
