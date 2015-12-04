{-
  Here the Language and its operations are defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 0.2: Set of Strings
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 26-11-2015
-}

module Language (Σ : Set) where

open import Level renaming (zero to lzero ; suc to lsuc ; _⊔_ to _⊔ˡ_)
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (Σ)
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
Language = Subset Σ* {lzero}

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

Σᵉ*-lem₂ : ∀ {w}
           → toΣᵉ* w ≡ []
           → w ≡ []
Σᵉ*-lem₂ {[]}       refl = refl
Σᵉ*-lem₂ {(x ∷ xs)} ()
