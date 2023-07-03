{-
  Here the translation from regular expressions to ε-NFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung
  Version 15-03-2016
-}
open import Util
module Translation.RegExp-eNFA (Σ : Set)(dec : DecEq Σ) where

open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Sum hiding (map)
open import Data.Nat renaming (_≟_ to _≟N_) 
open import Data.Vec hiding (init)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ⱽ_) hiding (_∉_)
open import Data.Vec.Relation.Unary.Any as AnyV using (here; there)  
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_ ; _∈?_ to _∈ᵈ?_ ; Ø to ø ; _⋃_ to _⋃ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ ; _⊆_ to _⊆ᵈ_ ; _⊇_ to _⊇ᵈ_ ; _≈_ to _≈ᵈ_ ; ≈-isEquiv to ≈ᵈ-isEquiv)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)
open import Language Σ dec hiding (⟦_⟧)
open import RegularExpression Σ dec 
open import eNFA Σ dec
open import State


-- translate a Regular expression to a NFA with ε-step
regexToε-NFA : RegExp → ε-NFA
regexToε-NFA Ø =
  record { Q = Q ; Q? = DecEq-Ø ; δ = δ ; q₀ = init ; F = ø ; ∀qEq = ∀qEq ; It = Ø-Vec ; ∣Q∣-1 = zero ; ∀q∈It = ∀q∈It ; unique = unique }
    where
      Q : Set
      Q = Ø-State
      δ : Q → Σᵉ → DecSubset Q
      δ init E init = true
      δ _    _ _    = false
      ∀qEq : ∀ q → q ∈ᵈ δ q E
      ∀qEq init = refl
      ∀q∈It : ∀ q → q ∈ⱽ Ø-Vec
      ∀q∈It init = here refl
      unique : Unique Ø-Vec
      unique = unique-Ø
regexToε-NFA ε =
  record { Q = Q ; Q? = DecEq-ε ; δ = δ ; q₀ = init ; F = F ; ∀qEq = ∀qEq ; It = ε-Vec ; ∣Q∣-1 = zero ; ∀q∈It = ∀q∈It ; unique = unique }
    where
      Q : Set
      Q = ε-State
      δ : Q → Σᵉ → DecSubset Q
      δ init E     init = true
      δ init (α a) init = false
      F : DecSubset Q
      F init  = true
      ∀qEq : ∀ q → q ∈ᵈ δ q E
      ∀qEq init = refl
      ∀q∈It : ∀ q → (q ∈ⱽ ε-Vec)
      ∀q∈It init = here refl
      unique : Unique ε-Vec
      unique = unique-ε
regexToε-NFA (σ a) =
  record { Q = Q ; Q? = DecEq-σ ; δ = δ ; q₀ = init ; F = F ; ∀qEq = ∀qEq ; It = σ-Vec ; ∣Q∣-1 = 1 ; ∀q∈It = ∀q∈It ; unique = unique }
    where
      Q : Set
      Q = σ-State
      δ : Q → Σᵉ → DecSubset Q
      δ init   E     init   = true
      δ init   (α b) accept = decEqToBool dec a b
      δ accept E     accept = true
      δ _      _     _      = false
      F : DecSubset Q
      F init   = false
      F accept = true
      ∀qEq : ∀ q → q ∈ᵈ δ q E
      ∀qEq init = refl
      ∀qEq accept = refl
      ∀q∈It : ∀ q → (q ∈ⱽ σ-Vec)
      ∀q∈It init   = here refl
      ∀q∈It accept = there (here refl)
      unique : Unique σ-Vec
      unique = unique-σ
regexToε-NFA (e₁ ∣ e₂) =
  record { Q = Q ; Q? = DecEq-⊍ Q₁? Q₂? ; δ = δ ; q₀ = init ; F = F ; ∀qEq = ∀qEq ; It = ⊍-Vec It₁ It₂ ; ∣Q∣-1 = suc (∣Q∣-1₁ + suc ∣Q∣-1₂) ; ∀q∈It = ∀q∈It ; unique = unique }
    where
      open ε-NFA (regexToε-NFA e₁)
        renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; ∀qEq to ∀qEq₁ ; It to It₁ ; ∣Q∣-1 to ∣Q∣-1₁ ; ∀q∈It to ∀q∈It₁ ; unique to unique₁)
      open ε-NFA (regexToε-NFA e₂)
        renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; ∀qEq to ∀qEq₂ ; It to It₂ ; ∣Q∣-1 to ∣Q∣-1₂ ; ∀q∈It to ∀q∈It₂ ; unique to unique₂)
      Q : Set
      Q = Q₁ ⊍ Q₂
      δ : Q → Σᵉ → DecSubset Q
      δ init      E init       = true
      δ init      E (⊍inj₁ q)  = decEqToBool Q₁? q q₀₁
      δ init      E (⊍inj₂ q)  = decEqToBool Q₂? q q₀₂
      δ (⊍inj₁ q) a (⊍inj₁ q') = q' ∈ᵈ? δ₁ q a
      δ (⊍inj₂ q) a (⊍inj₂ q') = q' ∈ᵈ? δ₂ q a
      δ _         _ _          = false
      F : DecSubset Q
      F init      = false
      F (⊍inj₁ q) = q ∈ᵈ? F₁
      F (⊍inj₂ q) = q ∈ᵈ? F₂
      ∀qEq : ∀ q → q ∈ᵈ δ q E
      ∀qEq init = refl
      ∀qEq (⊍inj₁ q) = ∀qEq₁ q
      ∀qEq (⊍inj₂ q) = ∀qEq₂ q
      ∀q∈It : ∀ q → q ∈ⱽ ⊍-Vec It₁ It₂
      ∀q∈It init      = here refl
      ∀q∈It (⊍inj₁ q) = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⊍ Q₁? Q₂?) (⊍inj₁ q) (map ⊍inj₁ It₁) (map ⊍inj₂ It₂) in
                         let prf₂ = Subset.VectorRep.∈-lem₂ Q₁? (DecEq-⊍ Q₁? Q₂?) ⊍inj₁ q It₁ (∀q∈It₁ q) in there (prf₁ (inj₁ prf₂))
      ∀q∈It (⊍inj₂ q) = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⊍ Q₁? Q₂?) (⊍inj₂ q) (map ⊍inj₁ It₁) (map ⊍inj₂ It₂) in
                         let prf₂ = Subset.VectorRep.∈-lem₂ Q₂? (DecEq-⊍ Q₁? Q₂?) ⊍inj₂ q It₂ (∀q∈It₂ q) in there (prf₁ (inj₂ prf₂))
      unique : Unique (⊍-Vec It₁ It₂)
      unique = unique-⊍ It₁ It₂ unique₁ unique₂
      
regexToε-NFA (e₁ ∙ e₂) =
  record { Q = Q ; Q? = DecEq-⍟ Q₁? Q₂? ; δ = δ ; q₀ = ⍟inj₁ q₀₁ ; F = F ; ∀qEq = ∀qEq ; It = ⍟-Vec It₁ It₂ ; ∣Q∣-1 = _ ; ∀q∈It = ∀q∈It ; unique = unique }
    where
      open ε-NFA (regexToε-NFA e₁)
        renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; ∀qEq to ∀qEq₁ ; It to It₁ ; ∀q∈It to ∀q∈It₁ ; unique to unique₁)
      open ε-NFA (regexToε-NFA e₂)
        renaming (Q to Q₂ ; Q? to Q₂? ; δ to δ₂ ; q₀ to q₀₂ ; F to F₂ ; ∀qEq to ∀qEq₂ ; It to It₂ ; ∀q∈It to ∀q∈It₂ ; unique to unique₂)
      Q : Set
      Q = Q₁ ⍟ Q₂
      δ : Q → Σᵉ → DecSubset Q
      δ (⍟inj₁ q) a (⍟inj₁ q') = q' ∈ᵈ? δ₁ q a
      δ (⍟inj₁ q) E mid        = q  ∈ᵈ? F₁
      δ (⍟inj₂ q) a (⍟inj₂ q') = q' ∈ᵈ? δ₂ q a
      δ mid       E mid        = true
      δ mid       E (⍟inj₂ q)  = decEqToBool Q₂? q q₀₂
      δ _         _ _ = false  
      F : DecSubset Q
      F (⍟inj₁ q) = false
      F mid       = false
      F (⍟inj₂ q) = q ∈ᵈ? F₂
      ∀qEq : ∀ q → q ∈ᵈ δ q E
      ∀qEq mid = refl
      ∀qEq (⍟inj₁ q) = ∀qEq₁ q
      ∀qEq (⍟inj₂ q) = ∀qEq₂ q
      ∀q∈It : ∀ q → q ∈ⱽ ⍟-Vec It₁ It₂
      ∀q∈It mid       = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⍟ Q₁? Q₂?) mid (map ⍟inj₁ It₁) (mid ∷ map ⍟inj₂ It₂) in
                         prf₁ (inj₂ (here refl))
      ∀q∈It (⍟inj₁ q) = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⍟ Q₁? Q₂?) (⍟inj₁ q) (map ⍟inj₁ It₁) (mid ∷ map ⍟inj₂ It₂) in
                         let prf₂ = Subset.VectorRep.∈-lem₂ Q₁? (DecEq-⍟ Q₁? Q₂?) ⍟inj₁ q It₁ (∀q∈It₁ q) in prf₁ (inj₁ prf₂)
      ∀q∈It (⍟inj₂ q) = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⍟ Q₁? Q₂?) (⍟inj₂ q) (map ⍟inj₁ It₁) (mid ∷ map ⍟inj₂ It₂) in
                         let prf₂ = Subset.VectorRep.∈-lem₂ Q₂? (DecEq-⍟ Q₁? Q₂?) ⍟inj₂ q It₂ (∀q∈It₂ q) in prf₁ (inj₂ (there prf₂))
      unique : Unique (⍟-Vec It₁ It₂)
      unique = unique-⍟ It₁ It₂ unique₁ unique₂
      
regexToε-NFA (e *) =
  record { Q = Q ; Q? = DecEq-* Q₁? ; δ = δ ; q₀ = init ; F = F ; ∀qEq = ∀qEq ; It = *-Vec It₁ ; ∣Q∣-1 = _ ; ∀q∈It = ∀q∈It ; unique = unique }
    where
      open ε-NFA (regexToε-NFA e)
        renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁ ; ∀qEq to ∀qEq₁ ; It to It₁ ; ∀q∈It to ∀q∈It₁ ; unique to unique₁)
      Q : Set
      Q = Q₁ *-State
      δ : Q → Σᵉ → DecSubset Q
      δ init    E     init     = true
      δ init    E     (inj q)  = decEqToBool Q₁? q q₀₁
      δ (inj q) E     (inj q') = q' ∈ᵈ? δ₁ q E ∨ (q ∈ᵈ? F₁ ∧ decEqToBool Q₁? q' q₀₁)
      δ (inj q) (α a) (inj q') = q' ∈ᵈ? δ₁ q (α a)
      δ _       _     _        = false
      F : DecSubset Q
      F init    = true
      F (inj q) = q ∈ᵈ? F₁
      ∀qEq : ∀ q → q ∈ᵈ δ q E
      ∀qEq init = refl
      ∀qEq (inj q) = Bool-lem₆ _ _ (∀qEq₁ q)
      ∀q∈It : ∀ q → q ∈ⱽ *-Vec It₁
      ∀q∈It init    = here refl
      ∀q∈It (inj q) = there (Subset.VectorRep.∈-lem₂ Q₁? (DecEq-* Q₁?) inj q It₁ (∀q∈It₁ q))
      unique : Unique (*-Vec It₁)
      unique = unique-* It₁ unique₁
