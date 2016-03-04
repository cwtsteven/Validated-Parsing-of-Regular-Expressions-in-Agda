{-
  Here the translation of a regular expression to a DFA is defined
  according to:
    the lecture notes written by Prof. Achim Jung 
    from The University of Birmingham, 
    School of Computer Science

  Steven Cheung 2015.
  Version 10-01-2016
-}
open import Util
module Translation (Σ : Set)(dec : DecEq Σ) where

--open import Level
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Sum hiding (map)
open import Data.Product hiding (Σ ; map)
open import Data.Unit
open import Data.Empty
open import Function
open import Data.Nat renaming (_≟_ to _≟N_) 
open import Data.Vec renaming (_∈_ to _∈ⱽ_) hiding (init)
open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_)

open import Subset.DecidableSubset renaming (Ø to ø ; _⋃_ to _⋃ᵈ_)
open import Language Σ dec hiding (⟦_⟧)
open import RegularExpression Σ dec 
open import eNFA Σ dec
open import NFA Σ dec
open import DFA Σ dec
open import State

open ≡-Reasoning


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
      ∀qEq : ∀ q → q ∈ δ q E
      ∀qEq init = refl
      ∀q∈It : ∀ q → q ∈ⱽ Ø-Vec
      ∀q∈It init = here
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
      ∀qEq : ∀ q → q ∈ δ q E
      ∀qEq init = refl
      ∀q∈It : ∀ q → (q ∈ⱽ ε-Vec)
      ∀q∈It init = here
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
      ∀qEq : ∀ q → q ∈ δ q E
      ∀qEq init = refl
      ∀qEq accept = refl
      ∀q∈It : ∀ q → (q ∈ⱽ σ-Vec)
      ∀q∈It init   = here
      ∀q∈It accept = there here
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
      δ (⊍inj₁ q) a (⊍inj₁ q') = q' ∈? δ₁ q a
      δ (⊍inj₂ q) a (⊍inj₂ q') = q' ∈? δ₂ q a
      δ _         _ _          = false
      F : DecSubset Q
      F init      = false
      F (⊍inj₁ q) = q ∈? F₁
      F (⊍inj₂ q) = q ∈? F₂
      ∀qEq : ∀ q → q ∈ δ q E
      ∀qEq init = refl
      ∀qEq (⊍inj₁ q) = ∀qEq₁ q
      ∀qEq (⊍inj₂ q) = ∀qEq₂ q
      ∀q∈It : ∀ q → q ∈ⱽ ⊍-Vec It₁ It₂
      ∀q∈It init      = here
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
      δ (⍟inj₁ q) a (⍟inj₁ q') = q' ∈? δ₁ q a
      δ (⍟inj₁ q) E mid        = q  ∈? F₁
      δ (⍟inj₂ q) a (⍟inj₂ q') = q' ∈? δ₂ q a
      δ mid       E mid        = true
      δ mid       E (⍟inj₂ q)  = decEqToBool Q₂? q q₀₂
      δ _         _ _ = false  
      F : DecSubset Q
      F (⍟inj₁ q) = false
      F mid       = false
      F (⍟inj₂ q) = q ∈? F₂
      ∀qEq : ∀ q → q ∈ δ q E
      ∀qEq mid = refl
      ∀qEq (⍟inj₁ q) = ∀qEq₁ q
      ∀qEq (⍟inj₂ q) = ∀qEq₂ q
      ∀q∈It : ∀ q → q ∈ⱽ ⍟-Vec It₁ It₂
      ∀q∈It mid       = let prf₁ = Subset.VectorRep.∈-lem₆ (DecEq-⍟ Q₁? Q₂?) mid (map ⍟inj₁ It₁) (mid ∷ map ⍟inj₂ It₂) in
                         prf₁ (inj₂ here)
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
      δ (inj q) E     (inj q') = q' ∈? δ₁ q E ∨ (q ∈? F₁ ∧ decEqToBool Q₁? q' q₀₁)
      δ (inj q) (α a) (inj q') = q' ∈? δ₁ q (α a)
      δ _       _     _        = false
      F : DecSubset Q
      F init    = true
      F (inj q) = q ∈? F₁
      ∀qEq : ∀ q → q ∈ δ q E
      ∀qEq init = refl
      ∀qEq (inj q) = Bool-lem₆ _ _ (∀qEq₁ q)
      ∀q∈It : ∀ q → q ∈ⱽ *-Vec It₁
      ∀q∈It init    = here
      ∀q∈It (inj q) = there (Subset.VectorRep.∈-lem₂ Q₁? (DecEq-* Q₁?) inj q It₁ (∀q∈It₁ q))
      unique : Unique (*-Vec It₁)
      unique = unique-* It₁ unique₁
   

-- remove ε-steps
remove-ε-step : ε-NFA → NFA
remove-ε-step nfa =
  record { Q = Q ; Q? = Q? ; δ = δ' ; q₀ = q₀ ; F = F' ; ∣Q∣-1 = _ ; It = It ; ∀q∈It = ∀q∈It ; unique = unique }
    where
      open ε-NFA nfa
      open ε-NFA-Operations nfa
      open ε-NFA-Properties nfa

      δ' : Q → Σ → DecSubset Q
      --     = { q' | q' ∈ δ q (α a) ∨ ∃p∈Q. q' ∈ δ p (α a) ∧ p ∈ ε-closure(q) }
      --     = λ q' → q' ∈ δ q (α a) ⊎ Σ[ p ∈ Q ] (q' ∈ δ p (α a) × p ∈ ε-closure q)
      δ' q a = λ q' → q' ∈? δ q (α a) ∨ ∃q⊢a-q'? (Dec-→ε*⊢ q a q')

      F' : DecSubset Q
      -- = { q | q ∈ F ∨ ∃p∈Q. p ∈ F ∧ p ∈ ε-closure(q) }
      -- = λ q → q ∈ F ⊎ Σ[ p ∈ Q ] (p ∈ F × p ∈ ε-closure q)
      F' = λ q → q ∈? F ∨ ∃q∈F? (Dec-→ε*∈F q)

--open import Data.Vec renaming (_∈_ to _∈ⱽ_)
--open import Subset.VectorRep renaming (_∈?_ to _∈ⱽ?_ ; Ø to Øⱽ)

-- determinise the NFA by powerset construction
powerset-construction : NFA → DFA
powerset-construction nfa =
  record { Q = Q' ; δ = δ' ; q₀ = q₀' ; F = F' ; _≋_ = _≈_ ; Dec-≋ = Decidable-≈.Dec-≈ {Q} {∣Q∣-1} Q? It ∀q∈It unique ; ≋-isEquiv = ≈-isEquiv ; F-lem = F-lem ; δ-lem = δ-lem ; Q? = undefined ; ∣Q∣-1 = undefined ; It = undefined ; ∀q∈It = undefined ; unique = undefined }
    where
      open NFA nfa
      open NFA-Operations nfa
      open NFA-Properties nfa
      open Vec-Rep {Q} {∣Q∣-1} Q? It ∀q∈It unique
      Q' : Set
      Q' = DecSubset Q
      
      δ' : Q' → Σ → Q'
      -- qs a = { q' | ∃q∈Q.q ∈ qs ∧ q' ∈ δ q a }
      -- qs a = λ q' → Σ[ q ∈ Q ] ( q ∈ qs × q' ∈ᵈ δ q a )
      δ' qs a q' with Dec-⊢ qs a q'
      ... | yes _ = true
      ... | no  _ = false
      
      q₀' : Q'
      q₀' = ⟦ q₀ ⟧ {{Q?}}
      
      F' : DecSubset Q'
      -- = { qs | ∃q∈Q. q ∈ qs ∧ q ∈ F }
      -- = λ qs → Σ[ q ∈ Q ] ( q ∈ qs × q ∈ F )
      F' qs with Dec-qs∈F qs
      ... | yes _ = true
      ... | no  _ = false

      

      δ-lem : ∀ {qs ps : Q'} a
              → qs ≈ ps
              → δ' qs a ≈ δ' ps a
      δ-lem {qs} {ps} a qs≈ps = δ-lem₁ , δ-lem₂
        where
          δ-lem₁ : δ' qs a ⊆ δ' ps a
          δ-lem₁ q q∈δqsa with q ∈? δ' ps a | inspect (δ' ps a) q
          δ-lem₁ q q∈δqsa | true  | [ q∈δpsa ] = refl
          δ-lem₁ q q∈δqsa | false | [ q∉δpsa ] with Dec-⊢ ps a q
          δ-lem₁ q q∈δqsa | false | [     () ] | yes _
          δ-lem₁ q q∈δqsa | false | [ q∉δpsa ] | no  ¬∃q with Dec-⊢ qs a q
          δ-lem₁ q q∈δqsa | false | [ q∉δpsa ] | no  ¬∃q | yes (q₁ , q₁∈qs , q∈δq₁a)
            = ⊥-elim (¬∃q (q₁ , proj₁ qs≈ps q₁ q₁∈qs , q∈δq₁a))
          δ-lem₁ q     () | false | [ q∉δpsa ] | no  ¬∃q | no  _
          δ-lem₂ : δ' qs a ⊇ δ' ps a
          δ-lem₂ q q∈δpsa with q ∈? δ' qs a | inspect (δ' qs a) q
          δ-lem₂ q q∈δpsa | true  | [ q∈δqsa ] = refl
          δ-lem₂ q q∈δpsa | false | [ q∉δqsa ] with Dec-⊢ qs a q
          δ-lem₂ q q∈δpsa | false | [     () ] | yes _
          δ-lem₂ q q∈δpsa | false | [ q∉δqsa ] | no  ¬∃q with Dec-⊢ ps a q
          δ-lem₂ q q∈δpsa | false | [ q∉δqsa ] | no  ¬∃q | yes (q₁ , q₁∈ps , q∈δq₁a)
            = ⊥-elim (¬∃q (q₁ , proj₂ qs≈ps q₁ q₁∈ps , q∈δq₁a))
          δ-lem₂ q     () | false | [ q∉δqsa ] | no  ¬∃q | no  _

      F-lem : ∀ {qs ps}
              → qs ≈ ps
              → qs ∈ F'
              → ps ∈ F'
      F-lem {qs} {ps} qs≈ps qs∈F with ps ∈? F' | inspect F' ps
      F-lem {qs} {ps} qs≈ps qs∈F | true  | [ ps∈F ] = refl
      F-lem {qs} {ps} qs≈ps qs∈F | false | [ ps∉F ] with Dec-qs∈F ps
      F-lem {qs} {ps} qs≈ps qs∈F | false | [   () ] | yes prf
      F-lem {qs} {ps} qs≈ps qs∈F | false | [ ps∉F ] | no  ¬∃p with Dec-qs∈F qs
      F-lem {qs} {ps} qs≈ps qs∈F | false | [ ps∉F ] | no  ¬∃p | yes (q , q∈qs , q∈F)
        = ⊥-elim (¬∃p (q , proj₁ qs≈ps q q∈qs , q∈F))
      F-lem {qs} {ps} qs≈ps   () | false | [ ps∉F ] | no  ¬∃p | no  _


minimise : (dfa : DFA) → Minimal dfa
minimise dfa = record { Qᴹ = {!!} ; ∀qAccess = {!!} ; δᴹ = {!!} ; q₀∈Qᴹ = {!!} ; Fᴹ = {!!} ; Fᴹ⊆Qᴹ = {!!} }
  where
    open DFA dfa
    open DFA-Properties dfa
    


-- translating a regular expression to a NFA w/o ε-step
regexToNFA : RegExp → NFA
regexToNFA = remove-ε-step ∘ regexToε-NFA


-- translating a regular expression to a DFA
regexToDFA : RegExp → DFA
regexToDFA = powerset-construction ∘ remove-ε-step ∘ regexToε-NFA


-- translating a regular expression to a MDFA
regexToMDFA : (r : RegExp) → Minimal (regexToDFA r)
regexToMDFA r = minimise (regexToDFA r)
