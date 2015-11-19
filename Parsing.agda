open import Util
module Parsing (Σ : Set) (dec : DecEq Σ) where

open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty

open import Subset renaming (Ø to ø)
open import RegularExpression Σ dec
open import Automata Σ dec

data _∥_ (A B : Set) : Set where
  init : A ∥ B
  ∥inj₁ : (a : A) → A ∥ B
  ∥inj₂ : (b : B) → A ∥ B

∥-lem₁ : {A B : Set}{q q' : A}{injq injq' : A ∥ B} → injq ≡ ∥inj₁ q → injq' ≡ ∥inj₁ q' → injq ≡ injq' → q ≡ q'
∥-lem₁ refl refl refl = refl

∥-lem₂ : {A B : Set}{q q' : A}{injq injq' : A ∥ B} → injq ≡ ∥inj₁ q → injq' ≡ ∥inj₁ q' → q ≢ q' → injq ≢ injq'
∥-lem₂ pr₁ pr₂ ¬q≡q' injq≡injq' = ¬q≡q' (∥-lem₁ pr₁ pr₂ injq≡injq')

∥-lem₃ : {A B : Set}{q q' : B}{injq injq' : A ∥ B} → injq ≡ ∥inj₂ q → injq' ≡ ∥inj₂ q' → injq ≡ injq' → q ≡ q'
∥-lem₃ refl refl refl = refl

∥-lem₄ : {A B : Set}{q q' : B}{injq injq' : A ∥ B} → injq ≡ ∥inj₂ q → injq' ≡ ∥inj₂ q' → q ≢ q' → injq ≢ injq'
∥-lem₄ pr₁ pr₂ ¬q≡q' injq≡injq' = ¬q≡q' (∥-lem₃ pr₁ pr₂ injq≡injq')

DecEq-∥ : {A B : Set} → DecEq A → DecEq B → DecEq (A ∥ B)
DecEq-∥ decA decB init init = yes refl
DecEq-∥ decA decB init (∥inj₁ _) = no (λ ())
DecEq-∥ decA decB init (∥inj₂ _) = no (λ ())
DecEq-∥ decA decB (∥inj₁ q) init = no (λ ())
DecEq-∥ decA decB (∥inj₁ q) (∥inj₁ q') with decA q q'
DecEq-∥ decA decB (∥inj₁ q) (∥inj₁ .q) | yes refl = yes refl
DecEq-∥ decA decB (∥inj₁ q) (∥inj₁ q') | no ¬q≡q' = no (∥-lem₂ refl refl ¬q≡q')
DecEq-∥ decA decB (∥inj₁ q) (∥inj₂ _) = no (λ ())
DecEq-∥ decA decB (∥inj₂ q) init = no (λ ())
DecEq-∥ decA decB (∥inj₂ q) (∥inj₂ q') with decB q q'
DecEq-∥ decA decB (∥inj₂ q) (∥inj₂ .q) | yes refl = yes refl
DecEq-∥ decA decB (∥inj₂ q) (∥inj₂ q') | no ¬q≡q' = no (∥-lem₄ refl refl ¬q≡q')
DecEq-∥ decA decB (∥inj₂ q) (∥inj₁ _) = no (λ ())

data _⍟_ (A B : Set) : Set where
 ⍟inj₁ : (a : A) → A ⍟ B
 mid   : A ⍟ B
 ⍟inj₂ : (b : B) → A ⍟ B
 
⍟-lem₁ : {A B : Set}{q q' : A}{injq injq' : A ⍟ B} → injq ≡ ⍟inj₁ q → injq' ≡ ⍟inj₁ q' → injq ≡ injq' → q ≡ q'
⍟-lem₁ refl refl refl = refl

⍟-lem₂ : {A B : Set}{q q' : A}{injq injq' : A ⍟ B} → injq ≡ ⍟inj₁ q → injq' ≡ ⍟inj₁ q' → q ≢ q' → injq ≢ injq'
⍟-lem₂ pr₁ pr₂ ¬q≡q' injq≡injq' = ¬q≡q' (⍟-lem₁ pr₁ pr₂ injq≡injq')

⍟-lem₃ : {A B : Set}{q q' : B}{injq injq' : A ⍟ B} → injq ≡ ⍟inj₂ q → injq' ≡ ⍟inj₂ q' → injq ≡ injq' → q ≡ q'
⍟-lem₃ refl refl refl = refl

⍟-lem₄ : {A B : Set}{q q' : B}{injq injq' : A ⍟ B} → injq ≡ ⍟inj₂ q → injq' ≡ ⍟inj₂ q' → q ≢ q' → injq ≢ injq'
⍟-lem₄ pr₁ pr₂ ¬q≡q' injq≡injq' = ¬q≡q' (⍟-lem₃ pr₁ pr₂ injq≡injq')

DecEq-⍟ : {A B : Set} → DecEq A → DecEq B → DecEq (A ⍟ B)
DecEq-⍟ decA decB (⍟inj₁ q) (⍟inj₁ q') with decA q q'
DecEq-⍟ decA decB (⍟inj₁ q) (⍟inj₁ .q) | yes refl = yes refl
DecEq-⍟ decA decB (⍟inj₁ q) (⍟inj₁ q') | no ¬q≡q' = no (⍟-lem₂ refl refl ¬q≡q')
DecEq-⍟ decA decB (⍟inj₁ q) (⍟inj₂ q') = no (λ ())
DecEq-⍟ decA decB (⍟inj₂ q) (⍟inj₂ q') with decB q q'
DecEq-⍟ decA decB (⍟inj₂ q) (⍟inj₂ .q) | yes refl = yes refl
DecEq-⍟ decA decB (⍟inj₂ q) (⍟inj₂ q') | no ¬q≡q' = no (⍟-lem₄ refl refl ¬q≡q')
DecEq-⍟ decA decB (⍟inj₂ q) (⍟inj₁ q') = no (λ ())
DecEq-⍟ decA decB mid mid = yes refl
DecEq-⍟ decA decB mid (⍟inj₁ q) = no (λ ())
DecEq-⍟ decA decB (⍟inj₁ q) mid = no (λ ())
DecEq-⍟ decA decB mid (⍟inj₂ q) = no (λ ())
DecEq-⍟ decA decB (⍟inj₂ q) mid = no (λ ())


data _*-State (A : Set) : Set where
 init : A *-State
 inj  : (a : A) → A *-State

*-lem₁ : {A : Set}{q q' : A} → inj q ≡ inj q' → q ≡ q'
*-lem₁ refl = refl

*-lem₂ : {A : Set}{q q' : A} → q ≢ q' → inj q ≢ inj q'
*-lem₂ ¬q≡q' injq≡q' = ¬q≡q' (*-lem₁ injq≡q')

DecEq-* : {A : Set} → DecEq A → DecEq (A *-State)
DecEq-* dec init init        = yes refl
DecEq-* dec init (inj _)     = no (λ ())
DecEq-* dec (inj q) (inj q') with dec q q'
DecEq-* dec (inj q) (inj .q) | yes refl = yes refl
DecEq-* dec (inj q) (inj q') | no ¬q≡q' = no (*-lem₂ ¬q≡q')
DecEq-* dec (inj _) init     = no (λ ())

data σ-State : Set where
 init   : σ-State
 accept : σ-State
 error  : σ-State

DecEq-σ : DecEq σ-State
DecEq-σ init init     = yes refl
DecEq-σ init accept   = no (λ ())
DecEq-σ init error    = no (λ ())
DecEq-σ accept accept = yes refl
DecEq-σ accept init   = no (λ ())
DecEq-σ accept error  = no (λ ())
DecEq-σ error error   = yes refl
DecEq-σ error init    = no (λ ())
DecEq-σ error accept  = no (λ ())

data ε-State : Set where
 init  : ε-State
 error : ε-State

DecEq-ε : DecEq ε-State
DecEq-ε init init   = yes refl
DecEq-ε init error  = no (λ ())
DecEq-ε error error = yes refl
DecEq-ε error init  = no (λ ())

data Ø-State : Set where
 init : Ø-State

DecEq-Ø : DecEq Ø-State
DecEq-Ø init init = yes refl


∣-2NFA : NFA → NFA → NFA
∣-2NFA nfa₁ nfa₂ = record { Q = Q' ; Q? = DecEq-∥ Q₁? Q₂? ; {-It = init ∷ (Data.List.map ∥inj₁ It₁) ++ (Data.List.map ∥inj₂ It₂) ;-} δ = δ' ; q₀ = init ; F = F' }
 where
  open NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; {-It to It₁ ;-} δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
  open NFA nfa₂ renaming (Q to Q₂ ; Q? to Q₂? ; {-It to It₂ ;-} δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
  Q' : Set
  Q' = Q₁ ∥ Q₂
  δ' : Q' → Σᵉ → Subset Q'
  δ' init      Ε (∥inj₁ q)  = q ≡ q₀₁
  δ' init      Ε (∥inj₂ q)  = q ≡ q₀₂
  δ' (∥inj₁ q) a (∥inj₁ q') = δ₁ q a q'
  δ' (∥inj₂ q) a (∥inj₂ q') = δ₂ q a q'
  δ' _         _ _          = ⊥
  F' : Subset Q'
  F' init      = ⊥
  F' (∥inj₁ q) = F₁ q
  F' (∥inj₂ q) = F₂ q

∙-2NFA : NFA → NFA → NFA
∙-2NFA nfa₁ nfa₂ = record { Q = Q' ; Q? = DecEq-⍟ Q₁? Q₂? ; {-It = Data.List.map ⍟inj₁ It₁ ++ mid ∷ Data.List.map ⍟inj₂ It₂ ;-} δ = δ' ; q₀ = ⍟inj₁ q₀₁ ; F = F' }
  where
   open NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; {-It to It₁ ;-} δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
   open NFA nfa₂ renaming (Q to Q₂ ; Q? to Q₂? ; {-It to It₂ ;-} δ to δ₂ ; q₀ to q₀₂ ; F to F₂)
   Q' : Set
   Q' = Q₁ ⍟ Q₂
   δ' : Q' → Σᵉ → Subset Q'
   δ' (⍟inj₁ q) a (⍟inj₁ q') = δ₁ q a q'
   δ' (⍟inj₁ q) Ε mid        = F₁ q
   δ' (⍟inj₂ q) a (⍟inj₂ q') = δ₂ q a q'
   δ' mid       Ε (⍟inj₂ q)  = q ≡ q₀₂
   δ' _         _ _ = ⊥  
   F' : Subset Q'
   F' (⍟inj₁ q) = ⊥
   F' mid       = ⊥
   F' (⍟inj₂ q) = F₂ q

*-2NFA : NFA → NFA
*-2NFA nfa = record { Q = Q' ; Q? = DecEq-* Q? ; {-It = init ∷ (Data.List.map inj It) ;-} δ = δ' ; q₀ = init ; F = F' }
 where
  open NFA nfa
  Q' : Set
  Q' = Q *-State
  δ' : Q' → Σᵉ → Subset Q'
  δ' init    E     (inj q)  = q ≡ q₀
  δ' (inj q) E     (inj q') = q ≡ q₀
  δ' (inj q) (α a) (inj q') = δ q (α a) q'
  δ' _       _     _        = ⊥
  F' : Subset Q'
  F' init = ⊤
  F' (inj q) = F q


Regex2NFA : RegExp → NFA
Regex2NFA Ø = record { Q = Ø-State ; Q? = DecEq-Ø ; {-It = init ∷ [] ;-} δ = λ _ _ _ → ⊥ ; q₀ = init ; F = ø }
Regex2NFA ε = record { Q = Q' ; Q? = DecEq-ε ; {-It = init ∷ error ∷ [] ;-} δ = δ' ; q₀ = init ; F = F' } 
 where
  Q' : Set
  Q' = ε-State
  δ' : Q' → Σᵉ → Subset Q'
  δ' init  E     init  = ⊤
  δ' init  (α a) error = ⊤
  δ' error _     error = ⊤
  δ' _     _     _     = ⊥
  F' : Subset Q'
  F' init  = ⊤
  F' error = ⊥
Regex2NFA (σ a) = record { Q = Q' ; Q? = DecEq-σ ; {-It = init ∷ accept ∷ error ∷ [] ;-} δ = δ' ; q₀ = init ; F = F' }
 where
  Q' : Set
  Q' = σ-State
  δ' : Q' → Σᵉ → Subset Q'
  δ' init   E       init   = ⊤
  δ' init   (α  b)  accept = a ≡ b
  δ' init   (α  b)  error  = a ≢ b
  δ' accept E       accept = ⊤
  δ' accept (α a)   error  = ⊤
  δ' error  _       error  = ⊤
  δ' _      _       _      = ⊥
  F' : Subset Q'
  F' init   = ⊥
  F' accept = ⊤
  F' error  = ⊥
Regex2NFA (e₁ ∣ e₂) = ∣-2NFA (Regex2NFA e₁) (Regex2NFA e₂)
Regex2NFA (e₁ ∙ e₂) = ∙-2NFA (Regex2NFA e₁) (Regex2NFA e₂)
Regex2NFA (e *)     = *-2NFA (Regex2NFA e)
