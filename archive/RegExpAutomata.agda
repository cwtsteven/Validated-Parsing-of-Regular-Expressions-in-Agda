module RegExpAutomata where

open import Data.List
open import Util
open import Relation.Binary
open import Data.Product
open import Data.Bool
open import Data.Nat
open import Data.Vec renaming (_++_ to _++v_; _∷ʳ_ to _∷ʳv_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

Σ* : {Σ : Set} → Set
Σ* {Σ} = List Σ


------------------------------------------------------ Regular Expression ------------------------------------------------------
infix 10 _∣_
infix 11 _∙_
infix 12 _*
data RegExp (Σ : Set) : Set where
 Ø   : RegExp Σ
 ε   : RegExp Σ
 σ   : Σ → RegExp Σ
 _∣_ : RegExp Σ → RegExp Σ → RegExp Σ
 _∙_ : RegExp Σ → RegExp Σ → RegExp Σ
 _*  : RegExp Σ → RegExp Σ

module RegExp-Operations (Σ : Set) where

 infix 0 _⇨_
 data _⇨_ : RegExp Σ → Σ* → Set where
  empty    : {w : Σ* {Σ}} → null w ≡ true → ε ⇨ w
  alphabet : {a b : Σ}{xs : Σ*} → a ≡ b → null xs ≡ true → (σ a) ⇨ b ∷ xs
  unionˡ   : {e₁ e₂ : RegExp Σ}{w : Σ*} → e₁ ⇨ w → e₁ ∣ e₂ ⇨ w
  unionʳ   : {e₁ e₂ : RegExp Σ}{w : Σ*} → e₂ ⇨ w → e₁ ∣ e₂ ⇨ w
  con      : {e₁ e₂ : RegExp Σ}{w w₁ w₂ : Σ*} → e₁ ⇨ w₁ → e₂ ⇨ w₂ → e₁ ∙ e₂ ⇨ w
  kleenᵉ   : {e : RegExp Σ}{w : Σ*} → null w ≡ true →  e * ⇨ w
  kleen    : {e : RegExp Σ}{w : Σ*} → e ⇨ w → e * ⇨ w

 ¬ε⇨w : {w : Σ*} → ¬ (null w ≡ true) → ¬ (ε ⇨ w)
 ¬ε⇨w ¬null (empty null≡true) = ¬null null≡true

 ¬σa⇨b∷[] : {a b : Σ} → ¬ (a ≡ b) → ¬ ((σ a) ⇨ b ∷ [])
 ¬σa⇨b∷[] a≢b (alphabet a≡b _) = a≢b a≡b

 ¬σa⇨x∷xs : {a : Σ}{x : Σ}{xs : Σ*} → ¬ (null xs ≡ true) → ¬ ((σ a) ⇨ x ∷ xs)
 ¬σa⇨x∷xs ¬null (alphabet a≡x null≡true) = ¬null null≡true
 
 ¬e₁∣e₂⇨w : {e₁ e₂ : RegExp Σ}{w : Σ*} → ¬ (e₁ ⇨ w) → ¬ (e₂ ⇨ w) → ¬ (e₁ ∣ e₂ ⇨ w)
 ¬e₁∣e₂⇨w ¬e₁⇨w ¬e₂⇨w (unionˡ e₁⇨w) = ¬e₁⇨w e₁⇨w
 ¬e₁∣e₂⇨w ¬e₁⇨w ¬e₂⇨w (unionʳ e₂⇨w) = ¬e₂⇨w e₂⇨w

 postulate ¬e₁∙e₂⇨wˡ : {e₁ e₂ : RegExp Σ}{w₁ w₂ : Σ*} → ¬ (e₁ ⇨ w₁) → ¬ (e₁ ∙ e₂ ⇨ w₁ ++ w₂)
 postulate ¬e₁∙e₂⇨wʳ : {e₁ e₂ : RegExp Σ}{w₁ w₂ : Σ*} → ¬ (e₂ ⇨ w₂) → ¬ (e₁ ∙ e₂ ⇨ w₁ ++ w₂)

 ¬e*⇨w : {e : RegExp Σ}{w : Σ*} → ¬ (e ⇨ w) → ¬ (null w ≡ true) → ¬ (e * ⇨ w)
 ¬e*⇨w ¬e⇨w ¬null (kleenᵉ null≡true) = ¬null null≡true
 ¬e*⇨w ¬e⇨w ¬null (kleen  e⇨w)       = ¬e⇨w e⇨w
{-
 list-lem : {A : Set}(w xs ys : List A) → (x : A) → w ≡ ys ++ (x ∷ xs) → w ≡ (ys ∷ʳ x) ++ xs
 list-lem w xs [] x w≡xxs = begin
                            [] ++ (x ∷ xs)  ≡⟨ refl ⟩
                            x ∷ xs          ≡⟨ refl ⟩
                            x ∷ ([] ++ xs)  ≡⟨ refl ⟩
                            x ∷ [] ++ xs    ≡⟨ refl ⟩
                            ∎
-}
 mutual
 {-
  e₁e₂⇨?w₁w₂ : {w : Σ*}(e₁ e₂ : RegExp Σ) → (w₁ w₂ : Σ*) → w ≡ w₁ ++ w₂ → {eq? : DecEq Σ} → Dec (e₁ ∙ e₂ ⇨ w)
  e₁e₂⇨?w₁w₂ e₁ e₂ ys [] w≡w₁w₂ {eq?} with (e₁ ⇨? ys) {eq?} | (e₂ ⇨? []) {eq?}
  ... | yes e₁⇨ys | yes e₂⇨[] = yes (con e₁⇨ys e₂⇨[])
  ... | no ¬e₁⇨ys | _         = no (¬e₁∙e₂⇨wˡ ¬e₁⇨ys)
  ... | _         | no ¬e₂⇨[] = no (¬e₁∙e₂⇨wʳ {e₁} {e₂} {ys} {[]} ¬e₂⇨[])
  e₁e₂⇨?w₁w₂ e₁ e₂ ys (x ∷ xs) w≡w₁w₂ {eq?} with (e₁ ⇨? ys) {eq?} | (e₂ ⇨? (x ∷ xs)) {eq?}
  ... | yes e₁⇨ys | yes e₂⇨xs = yes (con e₁⇨ys e₂⇨xs)
  ... | no _      | _          = e₁e₂⇨?w₁w₂ e₁ e₂ (ys ∷ʳ x) xs w≡w₁w₂ {eq?}
  ... | _         | no _       = e₁e₂⇨?w₁w₂ e₁ e₂ (ys ∷ʳ x) xs w≡w₁w₂ {eq?}
 -}

  infix 0 _⇨?_
  _⇨?_ : (e : RegExp Σ) → (w : Σ*) → {eq? : DecEq Σ} → Dec (e ⇨ w)
  Ø ⇨? _ = no (λ ())
  ε ⇨? w with (null w) ≡Bool? true
  ... | yes null≡true = yes (empty null≡true)
  ... | no  ¬null     = no (¬ε⇨w ¬null)
  σ a ⇨? []      = no (λ ())
  (σ a ⇨? b ∷ xs) {eq?} with xs | (null xs) ≡Bool? true 
  ... | w      | no ¬null    = no (¬σa⇨x∷xs ¬null)
  ... | w ∷ ws | yes ()
  ... | [] | yes isNull with a | b | eq? a b 
  ...   | .x | x  | yes refl = yes (alphabet refl refl)
  ...   | x  | y  | no a≢b   = no (¬σa⇨b∷[] a≢b)
  (e₁ ∣ e₂ ⇨? w) {eq?} with (e₁ ⇨? w) {eq?} | (e₂ ⇨? w) {eq?}
  ... | yes e₁⇨w  | _        = yes (unionˡ e₁⇨w)
  ... | _         | yes e₂⇨w = yes (unionʳ e₂⇨w)
  ... | no  ¬e₁⇨w | no ¬e₂⇨w = no (¬e₁∣e₂⇨w ¬e₁⇨w ¬e₂⇨w) 
  (e₁ ∙ e₂ ⇨? []) {eq?} with (e₁ ⇨? []) {eq?} | (e₂ ⇨? []) {eq?}
  ... | yes e₁⇨[] | yes e₂⇨[] = yes (con e₁⇨[] e₂⇨[])
  ... | no ¬e₁⇨[] | _         = no (¬e₁∙e₂⇨wˡ ¬e₁⇨[])
  ... | _         | no ¬e₂⇨[] = no (¬e₁∙e₂⇨wʳ {e₁} {e₂} {[]} {[]} ¬e₂⇨[])
  (e₁ ∙ e₂ ⇨? (x ∷ xs)) {eq?} = {!!}
  (e * ⇨? w) {eq?} with w | null w ≡Bool? true
  ... | []       | yes null≡true = yes (kleenᵉ refl)
  ... | (x ∷ xs) | yes ()
  ... | xs       | no  ¬null with (e ⇨? xs) {eq?}
  ...   | yes e⇨w   = yes (kleen e⇨w)
  ...   | no  ¬e⇨w  = no (¬e*⇨w ¬e⇨w ¬null)

 language : {eq? : DecEq Σ} → RegExp Σ → Σ* {Σ} → Bool
 language {eq?} e w with (e ⇨? w) {eq?}
 ... | yes _ = true
 ... | no _  = false


------------------------------------------------------ Automata ------------------------------------------------------
State : Set
State = ℕ

inv-equal : {m n : ℕ} → (suc m ≡ suc n) → m ≡ n
inv-equal refl = refl

¬sucm≡sucn : {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬sucm≡sucn m≢n sucm≡sucn = m≢n (inv-equal sucm≡sucn)

infix 0 _≡State?_
_≡State?_ : DecEq State
zero ≡State? zero    = yes refl
zero ≡State? suc n   = no (λ ())
suc n ≡State? zero   = no (λ ())
suc m ≡State? suc n with m ≡State? n
... | yes m≡n = yes (cong suc m≡n)
... | no  m≢n = no (¬sucm≡sucn m≢n)

infix 0 _,_,_,_,_
record NFA (Σ : Set) : Set₁ where
 constructor _,_,_,_,_
 field
  n  : ℕ
  Q  : Vec State n
  δ  : State → Σ → Subset State
  q₀ : State
  F  : Subset State

module NFA-Operations (Σ : Set)(N : NFA Σ) where

record DFA (Σ : Set) : Set₁ where
 constructor _,_,_,_,_
 field
  n  : ℕ
  Q  : Vec State n
  δ  : State → Σ → State
  q₀ : State
  F  : Subset State

module DFA-Operations (Σ : Set)(M : DFA Σ) where
  open DFA M
  
  δ^ : State → Σ* → State
  δ^ q [] = q
  δ^ q (x ∷ xs) = δ^ (δ q x) xs
  
  δ₀ : Σ* → State
  δ₀ w = δ^ q₀ w

  language : Σ* → Bool
  language w = (δ₀ w ∈? F) {_≡State?_}
