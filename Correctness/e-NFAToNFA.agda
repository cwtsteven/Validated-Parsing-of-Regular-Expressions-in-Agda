{-
  This module contains the following proofs:
    ∀nfa∈ε-NFA. L(nfa) ⊆ L(remove-ε-step nfa)
    ∀nfa∈ε-NFA. L(nfa) ⊇ L(remove-ε-step nfa)

  Steven Cheung 2015.
  Version 31-01-2015
-}
open import Util
module Correctness.e-NFAToNFA (Σ : Set)(dec : DecEq Σ) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Induction.Nat

open import Subset renaming (Ø to ø)
open import Subset.DecidableSubset renaming (_∈?_ to _∈ᵈ?_ ; _∈_ to _∈ᵈ_ ; ⟦_⟧ to ⟦_⟧ᵈ) hiding (_⊆_ ; _⊇_)
open import Language Σ dec
open import RegularExpression Σ dec
open import Automata Σ dec
open import Translation Σ dec
open import State



module Lᵉᴺ⊆Lᴺ (ε-nfa : ε-NFA) where
  nfa : NFA
  nfa = remove-ε-step ε-nfa

  open NFA nfa
  open NFA-Operations nfa
  open ε-NFA ε-nfa renaming (Q to Qₑ ; Q? to Qₑ? ; δ to δₑ ; q₀ to q₀ₑ ; F to Fₑ ; It to Itₑ) 
  open ε-NFA-Operations ε-nfa
    renaming (_⊢_ to _⊢ₑ_ ; _⊢*_ to _⊢*ₑ_ ; _⊢*₂_ to _⊢*₂ₑ_ ; _⊢ᵏ_─_ to _⊢ᵏₑ_─_ ; ⊢ᵏ₂-lem₉ to ⊢ᵏ₂-lem₉ₑ)


  lem₂ : ∀ q wᵉ n q' wᵉ'
         → (q , wᵉ) ⊢ᵏₑ n ─ (q' , wᵉ')
         → Σ[ p ∈ Qₑ ] Σ[ a ∈ Σ ] Σ[ n₁ ∈ ℕ ] ( n₁ <′ n ×  (q , wᵉ) ⊢ᵏₑ n₁ ─ (p , α a ∷ wᵉ') × (p , α a , wᵉ') ⊢ₑ (q' , wᵉ') )
           ⊎ ( Σ[ p ∈ Qₑ ] Σ[ a ∈ Σ ] Σ[ uᵉ ∈ Σᵉ* ] Σ[ n₁ ∈ ℕ ]
               ( n₁ <′ n
                 × ( Σ[ p₁ ∈ Qₑ ]
                     ( toΣ* uᵉ ≡ toΣ* wᵉ'
                       × (q , wᵉ) ⊢ᵏₑ n₁ ─ (p , α a ∷ uᵉ)
                       × (p , α a , uᵉ) ⊢ₑ (p₁ , uᵉ)
                       × (p₁ →ε* q') ) ) ) )
           ⊎ toΣ* wᵉ ≡ toΣ* wᵉ' × q →ε* q'
  lem₂ q wᵉ zero   .q .wᵉ  (refl , refl) = inj₂ (inj₂ (refl , (zero , refl)))
  lem₂ q wᵉ (suc n) q' wᵉ' prf with ⊢ᵏ₂-lem₂ {q} {wᵉ} {suc n} {q'} {wᵉ'} prf
  lem₂ q wᵉ (suc n) q' wᵉ' prf | p , α a , prf₁ , (refl , prf₂) = inj₁ (p , a , n , ≤′-refl , prf₁ , (refl , prf₂))
  lem₂ q wᵉ (suc n) q' wᵉ' prf | p , E   , prf₁ , (refl , prf₂) with lem₂ q wᵉ n p (E ∷ wᵉ') prf₁
  lem₂ q wᵉ (suc n) q' wᵉ' prf | p , E   , prf₁ , (refl , prf₂) | inj₁ (p₁ , a , n₁ , n₁<n , prf₃ , prf₄)
    = inj₂ (inj₁ (p₁ , a , E ∷ wᵉ' , n₁ , ≤′-step n₁<n , p , refl , prf₃ , prf₄ , (1 , q' , prf₂ , refl)))
  lem₂ q wᵉ (suc n) q' wᵉ' prf | p , E   , prf₁ , (refl , prf₂) | inj₂ (inj₁ (p₁ , a , uᵉ , n₁ , n₁<n , p₂ , uᵉ≡[] , prf₃ , prf₄ , (k , prf₅)))
    = inj₂ (inj₁ (p₁ , a , uᵉ , n₁ , ≤′-step n₁<n , p₂ , uᵉ≡[] , prf₃ , prf₄ , (suc k , →εᵏ-lem₁ p₂ k p q' prf₅ prf₂)))
  lem₂ q wᵉ (suc n) q' wᵉ' prf | p , E   , prf₁ , (refl , prf₂) | inj₂ (inj₂ (wᵉ≡[] , (k , q→εᵏp)))
    = inj₂ (inj₂ (wᵉ≡[] , (suc k , →εᵏ-lem₁ q k p q' q→εᵏp prf₂)))

  
  lem₃ : ∀ n w q wᵉ p a uᵉ q'
         → w ≡ toΣ* wᵉ
         → (q , wᵉ) ⊢ᵏₑ n ─ (p , α a ∷ uᵉ)
         → (p , α a , uᵉ) ⊢ₑ (q' , uᵉ)
         → Σ[ u ∈ Σ* ] ( u ≡ toΣ* uᵉ × ( Σ[ n₁ ∈ ℕ ] (q , w) ⊢ᵏ n₁ ─ (q' , u) ) )
  lem₃ = <-rec _ helper
    where
      helper : ∀ n
               → (∀ m₁
                 → m₁ <′ n
                 → ∀ w q wᵉ p a uᵉ q'
                   → w ≡ toΣ* wᵉ
                   → (q , wᵉ) ⊢ᵏₑ m₁ ─ (p , α a ∷ uᵉ)
                   → (p , α a , uᵉ) ⊢ₑ (q' , uᵉ)
                   → Σ[ u ∈ Σ* ] ( u ≡ toΣ* uᵉ × ( Σ[ n₁ ∈ ℕ ] (q , w) ⊢ᵏ n₁ ─ (q' , u) ) ))
               → ∀ w q wᵉ p a uᵉ q'
                 → w ≡ toΣ* wᵉ
                 → (q , wᵉ) ⊢ᵏₑ n ─ (p , α a ∷ uᵉ)
                 → (p , α a , uᵉ) ⊢ₑ (q' , uᵉ)
                 → Σ[ u ∈ Σ* ] ( u ≡ toΣ* uᵉ × ( Σ[ n₁ ∈ ℕ ] (q , w) ⊢ᵏ n₁ ─ (q' , u) ) )
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) with lem₂ q wᵉ n p (α a ∷ uᵉ) prf₁
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₁ (p₁ , a₁ , n₁ , n₁<n , prf₃ , prf₄) with rec n₁ n₁<n w q wᵉ p₁ a₁ (α a ∷ uᵉ) p w≡wᵉ prf₃ prf₄
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₁ (p₁ , a₁ , n₁ , n₁<n , prf₃ , prf₄) | ._ , refl , n₂ , prf₅
        = toΣ* uᵉ , refl , suc n₂ , ⊢ᵏ₂-lem₉ {q} {w} {n₂} {p} {a} {q'} {toΣ* uᵉ} prf₅ (refl , Bool-lem₆ _ _ prf₂)
        
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₁ (p₁ , a₁ , uᵉ₁ , n₁ , n₁<n , p₂ , uᵉ₁≡auᵉ , prf₃ , prf₄ , p₂→p)) with rec n₁ n₁<n w q wᵉ p₁ a₁ uᵉ₁ p₂ w≡wᵉ prf₃ prf₄
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₁ (p₁ , a₁ , uᵉ₁ , n₁ , n₁<n , p₂ , uᵉ₁≡auᵉ , prf₃ , prf₄ , p₂→p)) | ._ , refl , n₂ , prf₅ with ∃q⊢a-q'? (Dec-→ε*⊢ p₂ a q') | inspect (λ q' → ∃q⊢a-q'? (Dec-→ε*⊢ p₂ a q')) q'
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₁ (p₁ , a₁ , uᵉ₁ , n₁ , n₁<n , p₂ , uᵉ₁≡auᵉ , prf₃ , prf₄ , p₂→p)) | ._ , refl , n₂ , prf₅ | true  | [ eq ]
        = let q→p₂ = subst (λ u → (q , w) ⊢ᵏ n₂ ─ (p₂ , u)) uᵉ₁≡auᵉ prf₅ in
          toΣ* uᵉ , refl , suc n₂ , ⊢ᵏ₂-lem₉ {q} {w} {n₂} {p₂} {a} {q'} {toΣ* uᵉ} q→p₂ (refl , Bool-lem₁₀ (∃q⊢a-q'? (Dec-→ε*⊢ p₂ a q')) (q' ∈ᵈ? δₑ p₂ (α a)) eq)
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₁ (p₁ , a₁ , uᵉ₁ , n₁ , n₁<n , p₂ , uᵉ₁≡auᵉ , prf₃ , prf₄ , p₂→p)) | ._ , refl , n₂ , prf₅ | false | [ eq ] with Dec-→ε*⊢ p₂ a q'
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₁ (p₁ , a₁ , uᵉ₁ , n₁ , n₁<n , p₂ , uᵉ₁≡auᵉ , prf₃ , prf₄ , p₂→p)) | ._ , refl , n₂ , prf₅ | false | [ () ] | yes _
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₁ (p₁ , a₁ , uᵉ₁ , n₁ , n₁<n , p₂ , uᵉ₁≡auᵉ , prf₃ , prf₄ , p₂→p)) | ._ , refl , n₂ , prf₅ | false | [ eq ] | no  ¬q→p
        = ⊥-elim (¬q→p (p , prf₂ , p₂→p))
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₂ (wᵉ≡auᵉ , q→p)) with ∃q⊢a-q'? (Dec-→ε*⊢ q a q') | inspect (λ q' → ∃q⊢a-q'? (Dec-→ε*⊢ q a q')) q'
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₂ (wᵉ≡auᵉ , q→p)) | true  | [ eq ]
        = toΣ* uᵉ , refl , suc zero , (q' , a , toΣ* uᵉ , trans w≡wᵉ wᵉ≡auᵉ , (refl , Bool-lem₁₀ (∃q⊢a-q'? (Dec-→ε*⊢ q a q')) (q' ∈ᵈ? δₑ q (α a)) eq) , (refl , refl))
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₂ (wᵉ≡auᵉ , q→p)) | false | [ eq ] with Dec-→ε*⊢ q a q'
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₂ (wᵉ≡auᵉ , q→p)) | false | [ () ] | yes _
      helper n rec w q wᵉ p a uᵉ q' w≡wᵉ prf₁ (refl , prf₂) | inj₂ (inj₂ (wᵉ≡auᵉ , q→p)) | false | [ eq ] | no  ¬q→p
        = ⊥-elim (¬q→p (p , prf₂ , q→p))
    

  lem₁ : Lᵉᴺ ε-nfa ⊆ Lᴺ nfa
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) with lem₂ q₀ wᵉ n q [] prf
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₁ (p , a , n₁ , n₁<n , prf₁ , prf₂) with lem₃ n₁ w q₀ wᵉ p a [] q w≡wᵉ prf₁ prf₂
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₁ (p , a , n₁ , n₁<n , prf₁ , prf₂) | .[] , refl , n₂ , prf₃
    = q , Bool-lem₆ _ _ q∈Fₑ  , n₂ , prf₃
    
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₁ (p , a , uᵉ , n₁ , n₁<n , p₁ , uᵉ≡[] , prf₃ , prf₄ , (k , prf₅))) with ∃q∈F? (Dec-→ε*∈F p₁) | inspect (λ p → ∃q∈F? (Dec-→ε*∈F p)) p₁
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₁ (p , a , uᵉ , n₁ , n₁<n , p₁ , uᵉ≡[] , prf₃ , prf₄ , (k , prf₅))) | true  | [ eq ] with lem₃ n₁ w q₀ wᵉ p a uᵉ p₁ w≡wᵉ prf₃ prf₄
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₁ (p , a , uᵉ , n₁ , n₁<n , p₁ , uᵉ≡[] , prf₃ , prf₄ , (k , prf₅))) | true  | [ eq ] | u , u≡uᵉ , n₂ , prf₆
    = p₁ , Bool-lem₁₀ (∃q∈F? (Dec-→ε*∈F p₁)) (Fₑ p₁) eq , n₂ , subst (λ u → (q₀ , w) ⊢ᵏ n₂ ─ (p₁ , u)) (trans u≡uᵉ uᵉ≡[]) prf₆
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₁ (p , a , uᵉ , n₁ , n₁<n , p₁ , uᵉ≡[] , prf₃ , prf₄ , (k , prf₅))) | false | [ eq ] with Dec-→ε*∈F p₁
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₁ (p , a , uᵉ , n₁ , n₁<n , p₁ , uᵉ≡[] , prf₃ , prf₄ , (k , prf₅))) | false | [ () ] | yes _
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₁ (p , a , uᵉ , n₁ , n₁<n , p₁ , uᵉ≡[] , prf₃ , prf₄ , (k , prf₅))) | false | [ eq ] | no  ¬p→ε*q
    = ⊥-elim (¬p→ε*q (q , q∈Fₑ , k , prf₅))

  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₂ (wᵉ≡[] , q₀→q)) with ∃q∈F? (Dec-→ε*∈F q₀ₑ) | inspect (λ p → ∃q∈F? (Dec-→ε*∈F p)) q₀ₑ
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₂ (wᵉ≡[] , q₀→q)) | true  | [ eq ] = q₀ₑ , Bool-lem₁₀ (∃q∈F? (Dec-→ε*∈F q₀ₑ)) (Fₑ q₀ₑ) eq , (zero , refl , trans w≡wᵉ wᵉ≡[])
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₂ (wᵉ≡[] , q₀→q)) | false | [ eq ] with Dec-→ε*∈F q₀ₑ
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₂ (wᵉ≡[] , q₀→q)) | false | [ () ] | yes _
  lem₁ w (wᵉ , w≡wᵉ , q , q∈Fₑ , (n , prf)) | inj₂ (inj₂ (wᵉ≡[] , q₀→q)) | false | [ eq ] | no  ¬q₀→q
    = ⊥-elim (¬q₀→q (q , q∈Fₑ , q₀→q))


Lᵉᴺ⊆Lᴺ : ∀ ε-nfa → Lᵉᴺ ε-nfa ⊆ Lᴺ (remove-ε-step ε-nfa)
Lᵉᴺ⊆Lᴺ = Lᵉᴺ⊆Lᴺ.lem₁ 



module Lᵉᴺ⊇Lᴺ (ε-nfa : ε-NFA) where
  nfa : NFA
  nfa = remove-ε-step ε-nfa

  open NFA nfa
  open NFA-Operations nfa
  open ε-NFA ε-nfa renaming (Q to Qₑ ; Q? to Qₑ? ; δ to δₑ ; q₀ to q₀ₑ ; F to Fₑ ; It to Itₑ) 
  open ε-NFA-Operations ε-nfa
    renaming (_⊢_ to _⊢ₑ_ ; _⊢*_ to _⊢*ₑ_ ; _⊢*₂_ to _⊢*₂ₑ_ ; _⊢ᵏ_─_ to _⊢ᵏₑ_─_)

  lem₃ : ∀ q n q' uᵉ
         → q →εᵏ n ─ q'
         → Σ[ wᵉ ∈ Σᵉ* ] ( toΣ* uᵉ ≡ toΣ* wᵉ × (q , wᵉ) ⊢ᵏₑ n ─ (q' , uᵉ) )
  lem₃ q zero    .q  uᵉ refl = uᵉ , refl , (refl , refl)
  lem₃ q (suc n)  q' uᵉ (p , prf₁ , prf₂) with lem₃ p n q' uᵉ prf₂
  lem₃ q (suc n)  q' uᵉ (p , prf₁ , prf₂) | wᵉ , uᵉ≡wᵉ , prf₃ = E ∷ wᵉ , uᵉ≡wᵉ , (p , E , wᵉ , refl , (refl , prf₁) , prf₃)

  lem₂ : ∀ q w n q'
         → (q , w) ⊢ᵏ n ─ (q' , [])
         → Σ[ wᵉ ∈ Σᵉ* ] ( w ≡ toΣ* wᵉ × ( Σ[ n₁ ∈ ℕ ] (q , wᵉ) ⊢ᵏₑ n₁ ─ (q' , []) ) )
  lem₂ q .[] zero    .q  (refl , refl) = [] , refl , zero , (refl , refl)
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) with p ∈ᵈ? δₑ q (α a) | inspect (δₑ q (α a)) p
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | true  | [ p∈δqa ] with lem₂ p u n q' prf₂
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | true  | [ p∈δqa ] | uᵉ , u≡uᵉ , n₁ , prf₃
    = α a ∷ uᵉ , cong (λ u → a ∷ u) u≡uᵉ , suc n₁ , (p , α a , uᵉ , refl , (refl , p∈δqa) , prf₃)
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | false | [ p∉δqa ] with Dec-→ε*⊢ q a p
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | false | [ p∉δqa ] | yes (p₁ , p∈δp₁a , k , q→εᵏp₁) with lem₂ p u n q' prf₂
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | false | [ p∉δqa ] | yes (p₁ , p∈δp₁a , k , q→εᵏp₁) | uᵉ , u≡uᵉ , n₁ , prf₃ with lem₃ q k p₁ (α a ∷ uᵉ) q→εᵏp₁
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl , prf₁) , prf₂) | false | [ p∉δqa ] | yes (p₁ , p∈δp₁a , k , q→εᵏp₁) | uᵉ , u≡uᵉ , n₁ , prf₃ | uᵉ₁ , auᵉ≡uᵉ₁ , prf₄ 
    = uᵉ₁ , trans (cong (λ u → a ∷ u) u≡uᵉ) auᵉ≡uᵉ₁ , k + suc n₁ ,  ⊢*-lem₄ q uᵉ₁ k p₁ (α a ∷ uᵉ) (suc n₁) q' [] prf₄ (p , α a , uᵉ , refl , (refl , p∈δp₁a) , prf₃)
  lem₂ q ._  (suc n)  q' (p , a , u , refl , (refl ,   ()) , prf₂) | false | [ p∉δqa ] | no  _
  
  lem₄ : ∀ q wᵉ n q' vᵉ
         → (q , wᵉ) ⊢ᵏₑ n ─ (q' , [])
         → (q , wᵉ ++ vᵉ) ⊢ᵏₑ n ─ (q' , vᵉ)
  lem₄ q .[] zero   .q  vᵉ (refl , refl) = refl , refl
  lem₄ q ._  (suc n) q' vᵉ (p , a , uᵉ , refl , (refl , prf₁) , prf₂)
    = p , a , uᵉ ++ vᵉ , refl , (refl , prf₁) , lem₄ p uᵉ n q' vᵉ prf₂


  lem₁ : Lᵉᴺ ε-nfa ⊇ Lᴺ nfa
  lem₁ w (q , q∈F , n , prf) with q ∈ᵈ? Fₑ | inspect Fₑ q
  lem₁ w (q , q∈F , n , prf) | true  | [ q∈Fₑ ] with lem₂ q₀ w n q prf
  lem₁ w (q , q∈F , n , prf) | true  | [ q∈Fₑ ] | wᵉ , w≡wᵉ , n₁ , prf₁
    = wᵉ , w≡wᵉ , q , q∈Fₑ , (n₁ , prf₁)
  lem₁ w (q , q∈F , n , prf) | false | [ q∉Fₑ ] with Dec-→ε*∈F q
  lem₁ w (q , q∈F , n , prf) | false | [ q∉Fₑ ] | yes (p , p∈Fₑ , n₂ , q→εᵏp) with lem₂ q₀ w n q prf | lem₃ q n₂ p [] q→εᵏp
  lem₁ w (q , q∈F , n , prf) | false | [ q∉Fₑ ] | yes (p , p∈Fₑ , n₂ , q→εᵏp) | wᵉ , w≡wᵉ , n₁ , prf₁ | wᵉ₁ , []≡wᵉ , prf₂
    = wᵉ ++ wᵉ₁ , trans (subst (λ wᵉ₁ → w ≡ toΣ* wᵉ ++ wᵉ₁) []≡wᵉ (trans w≡wᵉ (sym (List-lem₂ (toΣ* wᵉ))))) (Σᵉ*-lem₁ wᵉ wᵉ₁)  , p , p∈Fₑ , n₁ + n₂ , q₀→p
      where
        q₀→q : (q₀ₑ , wᵉ ++ wᵉ₁) ⊢ᵏₑ n₁ ─ (q , wᵉ₁)
        q₀→q = lem₄ q₀ wᵉ n₁ q wᵉ₁ prf₁
        q₀→p : (q₀ₑ , wᵉ ++ wᵉ₁) ⊢ᵏₑ n₁ + n₂ ─ (p , []) 
        q₀→p = ⊢*-lem₄ q₀ (wᵉ ++ wᵉ₁) n₁ q wᵉ₁ n₂ p [] q₀→q prf₂
  lem₁ w (q ,  () , n , prf) | false | [ q∉Fₑ ] | no  _


Lᵉᴺ⊇Lᴺ : ∀ ε-nfa → Lᵉᴺ ε-nfa ⊇ Lᴺ (remove-ε-step ε-nfa)
Lᵉᴺ⊇Lᴺ = Lᵉᴺ⊇Lᴺ.lem₁
