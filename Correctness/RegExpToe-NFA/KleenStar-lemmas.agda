open import Util
open import RegularExpression
module Correctness.RegExpToe-NFA.KleenStar-lemmas (Σ : Set)(dec : DecEq Σ)(e : RegularExpression.RegExp Σ) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Unit
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_)
open import Language Σ
open import Automata Σ
open import Translation Σ dec
open import State

nfa : ε-NFA
nfa = regexToε-NFA (e *)

nfa₁ : ε-NFA
nfa₁ = regexToε-NFA e

open ε-NFA nfa
open ε-NFA nfa₁ renaming (Q to Q₁ ; Q? to Q₁? ; δ to δ₁ ; q₀ to q₀₁ ; F to F₁)
open ε-NFA-Operations nfa
open ε-NFA-Operations nfa₁ renaming (_⊢_ to _⊢ₑ₁_ ; _⊢*_ to _⊢*ₑ₁_ ; _⊢ᵏ_─_ to _⊢ᵏₑ₁_─_ ; ⊢*-lem₁ to ⊢*-lem₁ₑ₁)

module Lᴿ⊆Lᴺ where

{-
 lem₆ : ∀ q w n q' u v
        → w ≡ u ++ v
        → (q , u) ⊢ᵏₑ₁ n ─ (q' , [])
        → (inj q , w) ⊢ᵏ n ─ (inj q' , v)
 lem₆ q w zero    q' .[] u w≡u[] (q≡q' , refl)
   = cong inj q≡q' , trans w≡u[] refl
 lem₆ q w (suc n) q' u v w≡uv (p , (α a) , u' , refl , (refl , p≡δqa) , prf₃)
   = inj p , (α a) , u' ++ v , inj₁ (List-lem₅ w≡uv refl , a≢E)
     , (refl , p≡δqa) , lem₆ p (u' ++ v) n q' u' v refl prf₃
 lem₆ q w (suc n) q' u v w≡uv (p    ,  E , u' , inj₁ (u≡au' , a≢E)  , (refl , p≡δqa) , prf₃) = ⊥-elim (a≢E refl)
 lem₆ q w (suc n) q' u v w≡uv (p    , .E , u' , inj₂ (u≡u'  , refl) , (refl , p≡δqE) , prf₃) with inj p ∈ᵈ δ (inj q) E | inspect (δ (inj q) E) (inj p)
 lem₆ q w (suc n) q' u v w≡uv (p    , .E , u' , inj₂ (u≡u'  , refl) , (refl , p≡δqE) , prf₃) | true  | [ eq ]
   = inj p , E , u' ++ v , inj₂ (List-lem₅ w≡uv u≡u'  , refl) 
     , (refl , eq) , lem₆ p (u' ++ v) n q' u' v refl prf₃
 lem₆ q w (suc n) q' u v w≡uv (p    , .E , u' , inj₂ (u≡u'  , refl) , (refl , p≡δqE) , prf₃) | false | [ eq ] with p ∈ᵈ δ₁ q E | q ∈ᵈ F₁ | Q₁? p q₀₁
 lem₆ q w (suc n) q' u v w≡uv (.q₀₁ , .E , u' , inj₂ (u≡u'  , refl) , (refl , p≡δqE) , prf₃) | false | [ () ] | true  | true  | yes refl
 lem₆ q w (suc n) q' u v w≡uv (p    , .E , u' , inj₂ (u≡u'  , refl) , (refl , p≡δqE) , prf₃) | false | [ () ] | true  | true  | no  p≢q₀₁
 lem₆ q w (suc n) q' u v w≡uv (p    , .E , u' , inj₂ (u≡u'  , refl) , (refl , p≡δqE) , prf₃) | false | [ () ] | true  | false | _
 lem₆ q w (suc n) q' u v w≡uv (p    , .E , u' , inj₂ (u≡u'  , refl) , (refl , ()   ) , prf₃) | false | [ eq ] | false | _     | _

 lem₅ : ∀ w n q' u v
        → w ≡ u ++ v
        → (q₀₁ , u) ⊢ᵏₑ₁ n ─ (q' , [])
        → (init , w) ⊢ᵏ suc n ─ (inj q' , v)
 lem₅ w n q' u v w≡uv q₀₁u⊢ᵏₑ₁q'[] with inj q₀₁ ∈ᵈ δ init E | inspect (δ init E) (inj q₀₁)
 lem₅ w n q' u v w≡uv q₀₁u⊢ᵏₑ₁q'[] | true  | [ eq ]
   = inj q₀₁ , E , w , inj₂ (refl , refl) , (refl , eq) , lem₆ q₀₁ w n q' u v w≡uv q₀₁u⊢ᵏₑ₁q'[]
 lem₅ w n q' u v w≡uv q₀₁u⊢ᵏₑ₁q'[] | false | [ eq ] with Q₁? q₀₁ q₀₁
 lem₅ w n q' u v w≡uv q₀₁u⊢ᵏₑ₁q'[] | false | [ () ] | yes refl
 lem₅ w n q' u v w≡uv q₀₁u⊢ᵏₑ₁q'[] | false | [ eq ] | no  q₀₁≢q₀₁ = ⊥-elim (q₀₁≢q₀₁ refl)

 lem₄ : ∀ q a w q' w'
        → (q , a , w) ⊢ₑ₁ (q' , w')
        → (inj q , a , w) ⊢ (inj q' , w')
 lem₄ q E     w q'   w' (w≡w' , q'∈δqE) with inj q' ∈ᵈ δ (inj q) E | inspect (δ (inj q) E) (inj q')
 lem₄ q E     w q'   w' (w≡w' , q'∈δqE) | true  | [ eq ]  = w≡w' , refl
 lem₄ q E     w q'   w' (w≡w' , q'∈δqE) | false | [ eq ] with q' ∈ᵈ δ₁ q E | q ∈ᵈ F₁ | Q₁? q' q₀₁
 lem₄ q E     w .q₀₁ w' (w≡w' , refl  ) | false | [ () ] | true  | true  | yes refl
 lem₄ q E     w q'   w' (w≡w' , refl  ) | false | [ () ] | true  | true  | no  q'≢q₀₁
 lem₄ q E     w q'   w' (w≡w' , refl  ) | false | [ () ] | true  | false | _
 lem₄ q E     w q'   w' (w≡w' , ()    ) | false | [ eq ] | false | _     | _
 lem₄ q (α a) w q'   w' (w≡w' , q'∈δqa) = w≡w' , q'∈δqa

 lem₃ : ∀ q w n q' w'
        → (q , w) ⊢ᵏₑ₁ n ─ (q' , w')
        → (inj q , w) ⊢ᵏ n ─ (inj q' , w')
 lem₃ q w zero    .q  .w  (refl , refl) = refl , refl
 lem₃ q w (suc n)  q' w' (p , a , u , prf₁ , prf₂ , prf₃)
   = inj p , a , u , prf₁ , lem₄ q a u p u prf₂  , lem₃ p u n q' w' prf₃

 lem₂ : ∀ w q' w'
        → (q₀₁ , w) ⊢*ₑ₁ (q' , w')
        → (init , w) ⊢* (inj q' , w')
 lem₂ w q' w' (n , prf) with inj q₀₁ ∈ᵈ δ init E | inspect (δ init E) (inj q₀₁)
 lem₂ w q' w' (n , prf) | true  | [ eq ]
   = suc n , inj q₀₁ , E , w , inj₂ (refl , refl) , (refl , eq) , lem₃ q₀₁ w n q' w' prf
 lem₂ w q' w' (n , prf) | false | [ eq ] with Q₁? q₀₁ q₀₁
 lem₂ w q' w' (n , prf) | false | [ () ] | yes refl
 lem₂ w q' w' (n , prf) | false | [ eq ] | no  q'≢q₀₁ = ⊥-elim (q'≢q₀₁ refl)

 lem₁ : ∀ w u
        → w ≡ u ++ []
        → u ∈ Lᵉᴺ nfa₁
        → w ∈ Lᵉᴺ nfa
 lem₁ w u w≡u[] (q , q∈F₁ , q₀₁u⊢*̂ₑ₁q[])
   = inj q , q∈F₁
     , lem₂ (toΣᵉ* w) q []
       (subst (λ w → (q₀₁ , (toΣᵉ* w)) ⊢*ₑ₁ (q , []))
         (trans (sym (List-lem₂ u)) (sym w≡u[])) q₀₁u⊢*̂ₑ₁q[])
-}

 lem₆ : ∀ q wᵉ n vᵉ
        → ¬ (inj q , wᵉ) ⊢ᵏ n ─ (init , vᵉ)
 lem₆ q wᵉ zero    vᵉ (() , _)
 lem₆ q wᵉ (suc n) vᵉ (init  , α _ , uᵉ , _ , (refl ,   ()) , prf₂)
 lem₆ q wᵉ (suc n) vᵉ (init  , E   , uᵉ , _ , (refl ,   ()) , prf₂)
 lem₆ q wᵉ (suc n) vᵉ (inj p , a   , uᵉ , _ , (refl , prf₁) , prf₂)
   = lem₆ p uᵉ n vᵉ prf₂

 lem₅ : ∀ wᵉ n vᵉ
        → ¬ (init , wᵉ) ⊢ᵏ suc n ─ (init , vᵉ)
 lem₅ ._ zero    .uᵉ (.init  , α _ , uᵉ , refl , (refl ,   ()) , (refl , refl))
 lem₅ ._ zero    .uᵉ (.init  , E   , uᵉ , refl , (refl ,   ()) , (refl , refl))
 lem₅ ._ (suc n)  vᵉ ( init  , α _ , uᵉ , refl , (refl ,   ()) , prf₂)
 lem₅ ._ (suc n)  vᵉ ( init  , E   , uᵉ , refl , (refl ,   ()) , prf₂) 
 lem₅ ._ (suc n)  vᵉ ( inj p , a   , uᵉ , refl , (refl , prf₁) , prf₂)
   = lem₆ p uᵉ (suc n) vᵉ prf₂

 lem₄ : ∀ wᵉ n q₁
        → (q₀ , wᵉ)  ⊢ᵏ suc n ─ (inj q₁ , [])
        → Σ[ uᵉ ∈ Σᵉ* ] (wᵉ ≡ E ∷ uᵉ × (inj q₀₁ , uᵉ) ⊢ᵏ n ─ (inj q₁ , []))
 lem₄ ._ n  q₁ (init     , α _ , u , refl , (refl ,   ()) , prf₂)
 lem₄ ._ n  q₁ (init     , E   , u , refl , (refl ,   ()) , prf₂)
 lem₄ ._ n  q₁ (inj  p   , α _ , u , refl , (refl ,   ()) , prf₂)
 lem₄ ._ n  q₁ (inj  p   , E   , u , refl , (refl , prf₁) , prf₂) with Q₁? p q₀₁
 lem₄ ._ n  q₁ (inj .q₀₁ , E   , u , refl , (refl , prf₁) , prf₂) | yes refl = u , refl , prf₂
 lem₄ ._ n  q₁ (inj  p   , E   , u , refl , (refl ,   ()) , prf₂) | no p≢q₀₁


 lem₃ : ∀ q wᵉ uᵉ n q' vᵉ
        → wᵉ ≡ uᵉ ++ vᵉ
        → (q , uᵉ) ⊢ᵏₑ₁ n ─ (q' , [])
        → (inj q , wᵉ) ⊢ᵏ n ─ (inj q' , vᵉ)
 lem₃ q wᵉ .[] zero    .q  vᵉ w≡uv (refl , refl) = refl , w≡uv
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , α a , u₁ , refl , (refl , prf₁) , prf₂)
   = inj p , α a , u₁ ++ vᵉ , w≡uv , (refl , prf₁) , lem₃ p (u₁ ++ vᵉ) u₁ n q' vᵉ refl prf₂
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) with inj p ∈ᵈ δ (inj q) E | inspect (δ (inj q) E) (inj p)
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | true  | [ eq ]
   = inj p , E , u₁ ++ vᵉ , w≡uv , (refl , eq) , lem₃ p (u₁ ++ vᵉ) u₁ n q' vᵉ refl prf₂
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | false | [ eq ] with p ∈ᵈ δ₁ q E | inspect (δ₁ q E) p
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | false | [ () ] | true  | [ eq₁ ]
 lem₃ q wᵉ ._  (suc n)  q' vᵉ w≡uv (p , E   , u₁ , refl , (refl ,   ()) , prf₂) | false | [ eq ] | false | [ eq₁ ]

 lem₂ : ∀ wᵉ uᵉ n q vᵉ
        → wᵉ ≡ uᵉ ++ vᵉ
        → (q₀₁ , uᵉ) ⊢ᵏₑ₁ n ─ (q , [])
        → (init , E ∷ wᵉ) ⊢ᵏ suc n ─ (inj q , vᵉ)
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf with inj q₀₁ ∈ᵈ δ q₀ E | inspect (δ q₀ E) (inj q₀₁)
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | true  | [ eq ] = inj q₀₁ , E , wᵉ , refl , (refl , eq) , lem₃ q₀₁ wᵉ uᵉ n q vᵉ w≡uv prf
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | false | [ eq ] with Q₁? q₀₁ q₀₁
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | false | [ () ] | yes refl
 lem₂ wᵉ uᵉ n q vᵉ w≡uv prf | false | [ eq ] | no  q₀₁≢q₀₁ = ⊥-elim (q₀₁≢q₀₁ refl)

 {-
 lem₃ : ∀ q uᵉ n q₁ vᵉ
        → (q , uᵉ) ⊢ᵏₑ₁ n ─ (q₁ , vᵉ)
        → (inj q , uᵉ) ⊢ᵏ n ─ (inj q₁ , vᵉ)
 lem₃ q .vᵉ zero    .q  vᵉ (refl , refl) = refl , refl
 lem₃ q ._  (suc n)  q₁ vᵉ (p , α a , u₁ , refl , prf₁ , prf₂)
   = inj p , α a , u₁ , refl , prf₁ , lem₃ p u₁ n q₁ vᵉ prf₂
 lem₃ q ._  (suc n)  q₁ vᵉ (p , E   , u₁ , refl , (refl , prf₁) , prf₂) with inj p ∈ᵈ δ (inj q) E | inspect (δ (inj q) E) (inj p)
 lem₃ q ._  (suc n)  q₁ vᵉ (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | true  | [ eq ]
   = inj p , E , u₁ , refl , (refl , eq) , lem₃ p u₁ n q₁ vᵉ prf₂
 lem₃ q ._  (suc n)  q₁ vᵉ (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | false | [ eq ] with p ∈ᵈ δ₁ q E | inspect (δ₁ q E) p
 lem₃ q ._  (suc n)  q₁ vᵉ (p , E   , u₁ , refl , (refl , prf₁) , prf₂) | false | [ () ] | true  | [ eq₁ ]
 lem₃ q ._  (suc n)  q₁ vᵉ (p , E   , u₁ , refl , (refl ,   ()) , prf₂) | false | [ eq ] | false | [ eq₁ ]

 lem₂ : ∀ uᵉ n q₁
        → (q₀₁ , uᵉ) ⊢ᵏₑ₁ n ─ (q₁ , [])
        → (q₀ , E ∷ uᵉ)  ⊢ᵏ suc n ─ (inj q₁ , [])
 lem₂ uᵉ n q₁ prf with inj q₀₁ ∈ᵈ δ q₀ E | inspect (δ q₀ E) (inj q₀₁)
 lem₂ uᵉ n q₁ prf | true  | [ eq ] = inj q₀₁ , E , uᵉ , refl , (refl , eq) , lem₃ q₀₁ uᵉ n q₁ [] prf
 lem₂ uᵉ n q₁ prf | false | [ eq ] with Q₁? q₀₁ q₀₁
 lem₂ uᵉ n q₁ prf | false | [ () ] | yes refl
 lem₂ uᵉ n q₁ prf | false | [ eq ] | no  q₀₁≢q₀₁ = ⊥-elim (q₀₁≢q₀₁ refl)
-}
