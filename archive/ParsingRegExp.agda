module ParsingRegExp (Σ : Set) where

open import Data.List
open import Data.Vec renaming (_++_ to _++v_; map to vmap)
open import Data.Nat
open import Relation.Nullary
open import Data.Bool

open import Util
open import RegExpAutomata
open RegExp-Operations Σ

genState : (n : ℕ) → Vec State n
genState zero    = []
genState (suc n) = n ∷ genState n

∣2NFA : NFA Σ → NFA Σ → NFA Σ
∣2NFA (n₁ , Q₁ , δ₁ , q₀₁ , F₁) (n₂ , Q₂ , δ₂ , q₀₂ , F₂) = record { n = n' ; Q = genState n' ; δ = δ' ; q₀ = 0 ; F = F₁ ++ (map (_+_ (n₁ ∸ 1)) F₂) }
                                                            where
                                                              n' = n₁ + n₂ ∸ 1
                                                              δ' : State → Σ → Subset State
                                                              δ' 0 a = δ₁ 0 a ++ map (_+_ (n₁ ∸ 1)) (δ₂ 0 a)
                                                              δ' n a with n ≤? n₁ ∸ 1
                                                              ... | yes _  = δ₁ n a
                                                              ... | no  _  = map (_+_ (n₁ ∸ 1)) (δ₂ (n ∸ n₁ + 1) a)

∙2NFA : NFA Σ → NFA Σ → NFA Σ
∙2NFA (n₁ , Q₁ , δ₁ , q₀₁ , F₁) (n₂ , Q₂ , δ₂ , q₀₂ , F₂) = record { n = n' ; Q = genState n' ; δ = δ' ; q₀ = q₀₁; F = (map (_+_ n₁) F₂) }
                                                            where
                                                              n' = n₁ + n₂ ∸ 1
                                                              δ' : State → Σ → Subset State
                                                              δ' n a with n ≤? n₁ ∸ 1
                                                              ... | no  _ = map (_+_ n₁) (δ₂ (n ∸ n₁ + 1) a)
                                                              ... | yes _ with (n ∈? F₁) {_≡State?_}
                                                              ...   | true  = δ₁ n a ++ map (_+_ n₁) (δ₂ 0 a)
                                                              ...   | false = δ₁ n a

*2NFA : NFA Σ → NFA Σ
*2NFA (n₁ , Q₁ , δ₁ , q₀₁ , F₁) = record { n = n' ; Q = genState n' ; δ = δ' ; q₀ = 0; F = F' }
                                  where
                                    n' = n₁
                                    δ' : State → Σ → Subset State
                                    δ' 0 a = δ₁ 0 a
                                    δ' n a with (n ∈? F₁) {_≡State?_}
                                    ... | true  = δ₁ n a ++ δ₁ 0 a
                                    ... | false = δ₁ n a
                                    F' : Subset State
                                    F' with (zero ∈? F₁) {_≡State?_}
                                    ... | true  = F₁
                                    ... | false = 0 ∷ F₁

RegExp2NFA : {dec : DecEq Σ} → RegExp Σ → NFA Σ
RegExp2NFA Ø           = record { n = 1 ; Q = 0 ∷ [] ; δ = (λ q σ → 0 ∷ []) ; q₀ = 0 ; F = [] }
RegExp2NFA ε           = record { n = 2 ; Q = 1 ∷ 0 ∷ [] ; δ = (λ q σ → 1 ∷ []) ; q₀ = 0 ; F = (0 ∷ []) }
RegExp2NFA {eq?} (σ a) = record { n = 3 ; Q = 2 ∷ 1 ∷ 0 ∷ [] ; δ = δ' ; q₀ = 0 ; F = 1 ∷ [] }
                          where δ' : State → Σ → Subset State
                                δ' 0 x with eq? a x
                                ... | yes _ = 1 ∷ []
                                ... | no _  = 2 ∷ []
                                δ' _  _ = 2 ∷ []
RegExp2NFA {eq?} (e₁ ∣ e₂) = let e₁NFA = RegExp2NFA {eq?} e₁
                                 e₂NFA = RegExp2NFA {eq?} e₂
                             in ∣2NFA e₁NFA e₂NFA
RegExp2NFA {eq?} (e₁ ∙ e₂) = let e₁NFA = RegExp2NFA {eq?} e₁
                                 e₂NFA = RegExp2NFA {eq?} e₂
                             in ∙2NFA e₁NFA e₂NFA
RegExp2NFA {eq?} (e *)     = let eNFA = RegExp2NFA {eq?} e
                             in *2NFA eNFA
