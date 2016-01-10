{-
  This module contains the following proofs:

  Steven Cheung 2015.
  Version 10-01-2016
-}
open import Util
module Correctness.RegExpToe-NFA.Singleton-lemmas (Σ : Set)(dec : DecEq Σ)(a : Σ) where

open import Data.List
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Data.Product hiding (Σ)
open import Data.Empty
open import Data.Nat

open import Subset
open import Subset.DecidableSubset renaming (_∈_ to _∈ᵈ_)
open import Language Σ
open import RegularExpression Σ
open import Automata Σ
open import Translation Σ dec
open import State

e : RegExp
e = σ a

nfa : ε-NFA
nfa = regexToε-NFA e

open ε-NFA nfa
open ε-NFA-Operations nfa

module Lᴿ⊆Lᴺ where
 lem₁ : Lᴿ e ⊆ Lᵉᴺ nfa
 lem₁ []           ()
 lem₁ (.a ∷ [])    refl with accept ∈ᵈ δ init (α a) | inspect (δ init (α a)) accept
 lem₁ (.a ∷ [])    refl | true  | [ eq ]
   = α a ∷ [] , refl , accept , refl , 1 , accept , α a , [] , refl , (refl , eq) , (refl , refl)
 lem₁ (.a ∷ [])    refl | false | [ eq ] with dec a a
 lem₁ (.a ∷ [])    refl | false | [ () ] | yes refl
 lem₁ (.a ∷ [])    refl | false | [ eq ] | no  a≢a
   = ⊥-elim (a≢a refl)
 lem₁ (x ∷ y ∷ xs) ()

module Lᴿ⊇Lᴺ where
 lem₂ : ∀ u uᵉ n
        → u ≢ []
        → u ≡ toΣ* uᵉ
        → ¬ (accept , uᵉ) ⊢ᵏ n ─ (accept , [])
 lem₂ .[] .[] zero    xs≢[] refl (refl , refl) = ⊥-elim (xs≢[] refl)
 lem₂  _  ._  (suc n) xs≢[] prf₁ (_ , _   , _ , refl , (_ , ()) , _)

 lem₁ : Lᴿ e ⊇ Lᵉᴺ nfa
 lem₁ _ (_ , _ , init   , () , _)
 lem₁ [] (.[] , refl , accept , refl , zero  , () , refl)
 lem₁ [] (._  , ()   , accept , refl , suc n , _ , α _ , _  , refl , _        ,  _)
 lem₁ [] (._  , w≡wᵉ , accept , refl , suc n , _ , E   , uᵉ , refl , (_ , ()) ,  _)
 
 lem₁ ( x ∷ []) (.[] , ()   , accept , refl , zero  , ()     , refl)
 lem₁ ( x ∷ []) (._  , _    , accept , refl , suc n , init   , α  _ , _  , refl , (_ ,   ()) ,   _)
 lem₁ ( x ∷ []) (._  , _    , accept , refl , suc n , accept , α  _ , _  , refl , _          ,   _) with dec a x
 lem₁ (.a ∷ []) (._  , _    , accept , refl , suc n , accept , α  _ , _  , refl , _          ,   _) | yes refl = refl
 lem₁ ( x ∷ []) (._  , _    , accept , refl , suc n , accept , α  b , _  , refl , _          ,   _) | no  a≢x  with dec a b
 lem₁ ( x ∷ []) (._  , w≡wᵉ , accept , refl , suc n , accept , α .a , uᵉ , refl , (_ , refl) ,   _) | no  a≢x  | yes refl
   = ⊥-elim (List-lem₁ {xs = toΣ* uᵉ} {ys = []} a≢x (sym w≡wᵉ))
 lem₁ ( x ∷ []) (._  , _    , accept , refl , suc n , accept , α  b , _  , refl , (_ ,   ()) ,   _) | no  a≢x  | no  a≢b
 lem₁ ( x ∷ []) (._  , w≡wᵉ , accept , refl , suc n , _      , E    , uᵉ , refl , (_ ,   ()) ,   _)
 
 lem₁ ( x ∷ y ∷ xs) (._ , _    , accept , refl , zero  , ()     , refl)
 lem₁ ( x ∷ y ∷ xs) (._ , _    , accept , refl , suc n , init   , α _ , _  , refl , (_ , ())  ,   _)
 lem₁ ( x ∷ y ∷ xs) (._ , w≡wᵉ , accept , refl , suc n , accept , α b , uᵉ , refl , _         , prf)
   = ⊥-elim (lem₂ (y ∷ xs) uᵉ n (λ ()) (cong tail w≡wᵉ) prf)
 lem₁ ( x ∷ y ∷ xs) (._ , w≡wᵉ , accept , refl , suc n , _      , E   , uᵉ , refl , (_ , ())  ,   _)
