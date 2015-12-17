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
 lem₁ (.a ∷ [])    refl | true  | [ eq ] = accept , refl , 1 , accept , α a , [] , inj₁ (refl , λ ()) , (refl , eq) , (refl , refl)
 lem₁ (.a ∷ [])    refl | false | [ eq ] with dec a a
 lem₁ (.a ∷ [])    refl | false | [ () ] | yes refl
 lem₁ (.a ∷ [])    refl | false | [ eq ] | no  a≢a   = ⊥-elim (a≢a refl)
 lem₁ (x ∷ y ∷ xs) ()

module Lᴿ⊇Lᴺ where
 lem₂ : ∀ a xs n
        → ¬ (accept , (α a) ∷ xs) ⊢ᵏ n ─ (accept , [])
 lem₂ a xs zero    (refl   ,  ())
 lem₂ a xs (suc n) (init   , .(α a) , ._ , inj₁ (refl ,    _) , (_ , ()) ,   _)
 lem₂ a xs (suc n) (init   , .E     , ._ , inj₂ (refl , refl) , (_ , ()) ,   _)
 lem₂ a xs (suc n) (accept , .(α a) , ._ , inj₁ (refl ,    _) , (_ , ()) ,   _)
 lem₂ a xs (suc n) (accept , .E     , ._ , inj₂ (refl , refl) , (_ ,  _) , prf)
   = lem₂ a xs n prf

 lem₁ : Lᴿ e ⊇ Lᵉᴺ nfa
 lem₁ [] (init   , () , _)
 lem₁ [] (accept , refl , zero  , () , refl)
 lem₁ [] (accept , refl , suc n , _      ,  _ ,  _  , inj₁ (() , _)      , _           ,   _)
 lem₁ [] (accept , refl , suc n , init   , .E , .[] , inj₂ (refl , refl) , _           , prf)
   = lem₁ [] (accept , refl , n , prf)
 lem₁ [] (accept , refl , suc n , accept , .E ,  _  , inj₂ (refl , refl) , (_ , ())    ,   _)
 lem₁ ( x ∷ []) (init   , () , _)
 lem₁ ( x ∷ []) (accept , refl , zero  , ()     , ())
 lem₁ ( x ∷ []) (accept , refl , suc n , init   , .(α _) ,  _  , inj₁ (refl   ,  _) , (_ , ()) ,   _)
 lem₁ ( x ∷ []) (accept , refl , suc n , init   , .E     ,  _  , inj₂ (refl , refl) , _        , prf)
   = lem₁ (x ∷ []) (accept , refl , n , prf)
 lem₁ ( x ∷ []) (accept , refl , suc n , accept , .(α _) , .[] , inj₁ (refl , x≢E)  , (_ , _ ) ,   _) with dec a x
 lem₁ (.a ∷ []) (accept , refl , suc n , accept , .(α _) , .[] , inj₁ (refl , x≢E)  , (_ , _ ) ,   _) | yes refl = refl
 lem₁ ( x ∷ []) (accept , refl , suc n , accept , .(α _) , .[] , inj₁ (refl , x≢E)  , (_ , ()) ,   _) | no a≢x
 lem₁ ( x ∷ []) (accept , refl , suc n , accept , .E     ,  _  , inj₂ (_    , refl) , (_ , ()) ,   _)
 lem₁ ( x ∷ y ∷ xs) (init   , ()   , _)
 lem₁ ( x ∷ y ∷ xs) (accept , refl , zero  , ()     , ())
 lem₁ ( x ∷ y ∷ xs) (accept , refl , suc n , init   , .(α _) , ._ , inj₁ (refl , _)    , (_ , ()) ,   _)
 lem₁ ( x ∷ y ∷ xs) (accept , refl , suc n , init   , .E     , ._ , inj₂ (refl , refl) , _        , prf)
   = lem₁ (x ∷ y ∷ xs) (accept , refl , n , prf)
 lem₁ ( x ∷ y ∷ xs) (accept , refl , suc n , accept , .(α _) , ._ , inj₁ (refl , _)    , (_ , _)  , prf)
   = ⊥-elim (lem₂ y (toΣᵉ* xs) n prf)
 lem₁ ( x ∷ y ∷ xs) (accept , refl , suc n , accept , .E     , ._ , inj₂ (refl , refl) , (_ , _)  , prf)
   = ⊥-elim (lem₂ x (toΣᵉ* (y ∷ xs)) n prf)
