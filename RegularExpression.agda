{-
  Here the Regular Language and Regular Expressions are 
  defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 2.2: Regular sets, their generators, and their recognizers
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 07-01-2016
-}
open import Util
module RegularExpression (Σ : Set)(dec : DecEq Σ) where


open import Data.List
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product hiding (Σ)
open import Data.Sum
open import Data.Nat
open import Data.Empty

open import Language Σ dec renaming (Ø to ø)
open import Subset hiding (Ø ; ⟦_⟧ ; _⋃_)

-- Regular Language
-- section 2.2.1: Regular Sets and Regular Expressions
data Regular : Language → Set₁ where
  nullL : ∀ {L} → L ≈ ø  → Regular L
  empty : ∀ {L} → L ≈ ⟦ε⟧ → Regular L
  singl : ∀ {L} → (a : Σ) → L ≈ ⟦ a ⟧ → Regular L
  union : ∀ {L} L₁ L₂ → Regular L₁ → Regular L₂ → L ≈ L₁ ⋃ L₂ → Regular L
  conca : ∀ {L} L₁ L₂ → Regular L₁ → Regular L₂ → L ≈ L₁ • L₂ → Regular L
  kleen : ∀ {L} L₁    → Regular L₁ → L ≈ L₁ ⋆ → Regular L


-- Regular expressions
-- section 2.2.1: Regular Sets and Regular Expressions
infix 11 _∣_
infix 12 _∙_
infix 13 _*
data RegExp : Set where
  Ø   : RegExp 
  ε   : RegExp 
  σ   : Σ → RegExp
  _∣_ : RegExp → RegExp → RegExp
  _∙_ : RegExp → RegExp → RegExp
  _*  : RegExp → RegExp


-- Language denoted by regular expressions
-- section 2.2.1: Regular Sets and Regular Expressions
Lᴿ : RegExp → Language
Lᴿ Ø         = ø
Lᴿ ε         = ⟦ε⟧
Lᴿ (σ a)     = ⟦ a ⟧
Lᴿ (e₁ ∣ e₂) = Lᴿ e₁ ⋃ Lᴿ e₂
Lᴿ (e₁ ∙ e₂) = Lᴿ e₁ • Lᴿ e₂
Lᴿ (e *)     = (Lᴿ e) ⋆


-- A language is Regular if and only if there is a Regular Expression denoting it
Soundness : ∀ L → Σ[ e ∈ RegExp ] (Lᴿ e ≈ L) → Regular L
Completeness : ∀ L → Regular L → Σ[ e ∈ RegExp ] (Lᴿ e ≈ L)

L⇔Lᴿ : ∀ L → Regular L ⇔ ( Σ[ e ∈ RegExp ] (Lᴿ e ≈ L) )
L⇔Lᴿ L = Completeness L , Soundness L


Lemma₁ : ∀ e → Regular (Lᴿ e)
Lemma₁ Ø = nullL ≈-refl
Lemma₁ ε = empty ≈-refl
Lemma₁ (σ x) = singl x ≈-refl
Lemma₁ (e ∣ e₁) = union (Lᴿ e) (Lᴿ e₁) (Lemma₁ e) (Lemma₁ e₁) ((λ x x₁ → x₁) , (λ x x₁ → x₁))
Lemma₁ (e ∙ e₁) = conca (Lᴿ e) (Lᴿ e₁) (Lemma₁ e) (Lemma₁ e₁) ((λ x x₁ → x₁) , (λ x x₁ → x₁))
Lemma₁ (e *) = kleen (Lᴿ e) (Lemma₁ e) ((λ x x₁ → x₁) , (λ x x₁ → x₁))


Soundness _ (Ø , Ø≈L) = nullL (≈-sym Ø≈L)
Soundness _ (ε , ⟦ε⟧≈L) = empty (≈-sym ⟦ε⟧≈L)
Soundness _ (σ a , ⟦a⟧≈L) = singl a (≈-sym ⟦a⟧≈L)
Soundness _ (e₁ ∣ e₂ , prf) = union (Lᴿ e₁) (Lᴿ e₂) (Lemma₁ e₁) (Lemma₁ e₂) (≈-sym prf)
Soundness _ (e₁ ∙ e₂ , prf) = conca (Lᴿ e₁) (Lᴿ e₂) (Lemma₁ e₁) (Lemma₁ e₂) (≈-sym prf)
Soundness _ (e * , prf) = kleen (Lᴿ e) (Lemma₁ e) (≈-sym prf)


Completeness ._ (nullL L≈Ø) = Ø , proj₂ L≈Ø , proj₁ L≈Ø
Completeness ._ (empty L≈⟦ε⟧) = ε , proj₂ L≈⟦ε⟧ , proj₁ L≈⟦ε⟧
Completeness ._ (singl a ⟦a⟧≈L) = σ a , proj₂ ⟦a⟧≈L , proj₁ ⟦a⟧≈L
Completeness ._  (union L₁ L₂ RL₁ RL₂ L≈L₁⋃L₂) with Completeness L₁ RL₁ | Completeness L₂ RL₂
Completeness ._  (union L₁ L₂ RL₁ RL₂ L≈L₁⋃L₂) | e₁ , Lᴿe₁=L₁ | e₂ , Lᴿe₂=L₂ = e₁ ∣ e₂ , (lem₁ , lem₂)
  where
    lem₁ : Lᴿ e₁ ⋃ Lᴿ e₂ ⊆ _
    lem₁ w (inj₁ w∈Lᴿe₁) = proj₂ L≈L₁⋃L₂ w (inj₁ (proj₁ Lᴿe₁=L₁ w w∈Lᴿe₁))
    lem₁ w (inj₂ w∈Lᴿe₂) = proj₂ L≈L₁⋃L₂ w (inj₂ (proj₁ Lᴿe₂=L₂ w w∈Lᴿe₂))
    lem₂ : Lᴿ e₁ ⋃ Lᴿ e₂ ⊇ _
    lem₂ w w∈L with proj₁ L≈L₁⋃L₂ w w∈L
    ... | inj₁ w∈L₁ = inj₁ (proj₂ Lᴿe₁=L₁ w w∈L₁)
    ... | inj₂ w∈L₂ = inj₂ (proj₂ Lᴿe₂=L₂ w w∈L₂)
Completeness ._  (conca L₁ L₂ RL₁ RL₂ L≈L₁•L₂) with Completeness L₁ RL₁ | Completeness L₂ RL₂
Completeness ._  (conca L₁ L₂ RL₁ RL₂ L≈L₁•L₂) | e₁ , Lᴿe₁=L₁ | e₂ , Lᴿe₂=L₂ = e₁ ∙ e₂ , (lem₁ , lem₂)
  where
    lem₁ : Lᴿ e₁ • Lᴿ e₂ ⊆ _
    lem₁ w (u , v , u∈Lᴿe₁ , v∈Lᴿe₂ , w≡uv) = proj₂ L≈L₁•L₂ w (u , v , proj₁ Lᴿe₁=L₁ u u∈Lᴿe₁ , proj₁ Lᴿe₂=L₂ v v∈Lᴿe₂ , w≡uv)
    lem₂ : Lᴿ e₁ • Lᴿ e₂ ⊇ _
    lem₂ w w∈L with proj₁ L≈L₁•L₂ w w∈L
    ... | (u , v , u∈L₁ , v∈L₂ , w≡uv) = u , v , proj₂ Lᴿe₁=L₁ u u∈L₁ , proj₂ Lᴿe₂=L₂ v v∈L₂ , w≡uv
Completeness ._  (kleen L RL L≈L⋆) with Completeness L RL
Completeness ._  (kleen L RL L≈L⋆) | e , Lᴿe=L = e * , (lem₁ , lem₂)
  where
    lem₁ : (Lᴿ e) ⋆ ⊆ _
    lem₁ w (n , w∈Lᴿeⁿ) = proj₂ L≈L⋆ w (n , lem n w w∈Lᴿeⁿ)
      where
        lem : ∀ n → (Lᴿ e) ^ n ⊆ L ^ n
        lem zero    w w∈Lᴿe = w∈Lᴿe
        lem (suc n) w (u , v , u∈Lᴿe , v∈Lᴿeⁿ , w≡uv) = u , v , proj₁ Lᴿe=L u u∈Lᴿe , lem n v v∈Lᴿeⁿ , w≡uv
    lem₂ : (Lᴿ e) ⋆ ⊇ _
    lem₂ w prf with proj₁ L≈L⋆ w prf
    ... | n , w∈Lⁿ = n , lem n w w∈Lⁿ
      where
        lem : ∀ n → (Lᴿ e) ^ n ⊇ L ^ n
        lem zero    w w∈L = w∈L
        lem (suc n) w (u , v , u∈L , v∈Lⁿ , w≡uv) = u , v , proj₂ Lᴿe=L u u∈L , lem n v v∈Lⁿ , w≡uv
