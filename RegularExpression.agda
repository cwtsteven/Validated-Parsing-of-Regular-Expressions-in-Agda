{-
  Here the Regular Language and Regular Expressions are 
  defined according to:
    The Theory of Parsing, Translation and Compiling (Vol. 1 : Parsing)
    Section 2.2: Regular sets, their generators, and their recognizers
      by Alfred V. Aho and Jeffery D. Ullman

  Steven Cheung 2015.
  Version 07-01-2016
-}
open import Util hiding (_^_)
module RegularExpression (Σ : Set)(dec : DecEq Σ) where


open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (Σ)
open import Data.Sum
open import Data.Nat

open import Language Σ dec renaming (Ø to ø)
open import Subset hiding (Ø ; ⟦_⟧ ; _⋃_)

-- Regular Language
-- section 2.2.1: Regular Sets and Regular Expressions
data Regular : Language → Set₁ where
  nullL : Regular ø
  empty : Regular ⟦ε⟧
  singleton : (a : Σ) → Regular ⟦ a ⟧
  union : ∀ L₁ L₂ → Regular L₁ → Regular L₂ → Regular (L₁ ⋃ L₂)
  conca : ∀ L₁ L₂ → Regular L₁ → Regular L₂ → Regular (L₁ • L₂)
  kleen : ∀ L     → Regular L → Regular (L ⋆)


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
Lemma₁ : ∀ e → Regular (Lᴿ e)
Lemma₁ Ø = nullL
Lemma₁ ε = empty
Lemma₁ (σ x) = singleton x
Lemma₁ (e ∣ e₁) = union (Lᴿ e) (Lᴿ e₁) (Lemma₁ e) (Lemma₁ e₁)
Lemma₁ (e ∙ e₁) = conca (Lᴿ e) (Lᴿ e₁) (Lemma₁ e) (Lemma₁ e₁)
Lemma₁ (e *) = kleen (Lᴿ e) (Lemma₁ e)


Soundness : ∀ L → Σ[ e ∈ RegExp ] (Lᴿ e ≈ L) → Regular L
Soundness _ (Ø , Ø≈L) = ≈-subst (λ L → Regular L) Ø≈L nullL
Soundness _ (ε , ⟦ε⟧≈L) = ≈-subst (λ L → Regular L) ⟦ε⟧≈L empty
Soundness _ (σ a , ⟦a⟧≈L) = ≈-subst (λ L → Regular L) ⟦a⟧≈L (singleton a)
Soundness _ (e₁ ∣ e₂ , prf) = ≈-subst (λ L → Regular L) prf (union (Lᴿ e₁) (Lᴿ e₂) (Lemma₁ e₁) (Lemma₁ e₂))
Soundness _ (e₁ ∙ e₂ , prf) = ≈-subst (λ L → Regular L) prf (conca (Lᴿ e₁) (Lᴿ e₂) (Lemma₁ e₁) (Lemma₁ e₂))
Soundness _ (e * , prf) = ≈-subst (λ L → Regular L) prf (kleen (Lᴿ e) (Lemma₁ e))


Completeness : ∀ L → Regular L → Σ[ e ∈ RegExp ] (Lᴿ e ≈ L)
Completeness ._ nullL = Ø , (λ x x₁ → x₁) , (λ x x₁ → x₁)
Completeness ._ empty = ε , (λ x x₁ → x₁) , (λ x x₁ → x₁)
Completeness ._ (singleton a) = σ a , (λ x₁ x₂ → x₂) , (λ x₁ x₂ → x₂)
Completeness ._  (union L₁ L₂ RL₁ RL₂) with Completeness L₁ RL₁ | Completeness L₂ RL₂
Completeness ._  (union L₁ L₂ RL₁ RL₂) | e₁ , Lᴿe₁=L₁ | e₂ , Lᴿe₂=L₂ = e₁ ∣ e₂ , (lem₁ , lem₂)
  where
    lem₁ : Lᴿ (e₁ ∣ e₂) ⊆ (L₁ ⋃ L₂)
    lem₁ w (inj₁ w∈Le₁) = inj₁ (proj₁ Lᴿe₁=L₁ w w∈Le₁)
    lem₁ w (inj₂ w∈Le₂) = inj₂ (proj₁ Lᴿe₂=L₂ w w∈Le₂)
    lem₂ : Lᴿ (e₁ ∣ e₂) ⊇ (L₁ ⋃ L₂)
    lem₂ w (inj₁ w∈L₁) = inj₁ (proj₂ Lᴿe₁=L₁ w w∈L₁)
    lem₂ w (inj₂ w∈L₂) = inj₂ (proj₂ Lᴿe₂=L₂ w w∈L₂)
Completeness ._  (conca L₁ L₂ RL₁ RL₂) with Completeness L₁ RL₁ | Completeness L₂ RL₂
Completeness ._  (conca L₁ L₂ RL₁ RL₂) | e₁ , Lᴿe₁=L₁ | e₂ , Lᴿe₂=L₂ = e₁ ∙ e₂ , (lem₁ , lem₂)
  where
    lem₁ : Lᴿ (e₁ ∙ e₂) ⊆ (L₁ • L₂)
    lem₁ w (u , v , u∈Lᴿe₁ , v∈Lᴿe₂ , w≡uv) = u , v , proj₁ Lᴿe₁=L₁ u u∈Lᴿe₁ , proj₁ Lᴿe₂=L₂ v v∈Lᴿe₂ , w≡uv
    lem₂ : Lᴿ (e₁ ∙ e₂) ⊇ (L₁ • L₂)
    lem₂ w (u , v , u∈L₁ , v∈L₂ , w≡uv) = u , v , proj₂ Lᴿe₁=L₁ u u∈L₁ , proj₂ Lᴿe₂=L₂ v v∈L₂ , w≡uv
Completeness ._  (kleen L RL) with Completeness L RL
Completeness ._  (kleen L RL) | e , Lᴿe=L = e * , (lem₁ , lem₂)
  where
    lem₁ : Lᴿ (e *) ⊆ L ⋆
    lem₁ w (n , w∈Lᴿeⁿ) = n , lem n w w∈Lᴿeⁿ
      where
        lem : ∀ n → (Lᴿ e) ^ n ⊆ L ^ n
        lem zero    w w∈Lᴿe = w∈Lᴿe
        lem (suc n) w (u , v , u∈Lᴿe , v∈Lᴿeⁿ , w≡uv) = u , v , proj₁ Lᴿe=L u u∈Lᴿe , lem n v v∈Lᴿeⁿ , w≡uv
    lem₂ : Lᴿ (e *) ⊇ L ⋆
    lem₂ w (n , w∈Lⁿ) = n , lem n w w∈Lⁿ
      where
        lem : ∀ n → (Lᴿ e) ^ n ⊇ L ^ n
        lem zero    w w∈L = w∈L
        lem (suc n) w (u , v , u∈L , v∈Lⁿ , w≡uv) = u , v , proj₂ Lᴿe=L u u∈L , lem n v v∈Lⁿ , w≡uv


L⇔Lᴿ : ∀ L → Regular L ⇔ ( Σ[ e ∈ RegExp ] (Lᴿ e ≈ L) )
L⇔Lᴿ L = Completeness L , Soundness L
