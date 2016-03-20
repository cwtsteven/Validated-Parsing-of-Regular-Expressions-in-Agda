# Parsing-Regular-Expressions

This project is part of an undergraduate course.

postulate list

All these postulates regards the 

-- these can be proved using similar method in computing ε-closure

Translation/DFA-MDFA.agda:282:    postulate q1-lem₁ : ∀ k → Steps k ≈ᵈ Steps (suc k) → D-States ≈ D-Statesᵏ k

Translation/DFA-MDFA.agda:286:    postulate q2-lem₁ : ∀ p q → (p , q) ∈ D-States ⇔ (p , q) ∈ᵈ Steps Size

-- this is really the heart of the proof

Translation/DFA-MDFA.agda:302:    postulate lem₄ : (p , q) ∉ᵈ Steps Size → ¬ (p ≠ q)

-- once we proved the above lemmas, this one will follow

Translation/DFA-MDFA.agda:326:    postulate Dec-≠ : ∀ p q → Dec (p ≠ q)

belows are minor proofs

-- make sense

RelationTable.agda:48:  postulate ∀ab∈table : ∀ a b → (a , b) ∈ⱽ table

RelationTable.agda:51:  postulate unique-table : Unique table

RelationTable.agda:54:  postulate It-lem : {n : ℕ}(as : Vec (A × A) (suc n))

-- represent states in vector

Translation/DFA-MDFA.agda:157:    postulate ∣Q∣-1 : ℕ

Translation/DFA-MDFA.agda:158:    postulate Q? : DecEq Q

Translation/DFA-MDFA.agda:159:    postulate It : Vec Q (suc ∣Q∣-1)

Translation/DFA-MDFA.agda:160:    postulate ∀q∈It : ∀ q → q ∈ⱽ It

Translation/DFA-MDFA.agda:161:    postulate unique : Unique It

-- make sense

Translation/DFA-MDFA.agda:211:    postulate ⟦pq⟧-lem : ∀ p q qs → (p , q) ∈ᵈ ⟦ p , q ⟧ᵈ {{Dec-Pair}} ⋃ᵈ qs


-- this should hold as Basis build from comparing p ∈ᵈ? F | q ∈ᵈ? F

Translation/DFA-MDFA.agda:214:    postulate Basis-lem₂ : ∀ p q → (δ* p [] ∈ᵈ F × δ* q [] ∉ᵈ F ⊎ δ* p [] ∉ᵈ F × δ* q [] ∈ᵈ F) → (p , q) 
∈ᵈ Basis

-- we can iterate the set of alphbets 

Translation/DFA-MDFA.agda:239:    postulate Dec-mark : ∀ p q qs → Dec (Σ[ a ∈ Σ ] ( (δ p a , δ q a) ∈ᵈ qs × (δ p a ∈ᵈ F × δ q a ∉ᵈ F ⊎ δ p a ∉ᵈ F × δ q a ∈ᵈ F) ))

-- this should hold as we keep the Basis while iterate the Steps

Translation/DFA-MDFA.agda:264:    postulate steps-lem₂ : ∀ p q → (p , q) ∈ᵈ Basis → (p , q) ∈ᵈ Steps Size
