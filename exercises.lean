import standard
open set

section proof_practice

--(many of these courtesy of Dan)

variables {P Q R : Prop}

example : P → P := 
sorry

example : P → (P → Q) → Q :=
sorry

example : P → P ∨ Q :=
sorry

example : P → (P → Q) → (Q → R) → R :=
sorry 

example : P → (P → Q → R) → Q → R :=
sorry 

example : ((P → Q) → R) → (P → Q) → R :=
sorry 

example : P → Q → P ∧ Q :=
sorry 

example : P ∧ Q → P :=
sorry 

theorem and_comm : P ∧ Q → Q ∧ P :=
sorry 

example : P ∧ (Q ∧ R) → Q :=
sorry 

example : P ∨ P → P :=
sorry 

example : P ∨ Q → Q ∨ P :=
sorry 

example : P → ¬ P → Q :=
sorry 

example : (R → Q) → ¬ Q → ¬ R :=
sorry 

end proof_practice

section set_proofs

variable {T : Type}

open set

example : ∀ (B : set T), B ⊆ B :=
sorry 

example : ∀ (A B C : set T), A ⊆ B → B ⊆ C → A ⊆ C :=
sorry 

example : ∀ (A B : set T) (x : T), x ∈ A → x ∈ B → x ∈ A ∩ B :=
sorry 

example : ∀ (A B : set T), A ∩ B ⊆ A :=
sorry 

end set_proofs
