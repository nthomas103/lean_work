/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Author: Nathaniel Thomas

Formalization of "Quantum Lambda Calculus" paper by Selinger and Valiron.
-/
import data.nat data.examples.vector algebra.group_bigops data.fin data.list
open fin nat list

variables (unitary_group : Type)

inductive vid := | Id : nat → vid

inductive const := 
| new     : const
| meas    : const
| unitary : unitary_group → const

inductive ty :=
| qbit  : ty
| bang  : ty → ty
| lolly : ty → ty → ty
| top   : ty
| prod  : ty → ty → ty
| sum   : ty → ty → ty

prefix `!-`:52  := ty.bang
infixr `⊸`:51   := ty.lolly
infixl `⊗`:47   := ty.prod
infixl `⊕`:49   := ty.sum 
notation `⊤`    := ty.top
definition bit  := ty.top ⊕ ty.top

definition bangmult (t : ty) : nat → ty 
| bangmult 0     := t
| bangmult (n+1) := !- (bangmult n)
notation `!^`:42 := λ a b, bangmult b a

definition prodmult (t : ty) : nat → ty
| prodmult 0     := t
| prodmult 1     := t
| prodmult (n+1) := (prodmult n) ⊗ t
notation `⊗^`:47 := λ a b, prodmult b a

definition summult  (t : ty) : nat → ty
| summult 0     := t
| summult 1     := t
| summult (n+1) := (summult n) ⊕ t
notation `⊕^`:49 := λ a b, summult b a

lemma bangbang : ∀ n T, !-(!^ n T) = !^ (n + 1) T := 
assume n T, rfl

section subtyping

  open ty

  inductive subty : ty → ty → Prop :=
  infixl `<:`:50 := subty
  | sqbit  : ∀ m n, m = 0 ∨ n ≥ 1 → (!^n qbit) <: (!^m qbit)
  | stop   : ∀ m n, m = 0 ∨ n ≥ 1 → (!^n ⊤)    <: (!^m ⊤)
  | sprod  : ∀ A₁ A₂ B₁ B₂ m n, m = 0 ∨ n ≥ 1 → A₁ <: B₁ → A₂ <: B₂ → !^n (A₁ ⊗ A₂) <: !^m (B₁ ⊗ B₂)
  | splus  : ∀ A₁ A₂ B₁ B₂ m n, m = 0 ∨ n ≥ 1 → A₁ <: B₁ → A₂ <: B₂ → !^n (A₁ ⊕ A₂) <: !^m (B₁ ⊕ B₂)
  | slolly : ∀ A₁ A₂ B₁ B₂ m n, m = 0 ∨ n ≥ 1 → A₁ <: B₁ → A₂ <: B₂ → !^n (B₁ ⊸ A₂) <: !^m (A₁ ⊸ B₂)

  infixl `<:`:50 := subty

  open subty

  lemma sub_refl  : reflexive subty :=
  sorry

  lemma sub_trans : transitive subty :=
  sorry

  lemma bang_exist : ∀ A B, A <: (!-B) → ∃ A', A = !-A' := 
  assume A B sub, sorry

  lemma bit_qbit₁ : !-(bit ⊸ ty.qbit) <: !-(!-bit ⊸ ty.qbit) :=
  slolly (!-bit) ty.qbit bit ty.qbit 1 1 sorry 
  (splus ty.top ty.top ty.top ty.top 0 1 sorry (stop 0 0 sorry) (stop 0 0 sorry)) 
  (sqbit 0 0 sorry)

end subtyping

definition context := list (vid × ty)

definition context_union (Δ₁ Δ₂ : list (vid × ty)) := Δ₁ ++ Δ₂

inductive tm :=
| tconst  : tm --const → tm
| tvar    : vid → tm
| tlambda : vid → ty → tm → tm
| tapp    : tm → tm → tm
| tpair   : tm → tm → tm
| tunit   : tm
| tlet    : vid → vid → tm → tm → tm
| tinjl   : tm → tm
| tinjr   : tm → tm
| tmatch  : vid → vid → tm → tm → tm → tm
| trec    : vid → vid → tm → tm → tm

inductive has_type : context → tm → ty → Prop :=
notation Γ ▹ t ∈ T := (has_type Γ t T)
| Tax1  : ∀ Δ x A B, A <: B → (((x,A) :: Δ) ▹ (tm.tvar x) ∈ B)
| Tinjl : ∀ Δ n M A B, (Δ ▹ M ∈ (!^n A)) → (Δ ▹ (tm.tinjl M) ∈ (!^n (A ⊕ B)))
| Tinjr : ∀ Δ n M A B, (Δ ▹ M ∈ (!^n B)) → (Δ ▹ (tm.tinjr M) ∈ (!^n (A ⊕ B)))
| Ttop  : ∀ Δ n, (Δ ▹ tm.tunit ∈ (!^n ⊤))
| Tl1   : ∀ Δ x M A B, (((x,A) :: Δ) ▹ M ∈ B) → (Δ ▹ (tm.tlambda x A M) ∈ B)

notation Γ ▹ t ∈ T := has_type Γ t T
--open has_type


lemma bitI₁ (n : ℕ) : [] ▹ tm.tinjr tm.tunit ∈ !^n bit := !Tinjr !Ttop
lemma bitI₂ (n : ℕ) : [] ▹ tm.tinjl tm.tunit ∈ !^n bit := !Tinjl !Ttop


inductive val : tm → Prop :=
| vconst  : val tm.tconst
| vvar    : ∀ x, val (tm.tvar x)
| vlambda : ∀ x A M, val (tm.tlambda x A M)
| vinjr   : ∀ t, val t → val (tm.tinjr t)
| vinjl   : ∀ t, val t → val (tm.tinjl t)
| vunit   : val tm.tunit
| vpair   : ∀ t1 t2, val t1 → val t2 → val (tm.tpair t1 t2)









definition balanced {n : nat} (f : vector (fin 2) n → fin 2) : Prop := sorry

lemma balanced_decidable : ∀ {n} (f : vector (fin 2) n → fin 2), decidable (balanced f) := sorry

