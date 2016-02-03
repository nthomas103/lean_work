/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nathaniel Thomas, Leonardo de Moura

Matrices

NCT: translation of Coq Mathematical Components library into Lean
(https://github.com/math-comp/math-comp/blob/master/mathcomp/algebra/matrix.v)
-/
import algebra.ring data.fin data.fintype theories.group_theory.perm data.list
open fin group_theory function nat eq.ops list

-- preliminary definitions

definition swap {T : Type} (a b : T) [decidable_eq T] (r : T) : T :=
if r = a then b else
if r = b then a else r

theorem swap_inj {T : Type} (a b : T) [decidable_eq T] : injective (swap a b) :=
sorry

definition swap_perm {T : Type} (a b : T) [decidable_eq T] [fintype T] : perm T :=
perm.mk (swap a b) (swap_inj a b)

lemma split_helper {a b c : ℕ} (h₁ : ¬ a < b) (h₂ : a < b + c) : a - b < c := 
have a ≥ b, from le_of_not_gt h₁,
sorry

definition lshift m₁ m₂ (i : fin m₁) : fin (m₁ + m₂) := (lift i m₂)

definition rshift m₁ m₂ (i : fin m₂) : fin (m₁ + m₂) := fin.mk ((fin.val i) + m₁) 
                 (calc (fin.val i) + m₁ < m₂ + m₁ : add_lt_add_right (fin.is_lt i) m₁
                                   ...  = m₁ + m₂ : nat.add_comm m₂ m₁)

/-
definition split_subproof {m n} {i : fin (m + n)} : ¬ (i < m) → i - m < n := sorry

definition split' m n (i : fin (m + n)) : (fin m) ⊎ (fin n) := 
dite (fin.val i < m) 
  (λ h, sum.inl (fin.mk (fin.val i) h)) 
  (λ nh, sum.inr (fin.mk ((fin.val i) - m) (split_subproof nh)))
-/

-- matrix

definition matrix [reducible] (A : Type) (m n : nat) := fin m → fin n → A

namespace matrix

definition vector [reducible] (A : Type) (n : nat) := fin n → A
definition row_vector [reducible] (A : Type) (n : nat) := matrix A 1 n
definition column_vector [reducible] (A : Type) (n : nat) := matrix A n 1

definition vector_of_column_vector [reducible] [coercion] (A : Type) (n : nat) 
(v : vector A n) : column_vector A n := 
λ i j, v i

definition column_vector_of_matrix [reducible] [coercion] (A : Type) (n : nat)
(cv : column_vector A n) : matrix A n 1 := cv

variables {A B C : Type} {m n p : nat}

definition val [reducible] (M : matrix A m n) (i : fin m) (j : fin n) : A :=
M i j

definition get_row [reducible] (row : fin m) (M : matrix A m n) : row_vector A n :=
λ i j, M row j

definition get_col [reducible] (col : fin n) (M : matrix A m n) : column_vector A m :=
λ i j, M i col

namespace ops
notation M `[` i `, ` j `]` := val M i j
end ops

open ops


/-definition list_to_vector {T : Type} (l : list T) : vector T (length l) := 
@fintype.list_to_fun (fin (length l)) T _ _ l sorry
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l
-/

protected lemma ext {M N : matrix A m n} (h : ∀ i j, M[i,j] = N[i, j]) : M = N :=
funext (λ i, funext (λ j, h i j))

protected lemma has_decidable_eq [h : decidable_eq A] (m n : nat) : decidable_eq (matrix A m n) :=
_

definition to_matrix (f : fin m → fin n → A) : matrix A m n :=
f

definition map (f : A → B) (M : matrix A m n) : matrix B m n :=
λ i j, f (M[i,j])

definition map₂ (f : A → B → C) (M : matrix A m n) (N : matrix B m n) : matrix C m n :=
λ i j, f (M[i, j]) (N[i,j])

definition transpose (M : matrix A m n) : matrix A n m :=
λ i j, M[j, i]

definition symmetric (M : matrix A n n) :=
transpose M = M

section
variable [r : comm_ring A]
include r

definition identity (n : nat) : matrix A n n :=
λ i j, if i = j then 1 else 0

definition I {n : nat} : matrix A n n :=
identity n

definition const_mx (m n : nat) (a : A) : matrix A m n :=
λ i j, a

protected definition zero (m n : nat) : matrix A m n :=
λ i j, 0

protected definition add (M : matrix A m n) (N : matrix A m n) : matrix A m n :=
λ i j, M[i, j] + N[i, j]

protected definition sub (M : matrix A m n) (N : matrix A m n) : matrix A m n :=
λ i j, M[i, j] - N[i, j]

protected definition mul (M : matrix A m n) (N : matrix A n p) : matrix A m p :=
λ i j, fin.foldl has_add.add 0 (λ k : fin n, M[i,k] * N[k,j])

definition smul (a : A) (M : matrix A m n) : matrix A m n :=
λ i j, a * M[i, j]

definition matrix_has_zero [reducible] [instance] (m n : nat) : has_zero (matrix A m n) :=
has_zero.mk (matrix.zero m n)

definition matrix_has_one [reducible] [instance] (n : nat) : has_one (matrix A n n) :=
has_one.mk (identity n)

definition matrix_has_add [reducible] [instance] (m n : nat) : has_add (matrix A m n) :=
has_add.mk matrix.add

definition matrix_has_mul [reducible] [instance] (n : nat) : has_mul (matrix A n n) :=
has_mul.mk matrix.mul

infix ` × ` := mul
infix `⬝`    := smul

protected lemma add_zero (M : matrix A m n) : M + 0 = M :=
matrix.ext (λ i j, !add_zero)

protected lemma zero_add (M : matrix A m n) : 0 + M = M :=
matrix.ext (λ i j, !zero_add)

protected lemma add.comm (M : matrix A m n) (N : matrix A m n) : M + N = N + M :=
matrix.ext (λ i j, !add.comm)

protected lemma add.assoc (M : matrix A m n) (N : matrix A m n) (P : matrix A m n) : (M + N) + P = M + (N + P) :=
matrix.ext (λ i j, !add.assoc)

definition is_diagonal (M : matrix A n n) :=
∀ i j, i = j ∨ M[i, j] = 0

definition is_zero (M : matrix A m n) :=
∀ i j, M[i, j] = 0

definition is_upper_triangular (M : matrix A n n) :=
∀ i j : fin n, i > j → M[i, j] = 0

definition is_lower_triangular (M : matrix A n n) :=
∀ i j : fin n, i < j → M[i, j] = 0

definition inverse (M : matrix A n n) (N : matrix A n n) :=
M * N = I ∧ N * M = I

definition invertible (M : matrix A n n) :=
∃ N, inverse M N

---- added by NCT:

-- castmx might not be needed
definition castmx {m' n'} (eq_mn : m = m' × n = n') (M : matrix A m n) : matrix A m' n' := 
sorry

definition row_perm (p : perm (fin m)) (M : matrix A m n) :=
λ i j, M[(move_by i p), j]

definition col_perm (p : perm (fin n)) (M : matrix A m n) :=
λ i j, M[i, (move_by j p)]

definition xrow (i₁ i₂ : fin m) (M : matrix A m n) := row_perm (swap_perm i₁ i₂) M

definition xcol (j₁ j₂ : fin n) (M : matrix A m n) := col_perm (swap_perm j₁ j₂) M

definition row' (i0 : fin (succ m)) (M : matrix A (succ m) n) : matrix A m n :=
λ (i : fin m) (j : fin n), if i < i0 then M[(lift_succ i), j] else M[succ i, j]

definition col' (j0 : fin (succ n)) (M : matrix A m (succ n)) : matrix A m n :=
λ (i : fin m) (j : fin n), if j < j0 then M[i, (lift_succ j)] else M[i, succ j]

section const

variables {a : A}

lemma trmx_const : transpose (const_mx m n a) = !const_mx a := sorry

lemma row_perm_const (p : perm (fin m)) : row_perm p (const_mx m n a) = !const_mx a :=
matrix.ext (λ i j, rfl)

lemma col_perm_const (p : perm (fin n)) : col_perm p (const_mx m n a) = !const_mx a :=
matrix.ext (λ i j, rfl)

lemma xrow_const (i₁ i₂ : fin m) : xrow i₁ i₂ (const_mx m n a) = !const_mx a := sorry

lemma xcol_const (j₁ j₂ : fin n) : xcol j₁ j₂ (const_mx m n a) = !const_mx a := sorry

lemma row_const (i₀ : fin m) : get_row i₀ (const_mx m n a) = !const_mx a := sorry

lemma col_const (j₀ : fin n) : get_col j₀ (const_mx m n a) = !const_mx a := sorry

lemma row'_const (i₀ : fin (succ m)) : row' i₀ (const_mx (succ m) n a) = !const_mx a := sorry

lemma col'_const (j₀ : fin (succ n)) : col' j₀ (const_mx m (succ n) a) = !const_mx a := sorry

end const

lemma row_perm1 (M : matrix A m n) : row_perm 1 M = M := sorry

lemma col_perm1 (M : matrix A m n) : col_perm 1 M = M := sorry

lemma row_permM s t (M : matrix A m n) : row_perm (s * t) M = row_perm s (row_perm t M) := sorry

lemma col_permM s t (M : matrix A m n) : col_perm (s * t) M = col_perm s (col_perm t M) := sorry

lemma col_row_permC s t (M : matrix A m n) : 
      col_perm s (row_perm t M) = row_perm t (col_perm s M) := sorry

postfix `ᵀ`:1500 := transpose

lemma transpose_invo (M : matrix A m n) : Mᵀᵀ = M := sorry

lemma transpose_inj : injective (λ M : matrix A m n, Mᵀ) := sorry

lemma tr_row_perm s (M : matrix A m n) : (row_perm s M)ᵀ = col_perm s Mᵀ := sorry

lemma tr_col_perm s (M : matrix A m n) : (col_perm s M)ᵀ = row_perm s Mᵀ := sorry

lemma tr_xrow i₁ i₂ (M : matrix A m n) : (xrow i₁ i₂ M)ᵀ = xcol i₁ i₂ Mᵀ := sorry

lemma tr_xcol j₁ j₂ (M : matrix A m n) : (xcol j₁ j₂ M)ᵀ = xrow j₁ j₂ Mᵀ := sorry

lemma row_id i (v : row_vector A n) : get_row i v = v := sorry

lemma col_id i (v : column_vector A n) : get_col i v = v := sorry

lemma row_eq m₁ m₂ i₁ i₂ (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) :
      get_row i₁ M₁ = get_row i₂ M₂ → M₁ i₁ = M₂ i₂ := sorry

lemma col_eq n₁ n₂ j₁ j₂ (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) :
      get_col j₁ M₁ = get_col j₂ M₂ → (λ i : fin m, M₁ i j₁) = (λ i : fin m, M₂ i j₂) := sorry

--lemma row'_eq i₀ (M N : matrix A m n) : row' i₀ M = row' i₀ N →

lemma tr_row i₀ (M : matrix A m n) : (get_row i₀ M)ᵀ = get_col i₀ Mᵀ := sorry

lemma tr_row' i₀ (M : matrix A (succ m) n) : (row' i₀ M)ᵀ = col' i₀ Mᵀ := sorry

lemma tr_col j₀ (M : matrix A m n) : (get_col j₀ M)ᵀ = get_row j₀ Mᵀ := sorry

lemma tr_col' j₀ (M : matrix A m (succ n)) : (col' j₀ M)ᵀ = row' j₀ Mᵀ := sorry

-- concatenating two matrices, in either direction

section

variables {m₁ m₂ m₃ n₁ n₂ n₃ : ℕ}

definition row_mx (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : matrix A m (n₁ + n₂) :=
λ i j, dite ((fin.val j) < n₁) 
       (λ h,  M₁[i, (fin.mk (fin.val j) h)])
       (λ nh, M₂[i, (fin.mk ((fin.val j) - n₁) (split_helper nh (fin.is_lt j)))])

definition col_mx (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : matrix A (m₁ + m₂) n :=
λ i j, dite ((fin.val i) < m₁)
       (λ h,  M₁[(fin.mk (fin.val i) h), j])
       (λ nh, M₂[(fin.mk ((fin.val i) - m₁) (split_helper nh (fin.is_lt i))), j])

-- submatrices

definition lsubmx (M : matrix A m (n₁ + n₂)) : matrix A m n₁ :=
λ i j, M[i, !lshift j]

definition rsubmx (M : matrix A m (n₁ + n₂)) : matrix A m n₂ :=
λ i j, M[i, !rshift j]

definition usubmx (M : matrix A (m₁ + m₂) n) : matrix A m₁ n :=
λ i j, M[!lshift i, j]

definition dsubmx (M : matrix A (m₁ + m₂) n) : matrix A m₂ n :=
λ i j, M[!rshift i, j]

lemma row_mxEl (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      ∀ i j, (row_mx M₁ M₂)[i, (!lshift j)] = M₁[i, j] := sorry

lemma row_mxKl (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      lsubmx (row_mx M₁ M₂) = M₁ := sorry

lemma row_mxEr (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      ∀ i j, (row_mx M₁ M₂)[i, (!rshift j)] = M₂[i, j] := sorry

lemma row_mxKr (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      rsubmx (row_mx M₁ M₂) = M₂ := sorry

lemma hsubmxK (M : matrix A m (n₁ + n₂)) : row_mx (lsubmx M) (rsubmx M) = M := sorry

lemma col_mxEl (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
      ∀ i j, (col_mx M₁ M₂)[(!lshift i), j] = M₁[i, j] := sorry

lemma col_mxKl (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
      usubmx (col_mx M₁ M₂) = M₁ := sorry

lemma col_mxEr (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
      ∀ i j, (col_mx M₁ M₂)[(!rshift i), j] = M₂[i, j] := sorry

lemma col_mxKr (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
      dsubmx (col_mx M₁ M₂) = M₂ := sorry

lemma eq_row_mx (M₁ N₁: matrix A m n₁) (M₂ N₂: matrix A m n₂) : 
      row_mx M₁ M₂ = row_mx N₁ N₂ → M₁ = N₁ ∧ M₂ = N₂ := sorry

lemma eq_col_mx (M₁ N₁: matrix A m₁ n) (M₂ N₂: matrix A m₂ n) : 
      col_mx M₁ M₂ = col_mx N₁ N₂ → M₁ = N₁ ∧ M₂ = N₂ := sorry

lemma row_mx_const (a : A) : row_mx (const_mx m n₁ a) (const_mx m n₂ a) = !const_mx a := sorry

lemma col_mx_const (a : A) : col_mx (const_mx m₁ n a) (const_mx m₂ n a) = !const_mx a := sorry

lemma trmx_lsub (M : matrix A m (n₁ + n₂)) : (lsubmx M)ᵀ = usubmx Mᵀ := sorry

lemma trmx_rsub (M : matrix A m (n₁ + n₂)) : (rsubmx M)ᵀ = dsubmx Mᵀ := sorry

lemma tr_row_mx (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : (row_mx M₁ M₂)ᵀ = col_mx M₁ᵀ M₂ᵀ := 
sorry

lemma tr_col_mx (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : (col_mx M₁ M₂)ᵀ = row_mx M₁ᵀ M₂ᵀ := 
sorry

lemma trmx_usub (M : matrix A (m₁ + m₂) n) : (usubmx M)ᵀ = lsubmx Mᵀ := sorry

lemma trmx_dsub (M : matrix A (m₁ + m₂) n) : (dsubmx M)ᵀ = rsubmx Mᵀ := sorry

lemma vsubmxK (M : matrix A (m₁ + m₂) n) : col_mx (usubmx M) (dsubmx M) = M := sorry

lemma row_mxA (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) (M₃ : matrix A m n₃) :
      row_mx M₁ (row_mx M₂ M₃) == row_mx (row_mx M₁ M₂) M₃ := sorry

lemma col_mxA (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) (M₃ : matrix A m₃ n) :
      col_mx M₁ (col_mx M₂ M₃) == col_mx (col_mx M₁ M₂) M₃ := sorry


definition permanent (M : matrix A n n) (i : fin n) : A :=
∑ s ← all_perms, ∏ i ← upto n, M[i, move_by i s]

/-definition determinant (M : matrix A n n) (i : fin n) : A :=
∑ s ← all_perms, (-1) ^ s * ∏ i ← upto n, M[i, move_by i s]-/


end


end
end matrix
