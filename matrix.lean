/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nathaniel Thomas, Leonardo de Moura

Matrices

NCT: translation of Coq Mathematical Components library into Lean
(https://github.com/math-comp/math-comp/blob/master/mathcomp/algebra/matrix.v)
-/
import algebra.ring data.fin data.fintype theories.group_theory.perm 
import data.list algebra.module
open fin group_theory function nat eq.ops list

-- preliminary definitions

definition swap [reducible] {T : Type} (a b : T) [decidable_eq T] (r : T) : T :=
if r = a then b else
if r = b then a else r

theorem swap_inj {T : Type} (a b : T) [decidable_eq T] : 
        injective (swap a b) :=
sorry

definition swap_perm [reducible] {T : Type} (a b : T) 
           [decidable_eq T] [fintype T] : perm T :=
perm.mk (swap a b) (swap_inj a b)

lemma split_helper {a b c : ℕ} (h₁ : ¬ a < b) (h₂ : a < b + c) : a - b < c := 
have a ≥ b, from le_of_not_gt h₁,
sorry

definition lshift [reducible] m₁ m₂ (i : fin m₁) : fin (m₁ + m₂) := 
(lift i m₂)

definition rshift [reducible] m₁ m₂ (i : fin m₂) : fin (m₁ + m₂) := 
fin.mk ((fin.val i) + m₁) 
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

definition map [reducible] (f : A → B) (M : matrix A m n) : matrix B m n :=
λ i j, f (M[i,j])

definition map₂ (f : A → B → C) (M : matrix A m n) (N : matrix B m n) : matrix C m n :=
λ i j, f (M[i, j]) (N[i,j])

definition transpose [reducible] (M : matrix A m n) : matrix A n m :=
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

definition const_mx [reducible] (m n : nat) (a : A) : matrix A m n :=
λ i j, a

protected definition zero (m n : nat) : matrix A m n :=
λ i j, 0

protected definition add (M : matrix A m n) (N : matrix A m n) : 
                     matrix A m n :=
λ i j, M[i, j] + N[i, j]

protected definition sub (M : matrix A m n) (N : matrix A m n) : 
                     matrix A m n :=
λ i j, M[i, j] - N[i, j]

protected definition mul (M : matrix A m n) (N : matrix A n p) : 
                     matrix A m p :=
λ i j, fin.foldl has_add.add 0 (λ k : fin n, M[i,k] * N[k,j])

definition smul [reducible] (a : A) (M : matrix A m n) : matrix A m n :=
λ i j, a * M[i, j]

definition matrix_has_zero [reducible] [instance] (m n : nat) : 
           has_zero (matrix A m n) :=
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
definition castmx {m' n'} (eq_mn : m = m' × n = n') (M : matrix A m n) : 
           matrix A m' n' := 
sorry

definition row_perm [reducible] (p : perm (fin m)) (M : matrix A m n) :=
λ i j, M[(move_by i p), j]

definition col_perm [reducible] (p : perm (fin n)) (M : matrix A m n) :=
λ i j, M[i, (move_by j p)]

definition xrow [reducible] (i₁ i₂ : fin m) (M : matrix A m n) := 
           row_perm (swap_perm i₁ i₂) M

definition xcol [reducible] (j₁ j₂ : fin n) (M : matrix A m n) := 
           col_perm (swap_perm j₁ j₂) M

definition row' [reducible] (i0 : fin (succ m)) (M : matrix A (succ m) n) : 
           matrix A m n :=
λ (i : fin m) (j : fin n), 
  if i < i0 then M[(lift_succ i), j] else M[succ i, j]

definition col' [reducible] (j0 : fin (succ n)) (M : matrix A m (succ n)) : 
           matrix A m n :=
λ (i : fin m) (j : fin n), 
  if j < j0 then M[i, (lift_succ j)] else M[i, succ j]

section const

variables {a : A}

lemma trmx_const : transpose (const_mx m n a) = !const_mx a := 
rfl

lemma row_perm_const (p : perm (fin m)) : 
      row_perm p (const_mx m n a) = !const_mx a := 
matrix.ext (λ i j, rfl)

lemma col_perm_const (p : perm (fin n)) : 
      col_perm p (const_mx m n a) = !const_mx a :=
matrix.ext (λ i j, rfl)

lemma xrow_const (i₁ i₂ : fin m) : 
      xrow i₁ i₂ (const_mx m n a) = !const_mx a := 
rfl

lemma xcol_const (j₁ j₂ : fin n) : 
      xcol j₁ j₂ (const_mx m n a) = !const_mx a := 
rfl

lemma row_const (i₀ : fin m) : 
      get_row i₀ (const_mx m n a) = !const_mx a := 
rfl

lemma col_const (j₀ : fin n) : 
      get_col j₀ (const_mx m n a) = !const_mx a := 
rfl

lemma row'_const (i₀ : fin (succ m)) : 
      row' i₀ (const_mx (succ m) n a) = !const_mx a := sorry

lemma col'_const (j₀ : fin (succ n)) : 
      col' j₀ (const_mx m (succ n) a) = !const_mx a := sorry

end const

lemma row_perm1 (M : matrix A m n) : row_perm 1 M = M := sorry

lemma col_perm1 (M : matrix A m n) : col_perm 1 M = M := sorry

lemma row_permM s t (M : matrix A m n) : 
      row_perm (s * t) M = row_perm s (row_perm t M) := sorry

lemma col_permM s t (M : matrix A m n) : 
      col_perm (s * t) M = col_perm s (col_perm t M) := sorry

lemma col_row_permC s t (M : matrix A m n) : 
      col_perm s (row_perm t M) = row_perm t (col_perm s M) := sorry

postfix `ᵀ`:1500 := transpose

lemma transpose_invo (M : matrix A m n) : Mᵀᵀ = M := rfl

lemma transpose_inj : injective (λ M : matrix A m n, Mᵀ) := sorry

lemma tr_row_perm s (M : matrix A m n) : (row_perm s M)ᵀ = col_perm s Mᵀ := 
rfl

lemma tr_col_perm s (M : matrix A m n) : (col_perm s M)ᵀ = row_perm s Mᵀ := 
rfl

lemma tr_xrow i₁ i₂ (M : matrix A m n) : (xrow i₁ i₂ M)ᵀ = xcol i₁ i₂ Mᵀ := 
rfl

lemma tr_xcol j₁ j₂ (M : matrix A m n) : (xcol j₁ j₂ M)ᵀ = xrow j₁ j₂ Mᵀ := 
rfl

lemma row_id i (v : row_vector A n) : get_row i v = v := sorry

lemma col_id i (v : column_vector A n) : get_col i v = v := sorry

lemma row_eq m₁ m₂ i₁ i₂ (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) :
      get_row i₁ M₁ = get_row i₂ M₂ → M₁ i₁ = M₂ i₂ := sorry

lemma col_eq n₁ n₂ j₁ j₂ (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) :
      get_col j₁ M₁ = get_col j₂ M₂ → 
      (λ i : fin m, M₁ i j₁) = (λ i : fin m, M₂ i j₂) := sorry

--lemma row'_eq i₀ (M N : matrix A m n) : row' i₀ M = row' i₀ N →

lemma tr_row i₀ (M : matrix A m n) : (get_row i₀ M)ᵀ = get_col i₀ Mᵀ := 
rfl

lemma tr_row' i₀ (M : matrix A (succ m) n) : (row' i₀ M)ᵀ = col' i₀ Mᵀ := 
rfl

lemma tr_col j₀ (M : matrix A m n) : (get_col j₀ M)ᵀ = get_row j₀ Mᵀ := 
rfl

lemma tr_col' j₀ (M : matrix A m (succ n)) : (col' j₀ M)ᵀ = row' j₀ Mᵀ := 
rfl

-- concatenating two matrices, in either direction

section

variables {m₁ m₂ m₃ n₁ n₂ n₃ : ℕ}

definition row_mx [reducible] (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
           matrix A m (n₁ + n₂) :=
λ i j, dite ((fin.val j) < n₁) 
  (λ h,  M₁[i, (fin.mk (fin.val j) h)])
  (λ nh, M₂[i, (fin.mk ((fin.val j) - n₁) (split_helper nh (fin.is_lt j)))])

definition col_mx [reducible] (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
           matrix A (m₁ + m₂) n :=
λ i j, dite ((fin.val i) < m₁)
  (λ h,  M₁[(fin.mk (fin.val i) h), j])
  (λ nh, M₂[(fin.mk ((fin.val i) - m₁) (split_helper nh (fin.is_lt i))), j])

-- submatrices

definition lsubmx [reducible] (M : matrix A m (n₁ + n₂)) : matrix A m n₁ :=
λ i j, M[i, !lshift j]

definition rsubmx [reducible] (M : matrix A m (n₁ + n₂)) : matrix A m n₂ :=
λ i j, M[i, !rshift j]

definition usubmx [reducible] (M : matrix A (m₁ + m₂) n) : matrix A m₁ n :=
λ i j, M[!lshift i, j]

definition dsubmx [reducible] (M : matrix A (m₁ + m₂) n) : matrix A m₂ n :=
λ i j, M[!rshift i, j]

lemma row_mxEl (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      ∀ i j, (row_mx M₁ M₂)[i, (!lshift j)] = M₁[i, j] := sorry

lemma row_mxKl (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      lsubmx (row_mx M₁ M₂) = M₁ := sorry

lemma row_mxEr (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      ∀ i j, (row_mx M₁ M₂)[i, (!rshift j)] = M₂[i, j] := sorry

lemma row_mxKr (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      rsubmx (row_mx M₁ M₂) = M₂ := sorry

lemma hsubmxK (M : matrix A m (n₁ + n₂)) : 
      row_mx (lsubmx M) (rsubmx M) = M := sorry

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

lemma row_mx_const (a : A) : row_mx (const_mx m n₁ a) (const_mx m n₂ a) = 
      !const_mx a := sorry

lemma col_mx_const (a : A) : col_mx (const_mx m₁ n a) (const_mx m₂ n a) = 
      !const_mx a := sorry

lemma trmx_lsub (M : matrix A m (n₁ + n₂)) : (lsubmx M)ᵀ = usubmx Mᵀ := 
rfl

lemma trmx_rsub (M : matrix A m (n₁ + n₂)) : (rsubmx M)ᵀ = dsubmx Mᵀ := 
rfl

lemma tr_row_mx (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      (row_mx M₁ M₂)ᵀ = col_mx M₁ᵀ M₂ᵀ := 
rfl

lemma tr_col_mx (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
      (col_mx M₁ M₂)ᵀ = row_mx M₁ᵀ M₂ᵀ := 
rfl

lemma trmx_usub (M : matrix A (m₁ + m₂) n) : (usubmx M)ᵀ = lsubmx Mᵀ := 
rfl

lemma trmx_dsub (M : matrix A (m₁ + m₂) n) : (dsubmx M)ᵀ = rsubmx Mᵀ := 
rfl

lemma vsubmxK (M : matrix A (m₁ + m₂) n) : 
      col_mx (usubmx M) (dsubmx M) = M := sorry

lemma row_mxA (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) (M₃ : matrix A m n₃)
      : row_mx M₁ (row_mx M₂ M₃) == row_mx (row_mx M₁ M₂) M₃ := sorry

lemma col_mxA (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) (M₃ : matrix A m₃ n)
      : col_mx M₁ (col_mx M₂ M₃) == col_mx (col_mx M₁ M₂) M₃ := sorry

lemma row_row_mx i₀ (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      get_row i₀ (row_mx M₁ M₂) = row_mx (get_row i₀ M₁) (get_row i₀ M₂) :=
rfl

lemma col_col_mx j₀ (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
      get_col j₀ (col_mx M₁ M₂) = col_mx (get_col j₀ M₁) (get_col j₀ M₂) :=
rfl

lemma row'_row_mx i₀ (M₁ : matrix A (m+1) n₁) (M₂ : matrix A (m+1) n₂) : 
      row' i₀ (row_mx M₁ M₂) = row_mx (row' i₀ M₁) (row' i₀ M₂) := sorry

lemma col'_col_mx j₀ (M₁ : matrix A m₁ (n+1)) (M₂ : matrix A m₂ (n+1)) : 
      col' j₀ (col_mx M₁ M₂) = col_mx (col' j₀ M₁) (col' j₀ M₂) := sorry

lemma colKl j₁ (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      get_col (!lshift j₁) (row_mx M₁ M₂) = get_col j₁ M₁ := sorry

lemma colKr j₂ (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      get_col (!rshift j₂) (row_mx M₁ M₂) = get_col j₂ M₂ := sorry

lemma rowKu i₁ (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
      get_row (!lshift i₁) (col_mx M₁ M₂) = get_row i₁ M₁ := sorry

lemma rowKd i₂ (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
      get_row (!rshift i₂) (col_mx M₁ M₂) = get_row i₂ M₂ := sorry

/- elaborator issues?

lemma col'Kl j₁ (M₁ : matrix A m (n₁ + 1)) (M₂ : matrix A m n₂) :
      col' (!lshift j₁) (row_mx M₁ M₂) = row_mx (col' j₁ M₁) M₂ := sorry

lemma row'Ku i₁ (M₁ : matrix A (m₁ + 1) n) (M₂ : matrix A m₂ n) :
      row' (!lshift i₁) (col_mx M₁ M₂) = col_mx (row' i₁ M₁) M₂ := sorry

lemma col'Kr j₂ (M₁ : matrix A m n₁) (M₂ : matrix A m n₂) : 
      col' (!rshift j₂) (row_mx M₁ M₂) == row_mx M₁ (col' j₂ M₂) := sorry

lemma row'Kd i₂ (M₁ : matrix A m₁ n) (M₂ : matrix A m₂ n) : 
      row' (!rshift i₂) (col_mx M₁ M₂) == col_mx M₁ (row' i₂ M₂) := sorry
-/
end


-- block matrices

section block

variables {m₁ m₂ n₁ n₂ : ℕ}


definition block_mx [reducible] (Mul Mur Mdl Mdr) : 
           matrix A (m₁ + m₂) (n₁ + n₂) :=
           col_mx (row_mx Mul Mur) (row_mx Mdl Mdr)

lemma eq_block_mx (Mul Mur Mdl Mdr Nul Nur Ndl Ndr) : 
      (@block_mx A _ m₁ m₂ n₁ n₂ Mul Mur Mdl Mdr) = block_mx Nul Nur Ndl Ndr
      → Mul = Nul ∧ Mur = Nur ∧ Mdl = Ndl ∧ Mdr = Ndr := sorry

lemma block_mx_const (a : A) : 
      block_mx (!const_mx a) (!const_mx a) (!const_mx a) (!const_mx a) = 
        const_mx (m₁ + m₂) (n₁ + n₂) a := sorry

section cut_block

variable (M : matrix A (m₁ + m₂) (n₁ + n₂))

definition ulsubmx [reducible] := lsubmx (usubmx M)
definition ursubmx [reducible] := rsubmx (usubmx M)
definition dlsubmx [reducible] := lsubmx (dsubmx M)
definition drsubmx [reducible] := rsubmx (dsubmx M)

--lemma submxK : block_mx ulsubmx ursubmx dlsubmx drsubmx = M := sorry

end cut_block

section cat_block

variables {Mul : matrix A m₁ n₁} {Mur : matrix A m₁ n₂}
variables {Mdl : matrix A m₂ n₁} {Mdr : matrix A m₂ n₂}

definition M [reducible] := block_mx Mul Mur Mdl Mdr

/- elaborator issues ?

lemma block_mxEul (i j) :
      M[(!lshift i), (!lshift j)] = Mul[i, j] := sorry

lemma block_mxKul : ulsubmx M = Mul := sorry

lemma block_mxEv : M = col_mx (row_mx Mul Mur) (row_mx Mdl Mdr) := sorry
-/
end cat_block

end block

section tr_cut_block

variables {m₁ m₂ n₁ n₂ : ℕ}
variable M : matrix A (m₁ + m₂) (n₁ + n₂)

lemma trmx_ulsub : (ulsubmx M)ᵀ = ulsubmx Mᵀ := rfl

lemma trmx_ursub : (ursubmx M)ᵀ = dlsubmx Mᵀ := rfl

lemma trmx_dlsub : (dlsubmx M)ᵀ = ursubmx Mᵀ := rfl

lemma trmx_drsub : (drsubmx M)ᵀ = drsubmx Mᵀ := rfl

end tr_cut_block

section tr_block

variables {m₁ m₂ n₁ n₂ : ℕ}

variables {Mul : matrix A m₁ n₁} {Mur : matrix A m₁ n₂}
variables {Mdl : matrix A m₂ n₁} {Mdr : matrix A m₂ n₂}

lemma tr_block_mx : 
      (block_mx Mul Mur Mdl Mdr)ᵀ = block_mx Mulᵀ Mdlᵀ Murᵀ Mdrᵀ := 
sorry

lemma block_mxEh : 
      block_mx Mul Mur Mdl Mdr = row_mx (col_mx Mul Mdl) (col_mx Mur Mdr) :=
sorry

end tr_block

lemma block_mxA {m₁ m₂ m₃ n₁ n₂ n₃}
      (M₁₁ : matrix A m₁ n₁) (M₁₂ : matrix A m₁ n₂) (M₁₃ : matrix A m₁ n₃)
      (M₂₁ : matrix A m₂ n₁) (M₂₂ : matrix A m₂ n₂) (M₂₃ : matrix A m₂ n₃)
      (M₃₁ : matrix A m₃ n₁) (M₃₂ : matrix A m₃ n₂) (M₃₃ : matrix A m₃ n₃) :
block_mx M₁₁ (row_mx M₁₂ M₁₃) (col_mx M₂₁ M₃₁) (block_mx M₂₂ M₂₃ M₃₂ M₃₃) ==
block_mx (block_mx M₁₁ M₁₂ M₂₁ M₂₂) (col_mx M₁₃ M₂₃) (row_mx M₃₁ M₃₂) :=
sorry

section map_matrix

variables {f : A → B} [comm_ring B]

section one_matrix

variables {M : matrix A m n} 

lemma map_trmx : (map f M)ᵀ = map f Mᵀ := rfl

lemma map_const_mx (a : A) : 
      map f (@const_mx _ _ m n a) = !const_mx (f a) := rfl

lemma map_row (i) : map f (get_row i M) = get_row i (map f M) := rfl

lemma map_col (j) : map f (get_col j M) = get_col j (map f M) := rfl

lemma map_row' {M : matrix A (m+1) n} (i₀) : 
      map f (row' i₀ M) = row' i₀ (map f M) := sorry

lemma map_col' {M : matrix A m (n+1)} (j₀) : 
      map f (col' j₀ M) = col' j₀ (map f M) := sorry

lemma map_row_perm (s) : map f (row_perm s M) = row_perm s (map f M) := 
rfl

lemma map_col_perm (s) : map f (col_perm s M) = col_perm s (map f M) := 
rfl

lemma map_xrow (i₁ i₂) : map f (xrow i₁ i₂ M) = xrow i₁ i₂ (map f M) := 
rfl

lemma map_xcol (i₁ i₂) : map f (xcol i₁ i₂ M) = xcol i₁ i₂ (map f M) := 
rfl

end one_matrix

section block

variables {m₁ m₂ n₁ n₂ : ℕ}
variables {Mul : matrix A m₁ n₁} {Mur : matrix A m₁ n₂}
variables {Mdl : matrix A m₂ n₁} {Mdr : matrix A m₂ n₂}
variables {Nh : matrix A m₁ (n₁ + n₂)} {Nv : matrix A (m₁ + m₂) n₁}
variable  {N : matrix A (m₁ + m₂) (n₁ + n₂)}

lemma map_row_mx : map f (row_mx Mul Mur) = row_mx (map f Mul) (map f Mur) :=
sorry

lemma map_col_mx : map f (col_mx Mul Mdl) = col_mx (map f Mul) (map f Mdl) :=
sorry

lemma map_block_mx : map f (block_mx Mul Mur Mdl Mdr) = 
      block_mx (map f Mul) (map f Mur) (map f Mdl) (map f Mdr) := sorry

lemma map_lsubmx : map f (lsubmx Nh) = lsubmx (map f Nh) := rfl

lemma map_rsubmx : map f (rsubmx Nh) = rsubmx (map f Nh) := rfl

lemma map_usubmx : map f (usubmx Nv) = usubmx (map f Nv) := rfl

lemma map_dsubmx : map f (dsubmx Nv) = dsubmx (map f Nv) := rfl

lemma map_ulsubmx : map f (ulsubmx N) = ulsubmx (map f N) := rfl

lemma map_ursubmx : map f (ursubmx N) = ursubmx (map f N) := rfl

lemma map_dlsubmx : map f (dlsubmx N) = dlsubmx (map f N) := rfl

lemma map_drsubmx : map f (drsubmx N) = drsubmx (map f N) := rfl

end block

end map_matrix


-- matrix ring module, graded ring, and ring structures

section matrix_algebra

section ring_module

-- basis

definition delta_mx (i₀ j₀) : matrix A m n :=
λ i j, if (i = i₀ ∧ j = j₀) then 1 else 0

lemma scale1mx (M : matrix A m n) : 1 ⬝ M = M := sorry

lemma scalemxDl (x y) (M : matrix A m n) : (x + y) ⬝ M = x ⬝ M + y ⬝ M := 
sorry

lemma scalemxDr (x) (M N : matrix A m n) : x ⬝ (M + N) = x ⬝ M + x ⬝ N := 
sorry

lemma scalemxA (x y) (M : matrix A m n) : (x * y) ⬝ M = x ⬝ (y ⬝ M) := 
sorry

protected definition neg (M : matrix A m n) : matrix A m n :=
λ i j, -M[i, j]

definition matrix_has_neg [reducible] [instance] (m n : nat) : 
           has_neg (matrix A m n) :=
has_neg.mk (matrix.neg)

protected lemma add_left_inv (M : matrix A m n) : -M + M = 0 :=
matrix.ext (λ i j, !add.left_inv)

definition matrix_left_module [reducible] [instance] : 
           left_module A (matrix A m n) :=
⦃ left_module,
add := add,
zero := zero,
neg := neg,
add_left_inv := matrix.add_left_inv,
zero_add := matrix.zero_add,
add_zero := matrix.add_zero,
add_assoc := add.assoc,
add_comm := add.comm,
smul := smul,
smul_left_distrib := scalemxDr,
smul_right_distrib := scalemxDl,
mul_smul := scalemxA,
one_smul := scale1mx
⦄

lemma scalemx_const (a b : A) : 
      a ⬝ (const_mx m n b) = !const_mx (a * b) := rfl

lemma matrix_sum_delta (M : matrix A m n) :
      M = ∑ i ← upto m, ∑ j ← upto n, M[i, j] ⬝ (delta_mx i j) := sorry

end ring_module

lemma trmx_delta (i j) : (@delta_mx A m n _ i j)ᵀ = delta_mx j i := 
sorry

/-lemma row_sum_delta (n) (u : row_vector A n) : 
      u = ∑ j ← upto n, (u 0 j) * (@delta_mx A m n _ 0 j) := sorry-/


end matrix_algebra


definition permanent (M : matrix A n n) (i : fin n) : A :=
∑ s ← all_perms, ∏ i ← upto n, M[i, move_by i s]

/-definition determinant (M : matrix A n n) (i : fin n) : A :=
∑ s ← all_perms, (-1) ^ s * ∏ i ← upto n, M[i, move_by i s]-/



end
end matrix
