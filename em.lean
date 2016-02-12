import standard data.matrix theories.group_theory.perm
import theories.group_theory.hom algebra.module
open nat fin real matrix matrix.ops list group_theory finset int
open algebra


section fn_module

  variables {R S : Type} 
  variable  [field R]

  definition fn_add (f g : S → R) (x : S) := f x + g x

  definition fn_mul (a : R) (f : S → R) (x : S) := a * f x

  definition fn_zero (x : S) : R := 0

  definition fn_neg (f : S → R) (x : S) := - f x

  proposition fn_add_assoc (f g h : S → R) : 
    (fn_add (fn_add f g) h) = (fn_add f (fn_add g h)) :=
  sorry

  proposition fn_zero_add (f : S → R) :
    fn_add fn_zero f = f :=
  sorry

  proposition fn_add_zero (f : S → R) :
    fn_add f fn_zero = f := 
  sorry

  proposition fn_add_left_inv (f : S → R) :
    fn_add (fn_neg f) f = fn_zero := 
  sorry

  proposition fn_add_comm (f g : S → R) :
    fn_add f g = fn_add g f :=
  sorry

  proposition fn_smul_left_distrib : ∀ (a : R) (f g : S → R), 
    fn_mul a (fn_add f g) = (fn_add (fn_mul a f) (fn_mul a g)) := 
  sorry

  proposition fn_smul_right_distrib : ∀ (a b : R) (f : S → R),
    fn_mul (a + b) f = fn_add (fn_mul a f) (fn_mul b f) :=
  sorry

  proposition fn_smul_mul : ∀ (a b : R) (f : S → R),
    fn_mul (a * b) f = fn_mul a (fn_mul b f) := 
  sorry

  proposition fn_one_smul : ∀ (f : S → R), fn_mul 1 f = f :=
  sorry

  definition fn_module [instance] : vector_space R (S → R) :=
  ⦃
    vector_space,
    smul               := fn_mul,
    add                := fn_add,
    add_assoc          := fn_add_assoc,
    zero               := fn_zero,
    zero_add           := fn_zero_add,
    add_zero           := fn_add_zero,
    neg                := fn_neg,
    add_left_inv       := fn_add_left_inv,
    add_comm           := fn_add_comm,
    smul_left_distrib  := fn_smul_left_distrib,
    smul_right_distrib := fn_smul_right_distrib,
    mul_smul           := fn_smul_mul,
    one_smul           := fn_one_smul
  ⦄

end fn_module




definition vector [reducible] (T : Type) (n : ℕ) := fin n → T
definition vc [reducible] (n : ℕ) := vector ℝ n
definition mx [reducible] (m n : ℕ) := matrix ℝ m n
definition tn [reducible] (T : Type) (n m : ℕ) := (vector (fin n) m) → T

postfix `ᵀ`:1500 := transpose

definition skew_symm {n} {T : Type} [comm_ring T] (A : matrix T n n) := 
λ i j, A[i, j] = -A[j, i]

constant A' : vector (vc 4 → ℝ) 4

constant D {n} : vector ((vc n → ℝ) → (vc n → ℝ)) n

definition F' : matrix (vc 4 → ℝ) 4 4 := 
λ μ ν x, (D μ) (A' ν) x - (D ν) (A' μ) x

constant j' : vector (vc 4 → ℝ) 4

constant π : ℝ

constant homogeneous_maxwell' : 
     ∀ μ ρ σ x, (D μ) (F' ρ σ) x + (D ρ) (F' σ μ) x + (D σ) (F' μ ρ) x = 0

constant heterogeneous_maxwell' : 
     ∀ ν x, (∑ μ ← upto 4, (D μ) (F' μ ν) x) = - 4 * π * (j' ν) x

attribute [simp] heterogeneous_maxwell'

lemma charge_conservation : ∀ x, (∑ μ ← upto 4, (D μ) (j' μ) x) = 0 := 
sorry

/-lemma deriv_comm : ∀ T μ ν x, (D μ) ((D ν) T) x = (D ν) ((D μ) T) x :=
sorry-/

--lemma F_skew : skew_symm F := sorry

constant sgn {A : Type} [h : fintype A] (p : perm A) : ℤ
constant sgn_range {A : Type} [h : fintype A] (p : perm A) : 
         sgn p = 1 ∨ sgn p = -1
--constant sgn_hom {A : Type} [h : fintype A] : is_hom_class sgn

definition vec_is_fintype [instance] {A : Type} {n} : 
           fintype (vector A n) := sorry

noncomputable definition symmetrize {n m : ℕ} (T : tn (vc n → ℝ) n m) : 
                         tn (vc n → ℝ) n m :=
λ v, (fact m)⁻¹ • ∑ σ ← all_perms, T (move_by v σ)

noncomputable definition anti_symmetrize {n m : ℕ} 
  (T : tn (vc n → ℝ) n m) : tn (vc n → ℝ) n m :=
λ v, (fact m)⁻¹ • ∑ σ ← all_perms, sgn σ • (T (move_by v σ))

definition vhead {A : Type} {n} (v : vector A (n+1)) : A := 
v (mk 0 !zero_lt_succ)
definition vtail {A : Type} {n} (v : vector A (n+1)) : vector A n :=
λ i, v (mk (val i + 1) (add_lt_add_right (is_lt i) 1))

noncomputable definition d {n m : ℕ} (T : tn (vc n → ℝ) n m) : 
                         tn (vc n → ℝ) n (m+1) :=
anti_symmetrize (λ v, D (vhead v) (T (vtail v)))

theorem d2_0 [simp] {n m} {T : tn _ n m} {μ x} : d (d T) μ x = 0 := 
sorry

constant A : tn (vc 4 → ℝ) 4 1

noncomputable definition F := d A

attribute [reducible] F

theorem homogeneous_maxwell {μ} {x} : (d F) μ x = 0 := by inst_simp

--constant ε {n} {μ : vector (fin n) n} : ℤ

definition hodge (T : tn (vc 4 → ℝ) 4 2) : tn (vc 4 → ℝ) 4 2 := 
sorry
prefix `⋆`:2000 := hodge

constant J : tn (vc 4 → ℝ) 4 3

constant heterogeneous_maxwell : J = d ⋆ F

theorem continuity_equation {μ x} : (d J) μ x = 0 := calc
(d J) μ x = d (d ⋆ F) μ x : {heterogeneous_maxwell}
...       = 0             : d2_0

