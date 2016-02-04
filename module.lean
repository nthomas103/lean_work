/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad

Modules and vector spaces over a ring.
-/
import algebra.field data --data.matrix
open eq.ops set function fin

definition vector [reducible] (A : Type) (n : ℕ) := fin n → A

--definition matrix [reducible] (A : Type) (m n : ℕ) := fin m → fin n → A

structure has_scalar [class] (F V : Type) :=
(smul : F → V → V)

infixl ` • `:73 := has_scalar.smul

/- modules over a ring -/

structure left_module [class] (R M : Type) [ringR : ring R]
  extends add_comm_group M, has_scalar R M :=
(smul_left_distrib : ∀ (r : R) (x y : M), smul r (add x y) = (add (smul r x) (smul r y)))
(smul_right_distrib : ∀ (r s : R) (x : M), smul (ring.add r s) x = (add (smul r x) (smul s x)))
(smul_mul : ∀ r s x, smul (mul r s) x = smul r (smul s x))
(one_smul : ∀ x, smul one x = x)

section fn_module

  variables {R S : Type} 
  variable  [ring R]

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

  definition fn_module [instance] : left_module R (S → R) :=
  ⦃
    left_module,
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
    smul_mul           := fn_smul_mul,
    one_smul           := fn_one_smul
  ⦄

end fn_module

section left_module
  variables {R M : Type}
  variable  [ringR : ring R]
  variable  [moduleRM : left_module R M]
  include   ringR moduleRM

  -- Note: the anonymous include does not work in the propositions below.

  proposition smul_left_distrib (a : R) (u v : M) : a • (u + v) = a • u + a • v :=
  !left_module.smul_left_distrib

  proposition smul_right_distrib (a b : R) (u : M) : (a + b)•u = a•u + b•u :=
  !left_module.smul_right_distrib

  proposition smul_mul (a : R) (b : R) (u : M) : (a * b) • u = a • (b • u) :=
  !left_module.smul_mul

  proposition unique_add_id {z : M} : (∀ a, z + a = a) → z = 0 := 
  assume h, calc
  z   = z + 0 : !add_zero
  ... = 0     : !h

  proposition unique_add_inv : ∀ v w : M, w + v = 0 → w = -v :=
  sorry

  proposition one_smul (u : M) : (1 : R) • u = u := !left_module.one_smul

  proposition zero_smul (u : M) : (0 : R) • u = 0 :=
  have (0 : R) • u + 0 • u = 0 • u + 0, by rewrite [-smul_right_distrib, *add_zero],
  !add.left_cancel this

  proposition smul_zero (a : R) : a • (0 : M) = 0 :=
  have a • 0 + a • 0 = a • 0 + 0, by rewrite [-smul_left_distrib, *add_zero],
  !add.left_cancel this

  proposition neg_smul (a : R) (u : M) : (-a) • u = - (a • u) :=
  eq_neg_of_add_eq_zero (by rewrite [-smul_right_distrib, add.left_inv, zero_smul])

  proposition neg_one_smul (u : M) : -(1 : R) • u = -u :=
  by rewrite [neg_smul, one_smul]

end left_module


structure is_linear_subspace' [class] (R : Type) {M : Type}
  [ringR : ring R] (U : set M) extends left_module R M :=
(has_zero : zero ∈ U)
(closed_add : ∀ u v, u ∈ U → v ∈ U → add u v ∈ U)
(closed_smul : ∀ (α : R) u, u ∈ U → smul α u ∈ U)

structure is_linear_subspace [class] (R : Type) {M : Type}
  [ringR : ring R] [moduleRM : left_module R M] (U : set M) : Type := 
(has_zero : 0 ∈ U)
(closed_add : ∀ u v, u ∈ U → v ∈ U → u + v ∈ U)
(closed_smul : ∀ α u, u ∈ U → left_module.smul ringR α u ∈ U)

definition is_linear_subspace_to_left_module {R M : Type} [ring R] [left_module R M] (U : set M) 
           [is_linear_subspace R U] : left_module R (subtype U) := sorry

section linear_subspace

  variable (R : Type)
  variable {M : Type}
  variable [ring R]
  variable [moduleRM : left_module R M]
  variable {n : ℕ}
  include moduleRM

  definition univ_is_subspace [instance] : is_linear_subspace R (@univ M) := sorry

  definition zero_is_subspace [instance] : is_linear_subspace R ('{(0:M)}) := sorry

  definition sum_of_subsets' [reducible] (U₁ U₂ : set M) := 
  { u | ∃ u₁ u₂, u₁ ∈ U₁ → u₂ ∈ U₂ → u = u₁ + u₂ }

  definition sum_of_subsets [reducible] (U : vector (set M) n) := 
  { v | ∃ u, (∀ k, u k ∈ U k) → v = ∑ m ← upto n, u m }

  theorem sum_is_smallest_subspace' (U₁ U₂ : set M)
          [subspaceU₁ : is_linear_subspace R U₁] [subspaceU₂ : is_linear_subspace R U₂] :
    ∀ (U : set M), is_linear_subspace R U → (sum_of_subsets' R U₁ U₂) ⊆ U :=
  sorry

  theorem sum_is_smallest_subspace (U : vector (set M) n) 
          [subspaceU : ∀ k, is_linear_subspace R (U k)] :
    ∀ (V : set M), is_linear_subspace R V → (sum_of_subsets R U) ⊆ V :=
  sorry

  definition is_direct_sum' (U₁ U₂ : set M) :=
  ∀ u, u ∈ (sum_of_subsets' R U₁ U₂) → ∃! u₁ u₂, u₁ ∈ U₁ → u₂ ∈ U₂ → u = u₁ + u₂

  definition is_direct_sum (U : vector (set M) n) :=
  ∀ v, v ∈ (sum_of_subsets R U) → ∃! u, (∀ k, u k ∈ U k) → v = ∑ m ← upto n, u m

  theorem direct_sum_condition (U : vector (set M) n) 
          [subspaceU : ∀ k, is_linear_subspace R (U k)] :
    is_direct_sum R U ↔ ∀ (u : vector M n), (∑ k ← upto n, u k) = 0 → ∀ k, u k = 0 :=
  sorry

  theorem direct_sum_of_subspaces {U W : set M} 
          [subspaceU : is_linear_subspace R U] [subspaceW : is_linear_subspace R W] :
    is_direct_sum' R U W ↔ U ∩ W = '{0} := 
  sorry

end linear_subspace


section linear_independence

  variable (R : Type) 
  variable {M : Type}
  variable [ringR : ring R]
  variable [moduleRM : left_module R M]
  variable {n : ℕ}
  include  ringR moduleRM
v
  open nat

  definition linear_combination (a : vector R n) (v : vector M n) :=
  ∑ k ← upto n, (a k)•(v k)

  definition span [reducible] (v : vector M n) : set M := { w | ∃ a, linear_combination R a v = w }

  theorem span_smallest (v : vector M n) {U : set M} [subspaceU : is_linear_subspace R U] :
    (∀ k, v k ∈ U) → span R v ⊆ U :=
  sorry

  definition spans (v : vector M n) := span R v = univ

  definition finite_dim := ∃ m (v : vector M m), spans R v

  definition infinite_dim := ∀ m (v : vector M m), ∃ u : M, u ∉ span R v

  definition linearly_independent (v : vector M n) := 
  ∀ a, linear_combination R a v = 0 → (∀ k, a k = 0)

  definition linearly_dependent (v : vector M n) :=
  ∃ a m, (a m) ≠ 0 ∧ linear_combination R a v = 0

  -- is this true?
  theorem dep_not_indep : ∀ (v : vector M n), linearly_independent R v ↔ ¬linearly_dependent R v :=
  sorry

--  lemma linear_dependence (v : vector M (n+1)) : ∃ j : fin n, (v j) ∈ span R v ∧ 

  theorem linIndSpan : ∀ {n1 n2 : ℕ} (v1 : vector M n1) (v2 : vector M n), 
    linearly_independent R v1 → spans R v2 → n1 ≤ n2 := 
  sorry

  structure basis [class] (v : vector M n) : Type := 
  (lind : linearly_independent R v)
  (sp : spans R v)

  definition basis_criterion (v : vector M n) : 
    basis R v ↔ ∀ u, ∃! a, u = linear_combination R a v :=
  sorry

--  theorem span_contains_basis (v : vector M n) : spans R v → ∃ s : set (fin n), basis R (λ k, 

--  theorem everyFdBasis : finite_dim R → ∃ v, basis R v := sorry

--  theorem lin_ind_extends_to_basis

--TODO - might be something wrong about this (regarding h1)...
  theorem subspace_direct_sum (h1 : ∃ v : vector M n, basis R v) (U : set M) [subspaceU : is_linear_subspace R U] : 
    ∃ W, (is_linear_subspace R W) → (is_direct_sum' R U W) → (univ = (sum_of_subsets' R U W)) :=
  sorry

  theorem basisLength : ∀ {n₁ n₂ : ℕ} (v₁ : vector M n₁) (v₂ : vector M n₂),
    basis R v₁ → basis R v₂ → n₁ = n₂ :=
  sorry

  definition dim := Σ m, ∃ (v : vector M m), basis R v

--  theorem subspace_dim

--  theorem lin_ind_right_length_is_basis

--  theorem dim_of_sum

end linear_independence


section polynomial

  open nat
  variable {R : Type}
  variable [ringR : ring R]
  include  ringR

  definition polynomial (p : R → R) (m : ℕ) := 
  ∃ (a : vector R m), ∀ z, p z = ∑ k ← upto m, (a k) * (z ^ k)

  definition polynomials : set (R → R) := { p | ∃ m, polynomial p m }

  --TODO: case with degree 0
  definition deg (p : R → R) := 
  Σ (d : ℕ), ∃ (a : vector R (d + 1)), (a (mk_mod d d)) ≠ 0 ∧ 
    ∀ z, p z = ∑ k ← upto (d + 1), (a k) * (z ^ k) 

  definition polynomials_deg (m : ℕ) : set (R → R) := { p | ∃ n, n ≤ m ∧ polynomial p n }

  definition poly_module_dim (m : ℕ) : left_module R (Σ p : R → R, polynomial p m) := sorry

--  theorem pmfd : ∀ m, finite_dim R (poly_module_dim m) := sorry

  definition poly_module : left_module R (Σ p : R → R, ∃ m, polynomial p m) := sorry

--  theorem infinite_dim

--probably only true for integral domains
  theorem poly_coef_zero {m : ℕ} (a : vector R m) : 
    (∀ z, ( ∑ k ← upto m, (a k) * (z ^ k) ) = 0) → ∀ k, (a k) = 0 :=
  sorry

  definition root (p : R → R) {m : ℕ} [poly : polynomial p m] (r : R) := p r = 0

end polynomial


section vector

  variables {R : Type} [ringR : ring R] {n : ℕ}
  include ringR

  definition δ (i j : fin n) : R := if i = j then 1 else 0

  definition vector_add (x y : vector R n) := λ k, (x k) + (y k)

  theorem vector_add_comm (x y : vector R n) : vector_add x y = vector_add y x := 
  sorry

  definition vector_zero := λ k : fin n, (0:R)

  definition vector_neg (x : vector R n) := λ k, -(x k)

  definition vector_smul (a : R) (x : vector R n) := λ k, a * (x k)

  definition moduleRn [instance] : left_module R (vector R n) := 
  ⦃
    left_module,
    smul               := vector_smul,
    add                := vector_add,
    add_assoc          := sorry,
    zero               := vector_zero,
    zero_add           := sorry,
    add_zero           := sorry,
    neg                := vector_neg,
    add_left_inv       := sorry,
    add_comm           := vector_add_comm,
    smul_left_distrib  := sorry,
    smul_right_distrib := sorry,
    smul_mul           := sorry,
    one_smul           := sorry
  ⦄

  theorem coord_subspaces : @univ (vector R n) = sum_of_subsets R (λ k, { p | ∃ x : R, p = (λ j, x * δ k j) }) :=
  sorry

  theorem coord_direct_sum : is_direct_sum R (λ k, { p : vector R n | ∃ x : R, p = (λ j, x * δ k j) }) :=
  sorry

--  theorem coord_span : spans R (λ j k : fin n, δ j k) := sorry

  definition dot_product (x y : vector R n) := ∑ k ← upto n, (x k) * (y k)

end vector



/- linear maps -/

structure is_linear_map [class] (R : Type) {M₁ M₂ : Type}
  [smul₁ : has_scalar R M₁] [smul₂ : has_scalar R M₂]
  [add₁ : has_add M₁] [add₂ : has_add M₂]
  (T : M₁ → M₂) :=
(additive : ∀ u v : M₁, T (u + v) = T u + T v)
(homogeneous : ∀ a : R, ∀ u : M₁, T (a • u) = a • T u)

proposition linear_map_additive (R : Type) {M₁ M₂ : Type}
    [smul₁ : has_scalar R M₁] [smul₂ : has_scalar R M₂]
    [add₁ : has_add M₁] [add₂ : has_add M₂]
    (T : M₁ → M₂) [linT : is_linear_map R T] (u v : M₁) :
  T (u + v) = T u + T v :=
is_linear_map.additive smul₁ smul₂ _ _ T u v

proposition linear_map_homogeneous {R M₁ M₂ : Type}
    [smul₁ : has_scalar R M₁] [smul₂ : has_scalar R M₂]
    [add₁ : has_add M₁] [add₂ : has_add M₂]
    (T : M₁ → M₂) [linT : is_linear_map R T] (a : R) (u : M₁) :
  T (a • u) = a • T u :=
is_linear_map.homogeneous smul₁ smul₂ _ _ T a u

proposition is_linear_map_id [instance] (R : Type) {M : Type}
    [smulRM : has_scalar R M] [has_addM : has_add M] :
  is_linear_map R (id : M → M) :=
is_linear_map.mk (take u v, rfl) (take a u, rfl)

section is_linear_map
  variables {R M₁ M₂ : Type}
  variable  [ringR : ring R]
  variable  [moduleRM₁ : left_module R M₁]
  variable  [moduleRM₂ : left_module R M₂]
  include   ringR moduleRM₁ moduleRM₂

  variable  T : M₁ → M₂
  variable  [is_linear_mapT : is_linear_map R T]
  include   is_linear_mapT

  proposition linear_map_zero : T 0 = 0 :=
  calc
    T 0 = T ((0 : R) • 0) : zero_smul
    ... = (0 : R) • T 0   : !linear_map_homogeneous
    ... = 0               : zero_smul

  proposition linear_map_neg (u : M₁) : T (-u) = -(T u) :=
  by rewrite [-neg_one_smul, linear_map_homogeneous T, neg_one_smul]

  proposition linear_map_smul_add_smul (a b : R) (u v : M₁) :
    T (a • u + b • v) = a • T u + b • T v :=
  by rewrite [linear_map_additive R T, *linear_map_homogeneous T]

  theorem lin_map_basis_of_domain {n : ℕ} (v : vector M₁ n) (w : vector M₂ n) 
          [b₁ : basis R v] [b₂ : basis R w] :
    ∃! T' : M₁ → M₂, ∀ j, T' (v j) = (w j) :=
  sorry

  definition linear_map_module : left_module R (Σ T' : M₁ → M₂, is_linear_map R T') := sorry

--TODO composition of linear maps

  definition null := { v | T v = 0 }

  theorem null_subspace : is_linear_subspace R (@null R _ _ _ _ _ T _) := 
  sorry

  theorem inj_equiv_zero_null : injective T ↔ (@null R _ _ _ _ _ T _ = '{0}) :=
  sorry

  definition range := { w | ∃ v, w = T v }

  theorem range_subspace : is_linear_subspace R (@range R _ _ _ _ _ T _) :=
  sorry

--  theorem fundamental_linear_map

/-  open matrix

  definition M {n₁ n₂ : ℕ} (T : M₁ → M₂) [lin : is_linear_map R T] 
    {v : vector M₁ n₁} {w : vector M₂ n₂} [vb : basis R v] [wb : basis R w] := 
  Σ A : matrix R n₁ n₂, ∀ k, T (v k) = linear_combination R (A k) w
-/
--  theorem matrix_sum_linear_map (S T : M₁ → M₂) : M (linear_map_module.add S T) = matrix_add (M S) (M T)

--  theorem matrix_smul_linear_map

--  theorem dim Rmn = m * n

--  theorem matrix_prod_linear_map

  definition invertible := 
  ∃ (S : M₂ → M₁) (linS : is_linear_map R S), (S ∘ T) = (λ x : M₁, x) ∧ (T ∘ S) = (λ x : M₂, x)

end is_linear_map

section eigen

  variables {R M : Type}
  variable  [ringR : ring R]
  variable  [moduleRM : left_module R M]
  include   ringR moduleRM

  variable  T : M → M
  variable  [is_linear_mapT : is_linear_map R T]
  include   is_linear_mapT

  definition invariant_subspace (U : set M) [subspaceU : is_linear_subspace R U] :=
  ∀ u, u ∈ U → T u ∈ U

  definition eigenvalue (t : R) := Σ v, v ≠ 0 → T v = t • v

end eigen

/- vector spaces -/

structure vector_space [class] (F V : Type) [fieldF : field F]
  extends left_module F V

/- an example -/

section
  variables (F V : Type)
  variables [field F] [vector_spaceFV : vector_space F V]
  variable  T : V → V
  variable  [is_linear_map F T]
  include   vector_spaceFV

  example (a b : F) (u v : V) : T (a • u + b • v) = a • T u + b • T v :=
  !linear_map_smul_add_smul
end

open real

structure binary_to_real [class] (V : Type) :=
(ip : V → V → ℝ)

structure real_inner_product_space [class] (V : Type)
          extends vector_space ℝ V, binary_to_real V :=
(positivity : ∀ v, ip v v ≥ 0)
(definiteness : ∀ v, ip v v = 0 ↔ v = zero)
(add_left : ∀ u v w, (ip (add u v) w) = (ip u w) + (ip v w))
(homog_left : ∀ (a : ℝ) (u v : V), (ip (smul a u) v) = a * (ip u v))
(symm : ∀ u v, ip u v = ip v u)


