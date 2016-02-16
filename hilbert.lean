import standard algebra.module theories.topology.basic 
import theories.analysis.normed_space theories.analysis.ivt
import theories.analysis.metric_space
open real nat algebra prod function analysis classical
open fin set topology

definition vector [reducible] (T : Type) (n : ℕ) := fin n → T

definition δ {n} : fin n → fin n → ℝ :=
λ i j, if i = j then 1 else 0

/-attribute [simp] smul_left_distrib smul_right_distrib mul_smul one_smul
attribute [simp] zero_smul smul_zero neg_smul neg_one_smul smul_neg
attribute [simp] smul_sub_left_distrib sub_smul_right_distrib
-/

--function space is module

section fn_module

  variables {R S : Type} 
  variable  [comm_ring R]

  definition fn_add (f g : S → R) (x : S) := f x + g x

  definition fn_smul (a : R) (f : S → R) (x : S) := a * f x

  definition fn_zero (x : S) : R := 0

  definition fn_neg (f : S → R) (x : S) := - f x

  attribute [reducible] fn_add fn_smul fn_zero fn_neg

  proposition fn_add_assoc (f g h : S → R) : 
    (fn_add (fn_add f g) h) = (fn_add f (fn_add g h)) :=
  by blast

  proposition fn_zero_add (f : S → R) :
    fn_add fn_zero f = f :=
  by blast

  proposition fn_add_zero (f : S → R) :
    fn_add f fn_zero = f := 
  by blast

  proposition fn_add_left_inv (f : S → R) :
    fn_add (fn_neg f) f = fn_zero := 
  by blast

  proposition fn_add_comm (f g : S → R) :
    fn_add f g = fn_add g f :=
  by blast

--  attribute [simp] fn_add_assoc fn_zero_add fn_add_zero fn_add_left_inv
  --attribute [simp] fn_add_comm

  proposition fn_smul_left_distrib : ∀ (a : R) (f g : S → R), 
    fn_smul a (fn_add f g) = (fn_add (fn_smul a f) (fn_smul a g)) := 
  λ a f g, funext (λ x, !left_distrib)

  proposition fn_smul_right_distrib : ∀ (a b : R) (f : S → R),
    fn_smul (a + b) f = fn_add (fn_smul a f) (fn_smul b f) :=
  λ a f g, funext (λ x, !right_distrib)

  proposition fn_mul_smul : ∀ (a b : R) (f : S → R),
    fn_smul (a * b) f = fn_smul a (fn_smul b f) := 
  by blast

  proposition fn_one_smul : ∀ (f : S → R), fn_smul 1 f = f :=
  by blast

  definition fn_module [instance] : left_module R (S → R) :=
  ⦃
    left_module,
    smul               := fn_smul,
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
    mul_smul           := fn_mul_smul,
    one_smul           := fn_one_smul
  ⦄

  definition fn_mul (f g : S → R) (x : S) := (f x) * (g x)

  definition fn_one (x : S) : R := 1

--  definition fn_inv

  attribute [reducible] fn_mul fn_one

  proposition fn_mul_assoc (f g h : S → R) :
    (fn_mul (fn_mul f g) h) = (fn_mul f (fn_mul g h)) :=
  by blast

  proposition fn_one_mul (f : S → R) :
    (fn_mul fn_one f) = f :=
  by blast

  proposition fn_mul_one (f : S → R) :
    (fn_mul f fn_one) = f :=
  by blast

  proposition fn_mul_comm (f g : S → R) :
    (fn_mul f g) = (fn_mul g f) :=
  by blast

--  attribute [simp] fn_mul_assoc fn_one_mul fn_mul_one fn_mul_comm
  
  definition fn_comm_monoid [instance] : comm_monoid (S → R) :=
  ⦃ comm_monoid,
    mul       := fn_mul,
    one       := fn_one,
    mul_assoc := fn_mul_assoc,
    one_mul   := fn_one_mul,
    mul_one   := fn_mul_one,
    mul_comm  := fn_mul_comm
  ⦄

end fn_module

section vs

  variables {R M : Type} {ringR : ring R} {moduleRM : left_module R M}
  include ringR moduleRM

  lemma unique_additive_identity (z : M) 
        (h₁ : ∀ x, x + z = x) (h₂ : ∀ x, z + x = x) :
        z = 0 :=
  sorry

--  lemma unique_additive_inverse

end vs

definition is_subspace [class] (R : Type) [ring R]
           {V : Type} [left_module R V] 
           (U : set V) := left_module R (subtype U)

structure subspace [class] (R : Type) [ring R] 
          {V : Type} [left_module R V]
          (U : set V) :=
(zero_in : 0 ∈ U)
(add_in  : ∀ u w, u ∈ U → w ∈ U → u + w ∈ U)
(smul_in : ∀ (a : R) u, u ∈ U → a • u ∈ U)

definition subs [instance] {R : Type} [ring R] {V : Type} [left_module R V] 
           (U : set V) [subspace R U] : is_subspace R U :=
sorry

definition sum_of_subspaces (R : Type) [ring R] {V : Type} [left_module R V]
           (U₁ U₂ : set V) [is_subspace R U₁] [is_subspace R U₂] :=
{ u | ∃ u₁ u₂, u₁ ∈ U₁ ∧ u₂ ∈ U₂ ∧ u = u₁ + u₂}


definition sum_of_subspaces_bigop 
           (R : Type) [ring R] {V : Type} [left_module R V]
           {n} (U : vector (set V) n) {h : ∀ i, is_subspace R (U i)} :=
{ u₀ | ∃ u, (∀ i, (u i) ∈ (U i)) ∧ u₀ = ∑ i ← upto n, (u i)}

definition sum_of_subspaces_is_subspace [instance]
           (R : Type) [ring R] {V : Type} [left_module R V]
           (U₁ U₂ : set V) [is_subspace R U₁] [is_subspace R U₂] :
           is_subspace R (sum_of_subspaces R U₁ U₂) := sorry

theorem sum_of_subspaces_is_smallest 
        (R : Type) [ring R] {V : Type} [left_module R V]
        (U₁ U₂ : set V) [is_subspace R U₁] [is_subspace R U₂]
        (U : set V) (h : is_subspace R U) : 
        (sum_of_subspaces R U₁ U₂) ⊆ U := sorry

definition is_direct_sum (R : Type) [ring R] {V : Type} [left_module R V]
           (U₁ U₂ : set V) [is_subspace R U₁] [is_subspace R U₂] :=
∀ w, w ∈ (sum_of_subspaces R U₁ U₂) → 
     ∃! u₁ u₂, u₁ ∈ U₁ → u₂ ∈ U₂ → w = u₁ + u₂

theorem direct_sum_condition 
        (R : Type) [ring R] {V : Type} [left_module R V]
        (U₁ U₂ : set V) [is_subspace R U₁] [is_subspace R U₂] :
(is_direct_sum R U₁ U₂) ↔ 
(∀ u₁ u₂, u₁ ∈ U₁ → u₂ ∈ U₂ → u₁ + u₂ = 0 → u₁ = 0 ∧ u₂ = 0) := sorry

theorem direct_sum_intersection
        (R : Type) [ring R] {V : Type} [left_module R V]
        (U₁ U₂ : set V) [is_subspace R U₁] [is_subspace R U₂] :
(is_direct_sum R U₁ U₂) ↔ U₁ ∩ U₂ = '{0} := sorry


--finite dimensional vector spaces

definition linear_combination [reducible]
           {R V : Type} [ring R] [left_module R V]
           {n} (a : vector R n) (v : vector V n) :=
∑ i ← upto n, (a i)•(v i)

definition span [reducible]
           (R : Type) [ring R] {V : Type} [left_module R V]
           {n} (v : vector V n) :=
{ w | ∃ a : vector R n, w = linear_combination a v}
--what about span of 0-dim vector?  can we prove that it is '{0}?

definition span_is_subspace [instance]
           (R : Type) [ring R] {V : Type} [left_module R V]
           {n} (v : vector V n) : is_subspace R (span R v) :=
sorry

theorem span_is_smallest_subspace
        (R : Type) [ring R] {V : Type} [left_module R V] 
        {n} (v : vector V n)
        (U : set V) [is_subspace R U] (h : ∀ i, v i ∈ U) :
        (span R v) ⊆ U := sorry

definition spans 
          (R : Type) [ring R] {V : Type} [left_module R V] 
          {n} (v : vector V n) (U : set V) :=
span R v = U

definition is_finite_dim_vs [class]
          (R : Type) [ring R] (V : Type) [left_module R V] : Prop :=
∃ (n : ℕ) (v : vector V n), spans R v univ

definition linearly_independent [reducible]
          (R : Type) [ring R] {V : Type} [left_module R V] 
          {n} (v : vector V n) :=
∀ a : vector R n, linear_combination a v = 0 → a = (λ i, 0)

definition linearly_dependent [reducible]
          (R : Type) [ring R] {V : Type} [left_module R V] 
          {n} (v : vector V n) :=
∃ a : vector R n, linear_combination a v = 0
--do we have ∀ v, linearly_independent R v ↔ ¬ linearly_dependent R v ?



definition is_basis
          (R : Type) [ring R] {V : Type} [left_module R V] 
          {n} (v : vector V n) :=
linearly_independent R v ∧ spans R v univ

theorem basis_criterion
          (R : Type) [ring R] {V : Type} [left_module R V] 
          {n} (v : vector V n) :
        is_basis R v ↔ ∀ u, ∃! a : vector R n, u = linear_combination a v :=
sorry


theorem fdvs_basis
        (R : Type) [ring R] {V : Type} [left_module R V] 
        (fdvs : is_finite_dim_vs R V) :
∃ (n : ℕ) (v : vector V n), is_basis R v :=
sorry


definition eigenvalue 
           (R : Type) [ring R] {V : Type} [left_module R V] 
           (T : V → V) [is_linear_map R T] (a : R) :=
∃ v, v ≠ 0 ∧ T v = a • v




--misc properties of square roots

attribute [simp] sqrt_spec abs_of_nonneg abs_of_neg

lemma sqrt_zero [simp] : sqrt (0:ℝ) = 0 := 
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero (sqrt_spec 0 (le_of_eq rfl))) 
id id

lemma eq_zero_of_sqrt_eq_zero (a : ℝ) (h₁ : a ≥ 0) (h₂ : sqrt a = 0) : 
      a = 0 := 
calc a = sqrt a * sqrt a : sqrt_spec a h₁
   ... = 0               : by simp

lemma mul_sqrt_eq_sqrt_mul [simp] (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : 
      sqrt (a * b) = (sqrt a) * (sqrt b) := sorry

lemma sqrt_sqr [simp] (a : ℝ) : sqrt (a * a) = abs a := 
dite (a ≥ 0) 
(λ h, by inst_simp)
(λ nh, 
assert (a < 0), from lt_of_not_ge nh,
assert (-a ≥ 0), from neg_nonneg_of_nonpos (le_of_lt this),
calc sqrt (a * a) = sqrt (-a * -a) : by inst_simp
          ...     = abs a          : by inst_simp)






--attribute [simp] linear_map_zero linear_map_additive 
--attribute [simp] linear_map_homogeneous

--definition of real inner product spaces

structure real_inner_product_space [class] (V : Type)
          extends real_vector_space V :=
(ip : V → V → ℝ)
(positivity            : ∀ v, ip v v ≥ 0)
(ip_zero               : ip zero zero = 0)
(eq_zero_of_ip_eq_zero : ∀ v, ip v v = 0 → v = zero)
(add_left              : ∀ u v w, (ip (add u v) w) = (ip u w) + (ip v w))
(homog_left            : ∀ (a : ℝ) u v, ip (smul a u) v = a * (ip u v))
(symm                  : ∀ u v, ip u v = ip v u)

notation ⟨v,w⟩ := real_inner_product_space.ip v w

section rips

  variables {V : Type} [real_inner_product_space V]

  variables (u v w : V) (a : ℝ)

  lemma positivity [intro!] : ⟨v,v⟩ ≥ 0 := 
        !real_inner_product_space.positivity

  lemma eq_zero_of_ip_eq_zero [intro!] : ⟨v,v⟩ = 0 → v = 0 := 
        !real_inner_product_space.eq_zero_of_ip_eq_zero

  lemma ip_zero : ⟨(0:V),0⟩ = 0 := 
        !real_inner_product_space.ip_zero

  lemma add_left : ⟨u+v,w⟩ = ⟨u,w⟩ + ⟨v,w⟩ := 
        !real_inner_product_space.add_left

  lemma homog_left : ⟨a•u,v⟩ = a*⟨u,v⟩ :=
        !real_inner_product_space.homog_left

  lemma symm : ⟨u,v⟩ = ⟨v,u⟩ :=
        !real_inner_product_space.symm

  attribute [simp] ip_zero add_left homog_left symm

  theorem add_right : ⟨u,v+w⟩ = ⟨u,v⟩ + ⟨u,w⟩ := by inst_simp

  theorem homog_right : ⟨u,a•v⟩ = a*⟨u,v⟩ := by inst_simp

  noncomputable definition ip_linear [instance] : 
    is_linear_map ℝ (λ v₀, ⟨v₀,u⟩) := sorry

  theorem zero_left  [simp] : ⟨0,u⟩ = 0 := 
  sorry--linear_map_zero (λ v₀, ⟨v₀,u⟩)

  theorem zero_right [simp] : ⟨u,0⟩ = 0 := by inst_simp

  definition orthogonal [reducible] := ⟨u,v⟩ = 0

  theorem orth_0 : orthogonal 0 u := by inst_simp

  theorem orth_self : orthogonal u u → u = 0 := by grind

  definition is_orthonormal [reducible] {n} (e : vector V n) :=
  ∀ i j, ⟨e i, e j⟩ = δ i j
  
  theorem lin_ind_of_on {n} (e : vector V n) [is_orthonormal e] :
  linearly_independent ℝ e := sorry

  noncomputable definition is_onb [reducible] [class] 
                           {n} (e : vector V n) :=
  is_basis ℝ e ∧ is_orthonormal e
  
  theorem lin_comb_of_onb1 {n} (e : vector V n) [is_onb e] 
          (v : V) : 
  v = ∑ i ← upto n, ⟨v,(e i)⟩•(e i) := sorry




end rips



section sqrt_norm

variables {V : Type} [real_inner_product_space V]

--define Hilbert space norm

noncomputable definition sqrt_norm [instance] : has_norm V :=
⦃ has_norm,
  norm := λ v : V, sqrt ⟨v,v⟩
⦄
attribute [reducible] has_norm.norm


--prove properties of Hilbert space norm

lemma norm_zero : ∥(0:V)∥ = 0 := calc 
  sqrt ⟨0,0⟩ = sqrt 0 : {ip_zero}
       ...   = 0      : by simp

lemma eq_zero_of_norm_eq_zero (u : V) (h : ∥u∥ = 0) : u = 0 := 
eq_zero_of_ip_eq_zero u (eq_zero_of_sqrt_eq_zero ⟨u,u⟩ !positivity h)

lemma norm_smul (a : ℝ) (v : V) : ∥a•v∥ = abs a * ∥v∥ := calc
∥a•v∥ = sqrt (a * ⟨v,a•v⟩)   : {!homog_left}
  ... = sqrt (a * a * ⟨v,v⟩) : by inst_simp
  ... = sqrt (a * a) * ∥v∥  : !mul_sqrt_eq_sqrt_mul !mul_self_nonneg !positivity
  ... = abs a * ∥v∥          : by inst_simp

attribute [simp] norm_zero norm_smul pow_two

theorem pythagorean [simp] (u v : V) (h : orthogonal u v) : 
        ∥u + v∥^2 = ∥u∥^2 + ∥v∥^2 := calc
∥u + v∥^2 = ⟨u+v,u+v⟩     : sorry --shouldn't this work?
  ...     = ⟨u,u⟩ + ⟨v,v⟩ : by inst_simp
  ...     = ∥u∥^2 + ∥v∥^2 : sorry

--theorem orth_decomp (u v : V) {h : v ≠ 0} :

theorem cauchy_schwarz (u v : V) : abs ⟨u,v⟩ = ∥u∥*∥v∥ := sorry

lemma norm_triangle (u v : V) : ∥u + v∥ ≤ ∥u∥ + ∥v∥ := 
sorry --too complicated for now, need cauchy-schwarz

theorem parallelogram_eq (u v : V) : 
        ∥u+v∥^2 + ∥u-v∥^2 = 2*(∥u∥^2+∥v∥^2) := sorry

theorem norm_of_on_lin_comb {n} (a : vector ℝ n) 
        (e : vector V n) [is_orthonormal e] :
∥linear_combination a e∥^2 = ∑ i ← upto n, (a i)^2 := sorry

theorem lin_comb_of_onb2 {n} (e : vector V n) [is_onb e] 
        (v : V) : 
∥v∥^2 = ∑ i ← upto n, ⟨v,(e i)⟩^2 := sorry


end sqrt_norm



noncomputable definition real_inner_product_space_to_normed_vector_space 
           [reducible] [trans_instance] (V : Type) 
           [ips : real_inner_product_space V] : normed_vector_space V :=
⦃ normed_vector_space,
  norm_zero               := norm_zero,
  eq_zero_of_norm_eq_zero := eq_zero_of_norm_eq_zero,
  norm_triangle           := norm_triangle,
  norm_smul               := norm_smul,

  add_assoc          := real_inner_product_space.add_assoc,
  zero_add           := real_inner_product_space.zero_add,
  add_zero           := real_inner_product_space.add_zero,
  add_left_inv       := real_inner_product_space.add_left_inv,
  add_comm           := real_inner_product_space.add_comm,
  smul_left_distrib  := real_inner_product_space.smul_left_distrib,
  smul_right_distrib := real_inner_product_space.smul_right_distrib,
  mul_smul           := real_inner_product_space.mul_smul,
  one_smul           := real_inner_product_space.one_smul
⦄


structure real_hilbert_space [class] (V : Type)
          extends ips : real_inner_product_space V :=
(complete : ∀ X, @cauchy V (@normed_vector_space_to_metric_space V 
          (@real_inner_product_space_to_normed_vector_space V ips)) X →
          @converges_seq V (@normed_vector_space_to_metric_space V 
          (@real_inner_product_space_to_normed_vector_space V ips)) X)


noncomputable definition real_hilbert_space_to_banach_space 
                         [reducible] [trans_instance] 
                         (V : Type) [real_hilbert_space V] : 
                         banach_space V :=
⦃ banach_space,
  complete := real_hilbert_space.complete
⦄


-- euclidean spaces

definition R [reducible] (n : ℕ) := vector ℝ n

protected lemma ext {n} {x y : R n}
                (h : ∀ i , x i = y i) : x = y :=
funext (λ i, h i)


noncomputable definition euclidean_space [instance] {n : ℕ} :
           real_hilbert_space (R n) :=
⦃ real_hilbert_space,
  add                   := λ x y i, (x i) + (y i),
  add_assoc             := λ x y z, ext (λ i, !add.assoc),
  zero                  := λ i, 0,
  zero_add              := λ x, ext (λ i, !zero_add),
  add_zero              := λ x, ext (λ i, !add_zero),
  neg                   := λ x i, -(x i),
  add_left_inv          := λ x, ext (λ i, !add.left_inv),
  add_comm              := λ x y, ext (λ i, !add.comm),
  smul                  := λ a x i, a * (x i),
  smul_left_distrib     := λ r x y, ext (λ i, !smul_left_distrib),
  smul_right_distrib    := λ r s x, ext (λ i, !smul_right_distrib),
  mul_smul              := λ r s x, ext (λ i, !mul_smul),
  one_smul              := λ x, ext (λ i, !one_smul),
  ip                    := λ x y, ∑ i ← upto n, ((x i) * (y i)),
  positivity            := sorry,
  ip_zero               := !Suml_zero,
  eq_zero_of_ip_eq_zero := sorry,
  add_left              := sorry,
  homog_left            := sorry,
  symm                  := sorry,
  complete              := sorry
⦄


structure neighborhood [class] {X} [topology X] (p : X) (V : set X) :=
(U : set X)
(U_open : Open U)
(p_in_U : p ∈ U)
(U_in_V : U ⊆ V)

structure homeomorphism [class] {M N : Type} [topology M] [topology N] 
          (f : M → N) :=
(bij     : bijective f)
(contin  : continuous f)
(f_inv : N → M)
(inv        : left_inverse f_inv f)
(inv_contin : continuous f_inv)

definition homeomorphic (M N : Type) [topology M] [topology N] :=
Σ (f : M → N), homeomorphism f

structure locally_euclidean [class] (X : Type) extends T : topology X :=
(dim : ℕ)
(homeo : ∀ p : X, Σ (V : set X) (nbhd : @neighborhood _ T p V), 
         @homeomorphic X (R dim) T _)

structure manifold [class] (X : Type) 
          extends locally_euclidean X, T2_space X

structure atlas [class] (X : Type) [M : manifold X] :=
(I : Type)
(U : I → set X)
(chart : Π (α : I) x, x ∈ U α → R (manifold.dim X))
--(homeo : Π (α : I), homeomorphism (chart α))
(covers : (⋃ (α : I), U α) = univ)

/-definition transition_map {X : Type} [manifold X] [A : atlas X] 
           (α β : atlas.I) (x : X) (xmem : x ∈ atlas.U α ∩ atlas.U β) :=
(atlas.chart β (atlas.chart α x sorry)⁻¹ sorry)-/




definition Rn_T2 [instance] {n : ℕ} : T2_space (R n) := sorry

theorem id_contin {X : Type} [T : topology X] : continuous (@id X) :=
assume (x : X) (U : set X) (fxU : id x ∈ U) (U_open : Open U),
  exists.intro U (and.intro fxU (and.intro U_open sorry))

noncomputable definition Rn_homeo_Rn (n : ℕ) : homeomorphic (R n) (R n) := 
sigma.mk id 
  (homeomorphism.mk bijective_id id_contin id (λ x, !left_id) id_contin)

definition Rn_manifold [instance] {n : ℕ} : manifold (R n) := 
sorry





definition e_basis {n} (i : fin n) : R n := λ j, δ i j

noncomputable definition differentiable [class] {n m : ℕ} 
                         (f : R n → R m) (a : R n) :=
∃ (Df : R n → R m) (ilm : is_linear_map ℝ Df), 
(λ h, ∥f (a + h) - f a - Df h∥ / ∥h∥) ⟶  0 at 0

definition D {n m : ℕ} (f : R n → R m) (a : R n) : R m := sorry

theorem chain_rule [instance] {n m p : ℕ} (a : R n)
        (f : R n → R m) [differentiable f a]
        (g : R m → R p) [differentiable g (f a)] :
        differentiable (g ∘ f) a := sorry

theorem d_const {n m : ℕ} {y : R m} : ∀ a, D (λ x : R n, y) a = (λ i, 0) :=
sorry

theorem d_linear {n m : ℕ} (f : R n → R m) [is_linear_map ℝ f] :
        ∀ a, D f a = f a := 
sorry

definition R_to_R1 [coercion] (x : ℝ) : R 1 := sorry
definition R1_to_R (x : R 1) : ℝ := sorry

definition d_component1 [instance] {n m : ℕ} (f : R n → R m) (a : R n) 
        [differentiable f a] (i : fin m) : differentiable (λ x, f x i) a := 
sorry

definition d_component2 [instance] {n m : ℕ} (f : vector (R n → ℝ) m)
           (a : R n) (i : fin m) [differentiable (f i) a] :
           differentiable (λ x j, f j x) a := 
sorry

definition d_component3 {n m : ℕ} (f : R n → R m) (a : R n)
           [differentiable f a] :
           D f a = (λ i, R1_to_R (D (λ x, f x i) a)) := 
--         D f a ==(λ i,         D (λ x, f x i) a) := 
sorry

definition d_add' : 
  D (λ x : R 2, ∑ i ← upto 2, x i) = (λ x : R 2, ∑ i ← upto 2, x i) := 
sorry

/-definition d_mul' (a : R 2) :
  D (λ x : R 2, ∏ i ← upto 2, x i) a == 
  (λ x : R 2, (a (fin.mk 1 (by blast))) * (x (fin.mk 0 (by blast))) + (a (fin.mk 0 (by blast))) * (x (fin.mk 1 (by blast)))) a :=
sorry-/

definition d_add_diff [instance] {n : ℕ} (f g : R n → ℝ) (a : R n)
           [differentiable f a] [differentiable g a] :
           differentiable (f + g) a :=
sorry

definition d_add_mul [instance] {n : ℕ} (f g : R n → ℝ) (a : R n)
           [differentiable f a] [differentiable g a] :
           differentiable (f * g) a :=
sorry


definition d_add {n : ℕ} (f g : R n → ℝ) (a : R n)
           [differentiable f a] [differentiable g a] :
           D (f + g) a = D f a + D g a :=
sorry

definition d_mul {n : ℕ} (f g : R n → ℝ) (a : R n)
           [differentiable f a] [differentiable g a] :
           D (f * g) a = (g a) * D f a + (f a) * D g a :=
sorry

--definition d_div {n : ℕ} (f g : R n → ℝ) (a : R n)

attribute [simp] d_add d_mul




/-definition differentiable' {M : Type} [manifold M]
           (f : M → ℝ) (p : M) := sorry-/
/-∀ (α : atlas.I M) (memp : p ∈ (atlas.U α)), 
differentiable (f ∘ (λ p' memp', atlas.chart α p')) (λ p, memp)-/
