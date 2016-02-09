import data.real data.nat algebra.module
import theories.analysis.normed_space theories.analysis.ivt
open real nat algebra prod function analysis classical



--misc properties of square roots

attribute [simp] sqrt_spec abs_of_nonneg abs_of_neg

lemma sqrt_zero [simp] : sqrt (0:ℝ) = 0 := 
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero (sqrt_spec 0 (le_of_eq rfl))) id id

lemma eq_zero_of_sqrt_eq_zero (a : ℝ) (h₁ : a ≥ 0) (h₂ : sqrt a = 0) : a = 0 := 
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

variables {V : Type} [real_inner_product_space V] (a : ℝ) (u v w : V)

theorem positivity : ⟨v,v⟩ ≥ 0 := 
!real_inner_product_space.positivity

theorem ip_zero [simp] : ⟨(0:V),0⟩ = 0 :=
!real_inner_product_space.ip_zero

theorem eq_zero_of_ip_eq_zero [intro!] : ⟨v,v⟩ = 0 → v = 0 := 
!real_inner_product_space.eq_zero_of_ip_eq_zero

theorem add_left [simp] : (: ⟨u + v, w⟩ :) = ⟨u,w⟩ + ⟨v,w⟩ := 
!real_inner_product_space.add_left

theorem homog_left [simp] : ⟨a•u,v⟩ = a * ⟨u,v⟩ :=
!real_inner_product_space.homog_left

theorem symm [simp] : ⟨u,v⟩ = ⟨v,u⟩ :=
!real_inner_product_space.symm

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

lemma norm_triangle (u v : V) : ∥u + v∥ ≤ ∥u∥ + ∥v∥ := 
sorry --too complicated for now

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
                         (V : Type) [real_hilbert_space V] : banach_space V :=
⦃ banach_space,
  complete := real_hilbert_space.complete
⦄
