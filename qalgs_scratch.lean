import data.real data.complex data.list data.nat algebra.module theories.analysis.normed_space
import data.fintype data.finset data.set algebra.group_bigops data.fin
open complex real list nat algebra prod function finset set fintype fin metric_space

structure star_ring [class] (R : Type) extends ring R :=
(star : R → R)
(star_add  : ∀ x y, star (mul x y) = add (star x) (star y))
(star_mul  : ∀ x y, star (mul x y) = mul (star y) (star x))
(star_one  : star one = one)
(star_invo : ∀ x, star (star x) = x)

structure comm_star_ring [class] (R : Type) 
          extends star_ring R, comm_ring R

definition real_to_comm_star_ring    [instance] : comm_star_ring ℝ := sorry
definition complex_to_comm_star_ring [instance] : comm_star_ring ℂ := sorry

structure star_algebra [class] (R A : Type) [comm_star_ring R] 
          extends star_ring A, has_scalar R A :=
(star_alg_invo : ∀ r x, star (smul r x) = smul (comm_star_ring.star r) (star x))

structure banach_algebra [class] (V : Type) extends 
          banach_space V, semigroup V :=
(norm_mul : ∀ x y : V, norm (mul x y) ≤ (norm x) * (norm y))

structure C_star_algebra [class] (V : Type) 
          extends banach_algebra V, star_algebra ℝ V := -- should be ℂ
(star_norm : ∀ x, norm (mul (star x) x) = (norm x) * (norm (star x)))

structure C_star_algebra' [class] (V : Type) extends banach_algebra V :=
(star : V → V)
(star_invo : ∀ x, star (star x) = x)
(star_add  : ∀ x y, star (add x y) = add (star x) (star y))
(star_mul  : ∀ x y, star (mul x y) = mul (star y) (star x))
(star_smul : ∀ s x, star (smul s x) = smul s (star x)) --should be conj s
(star_norm : ∀ x, norm (mul (star x) x) = (norm x) * (norm (star x)))

--theorem C_star_symm {V : Type} [C_star_algebra V] : 

structure complex_vector_space [class] (V : Type) extends vector_space ℂ V

/-structure complex_normed_vector_space [class] (V : Type) extends complex_vector_space V, has_norm V :=
(norm_zero : norm zero = 0)
(eq_zero_of_norm_eq_zero : ∀ u : V, norm u = 0 → u = zero)
(norm_triangle : ∀ u v, norm (add u v) ≤ norm u + norm v)
(norm_smul : ∀ (a : ℂ) (v : V), norm (smul a v) = abs a * norm v)-/

--structure complex_inner_product [class] (V : Type) :=

structure bilinear_form [class] (F V : Type) [field F] 
          extends vector_space F V :=
(bf : V → V → F)
(add_left    : ∀ u v w, (bf (add u v) w) = (bf u w) + (bf v w))
(add_right   : ∀ u v w, (bf w (add u v)) = (bf w u) + (bf w v))
(homog_left  : ∀ (a : F) (u v : V), (bf (smul a u) v) = a * (bf u v))
(homog_right : ∀ (a : F) (u v : V), (bf v (smul a u)) = a * (bf v u))

structure non_degenerate_bilinear_form [class] (F V : Type) [field F] 
          extends bilinear_form F V :=
(non_degenerate : ∀ x y, bf x y = 0 → x = zero)

structure symmetric_bilinear_form [class] (F V : Type) [field F] 
          extends bilinear_form F V :=
(symmetric : ∀ x y, bf x y = bf y x)

structure frobenius_algebra [class] (k A : Type) [field k]
          extends monoid A, non_degenerate_bilinear_form k A :=
(frobenius : ∀ a b c : A, bf (mul a b) c = bf a (mul b c))

structure symm_frobenius_algebra [class] (k A : Type) [field k]
          extends frobenius_algebra k A, symmetric_bilinear_form k A

-- equivalent to 1+1-dim topological quantum field theory
structure comm_frobenius_algebra [class] (k A : Type) [field k]
          extends comm_monoid A, frobenius_algebra k A

-- might refactor to use non-degenerate bilinear form
structure complex_inner_product_space [class] (V : Type)
          extends vector_space ℂ V :=
(ip : V → V → ℂ)
(positivity   : ∀ v, re (ip v v) ≥ 0)
(definiteness : ∀ v, ip v v = 0 ↔ v = zero)
(add_left     : ∀ u v w, (ip (add u v) w) = (ip u w) + (ip v w))
(homog_left   : ∀ (a : ℂ) (u v : V), (ip (smul a u) v) = a * (ip u v))
(conj_symm    : ∀ u v, ip u v = conj (ip v u))

notation ⟨v,w⟩ := complex_inner_product_space.ip v w

structure minkowski_inner_product_space [class] (V : Type)
          extends vector_space ℝ V :=
(ip : V → V → ℝ)
(non_degeneracy : ∀ u v, ip u v = 0 → u = zero)
(add_left       : ∀ u v w, (ip (add u v) w) = (ip u w) + (ip v w))
(homog_left     : ∀ (a : ℝ) (u v : V), (ip (smul a u) v) = a * (ip u v))
(symm           : ∀ u v, ip u v = ip v u)

--definition real_inner_product_space_to_complex_inner_product_space [reducible] [trans_instance] := sorry

section inner_product

  variables {V : Type} [complex_inner_product_space V]

  definition orthogonal (u v : V) := ⟨u,v⟩ = 0

  structure orthonormal [class] {n : ℕ} (v : vector V n) := 
  (orth : ∀ i j, ⟨v i, v j⟩ = δ i j)

  structure orthonormal_basis [class] {n : ℕ} (v : vector V n) 
                           extends orthonormal v --, basis v

end inner_product

definition Rsqrt_exists (y : ℝ) (Hy : y ≥ 0) : Σ (z : ℝ), (z * z = y ∧ z ≥ 0) := sorry
definition Rsqrt (y : ℝ) (Hy : y ≥ (0:ℝ)) : ℝ := 
  obtain z Hz, from (Rsqrt_exists y Hy), z
lemma Rsqrt_0 : Rsqrt 0 !le.refl = 0 := sorry

definition complex_inner_product_space_to_normed_vector_space [reducible] [trans_instance] 
           (V : Type) [ips : complex_inner_product_space V] : normed_vector_space V := sorry
/--⦃ normed_vector_space,
  norm := λ v : V, (Rsqrt (re (complex_inner_product.ip v v)) !complex_inner_product_space.positivity),
  norm_zero := sorry,
  eq_zero_of_norm_eq_zero := sorry,
  norm_triangle := sorry,
  norm_smul := sorry
⦄--/

structure complex_hilbert_space [class] (V : Type)
          extends ips : complex_inner_product_space V :=
(complete : ∀ X, @metric_space.cauchy V (@normed_vector_space_to_metric_space V 
                 (@complex_inner_product_space_to_normed_vector_space V ips)) X →
                 @metric_space.converges_seq V (@normed_vector_space_to_metric_space V 
                 (@complex_inner_product_space_to_normed_vector_space V ips)) X)

definition complex_hilbert_space_to_banach_space [reducible] [trans_instance] 
           (V : Type) [hs : complex_hilbert_space V] : banach_space V := sorry

--structure tensor [class] (A : Type) := 

definition tensor_spaces [class] (H K : Type) 
           [complex_hilbert_space H] [complex_hilbert_space K] : Type := sorry
infixl `⊗`:80 := tensor_spaces

definition tensor_product [instance] (H K : Type) 
           [complex_hilbert_space H] [complex_hilbert_space K] :
           complex_hilbert_space (H ⊗ K) := sorry

definition tensor_fn {H₁ H₂ K₁ K₂ : Type} 
           (f : H₁ → H₂)              (g : K₁ → K₂) 
           [complex_hilbert_space H₁] [complex_hilbert_space K₁]
           [complex_hilbert_space H₂] [complex_hilbert_space K₂] :
           H₁ ⊗ K₁ → H₂ ⊗ K₂ := sorry
infixl `⊗`:80 := tensor_fn

noncomputable definition tensor_linear [instance] {H₁ H₂ K₁ K₂ : Type} 
           [complex_hilbert_space H₁] [complex_hilbert_space K₁] 
           [complex_hilbert_space H₂] [complex_hilbert_space K₂]
           (f : H₁ → H₂)              (g : K₁ → K₂) 
           [is_linear_map ℂ f]        [is_linear_map ℂ g] :
           is_linear_map ℂ (f ⊗ g) := sorry

definition tensor_state {H K : Type} 
           [complex_hilbert_space H] [complex_hilbert_space K] : 
           H → K → H ⊗ K := sorry
infixl `⊗`:80 := tensor_state

definition group_commutator {G : Type} [group G] (a b : G) := a * b * a⁻¹ * b⁻¹
notation `⟦`a`,`b`⟧` := group_commutator a b

section

  variables {H K : Type}
  variables [complex_hilbert_space H] [complex_hilbert_space K]

  notation `∥`v`∥` := normed_vector_space.norm v
  notation `⟨`v`,`w`⟩` := complex_inner_product_space.ip v w

  noncomputable definition gram_schmidt_aux : list H → list H → list H
  | []        _  := []
  | (w :: ws) vs := let v' := (w - ∑ v ← vs, ⟨v, w⟩ • v) in 
                    ∥v'∥⁻¹ • v' :: (gram_schmidt_aux ws (∥v'∥⁻¹ • v' :: vs))

  noncomputable definition gram_schmidt (ws : list H) := gram_schmidt_aux ws []

--  variable (list_to_vec {A : Type} (l : list A) : vector A (length l))

--  theorem gram_schmidt_onb (ws : list H) : orthonormal_basis (list_to_vec (gram_schmidt ws)) := sorry

/-  structure is_bounded_linear [class] (A : H → K) extends is_linear_map ℂ A :=
  (bd : true)-/

  structure is_continuous_linear [class] (A : H → K) extends is_linear_map ℂ A :=
  (contin : continuous A)

  definition adjoint_exists (A : H → K) [is_continuous_linear A] : 
             Σ B : K → H, ∀ x y, ⟨A x, y⟩ = ⟨x, B y⟩ := sorry --follows from Riesz rep thm

  definition adjoint [class] (A : H → K) [is_continuous_linear A] : K → H := 
    obtain B h, from adjoint_exists A, B
  postfix `⁺`:2000 := adjoint

  definition adjoint_linear [instance] (A : H → K) [is_continuous_linear A] : 
             is_continuous_linear (adjoint A) := sorry

  variables (s : ℂ) (A B : H → K) 
  variables [iclA : is_continuous_linear A] [iclB : is_continuous_linear B]
  include iclA iclB

  theorem adjoint_involutive : A⁺⁺ = A                  := sorry
  theorem adjoint_add        : (A + B)⁺ = A⁺ + B⁺       := sorry
  theorem adjoint_smul       : (s • A)⁺ = (conj s) • A⁺ := sorry
  theorem adjoint_mul        : (A B)⁺ = B⁺ A⁺           := sorry

end

structure is_unitary [class] {H : Type} [complex_hilbert_space H] (U : H → H) 
          extends icl : is_continuous_linear U :=
(uni_right : U ∘ (@adjoint _ _ _ _ U icl) = id) 
(uni_left  : (@adjoint _ _ _ _ U icl) ∘ U = id)

definition tensor_unitary [instance] {H₁ H₂ : Type} 
           [complex_hilbert_space H₁] [complex_hilbert_space H₂] 
           (U₁ : H₁ → H₁)             (U₂ : H₂ → H₂) 
           [is_unitary U₁]            [is_unitary U₂] : 
           is_unitary (U₁ ⊗ U₂) := sorry

definition unitary_group (H : Type) [complex_hilbert_space H] : Type := 
Σ U : H → H, is_unitary U

structure is_hermitian [class] {H : Type} [complex_hilbert_space H] (A : H → H) 
          extends icl : is_continuous_linear A := 
(herm : A = (@adjoint _ _ _ _ A icl))

definition tensor_hermitian [instance] {H₁ H₂ : Type} 
           [complex_hilbert_space H₁] [complex_hilbert_space H₂] 
           (A₁ : H₁ → H₁)             (A₂ : H₂ → H₂) 
           [is_hermitian A₁]          [is_hermitian A₂] : 
           is_hermitian (A₁ ⊗ A₂) := sorry

section

  variables {H : Type} [complex_hilbert_space H]

  definition time_independent_schrodinger H₀ [is_hermitian H₀] := 
             ∃ (E : ℝ) (ψ : H), H₀ ψ = E • ψ

  definition tis_2 {K₁ K₂ : Type}
             [complex_hilbert_space K₁] [complex_hilbert_space K₂]
             (H₁ : K₁ → K₁)             (H₂ : K₂ → K₂) 
             [is_hermitian H₁]          [is_hermitian H₂] :
             time_independent_schrodinger (H₁ ⊗ H₂) := sorry

  definition unitary_is_ring [instance] : ring (unitary_group H) := sorry

  definition operator_space [reducible] [trans_instance] : banach_space (unitary_group H) := sorry

  definition spectral_norm (U : H → H) [is_linear_map ℂ U] : ℝ := sorry
--  notation `/`A`/` := spectral_norm
  
--  definition spectral_norm (U : unitary_group H) : ℝ := sorry
  notation `∥`A`∥` := spectral_norm

  definition is_universal_gate_set [class] (ugs : finset (unitary_group H)) :=
                           ∀ U, ∀ ε : ℝ, ε > 0 → ∃ C : list (unitary_group H), 
                           (∀ G, G ∈ C → G ∈ ugs) → ∥U - (∏ u ← C, u)∥ ≤ ε

  lemma subadditivity_of_errors {t : nat} (U V : fin t → unitary_group H) :
        ∀ ε, ε > 0 → (∀ i, ∥(U i) - (V i)∥ ≤ ε) → 
        ∥(∏ i ← upto t, U i) - (∏ i ← upto t, V i)∥ ≤ t * ε := sorry

end



structure group_representation [class] {G R V : Type} 
          [group G] [ring R] [left_module R V] 
          (Φ : G → V → V) :=
(linear : ∀ g, is_linear_map R (Φ g))
(id     : ∀ v, Φ 1 v = v)
(assoc  : ∀ g1 g2 v, Φ g1 (Φ g2 v) = Φ (g1 * g2) v)



example {A : Type} (P : A → Prop) (H : ∀ x, ¬ P x) : ¬ ∃ x, P x := 
not.intro (assume exP, obtain x₀ Px, from exP, absurd Px (H x₀))

example {A : Type} (P : A → Prop) (H : ¬ ∃ x, P x) (x₀ : A) : ¬ P x₀ :=
not.intro (assume Px, have (∃ x, P x), from exists.intro x₀ Px, H this)



section

  variables {G : Type} [group G]
  variables (X Y Z : G)

  definition I := group.one G

  variables (x2 : X ^ 2 = I) (y2 : Y ^ 2 = I) (z2 : Z ^ 2 = I)


end


section

  variables {H : Type} [complex_hilbert_space H]

--set_option trace.class_instances true

  theorem no_cloning U [is_unitary U] (Φ : H) : ¬ ∀ Ψ, U (Ψ ⊗ Φ) = Ψ ⊗ Ψ := sorry

end

