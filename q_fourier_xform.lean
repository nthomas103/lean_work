import standard data.matrix
open nat matrix matrix.ops real complex fin 
open sigma prod prod.ops sigma.ops list


definition mx [reducible] (d : ℕ × ℕ) := matrix ℂ d.1 d.2

constant tensor_product {da db} 
         (A : mx da) (B : mx db) : mx (da.1*db.1,da.2*db.2)
infixl `⊗`:100 := tensor_product

constant mx_one : mx (1,1)
definition Imx {n} : mx (n,n) := @I ℂ _ n

definition mx_to_sigma [coercion] [reducible]
           {d} (M : mx d) : sigma mx := ⟨_,M⟩

definition tensor_bigop_aux (l : list (sigma mx)) := 
list.foldl 
(λ M N, ⟨_, M.2 ⊗ N.2⟩) ⟨_, mx_one⟩ l

definition tensor_bigop (l : list (sigma mx)) := (tensor_bigop_aux l).2
prefix `⊗` := tensor_bigop

constant (M₁ : mx (2,2))
constant (M₂ : mx (4,4))
eval (mx_to_sigma (matrix.mul (⊗ [M₂, M₁, M₂]) Imx)).1.1

definition conj_transpose {n} (M : mx (n,n)) : mx (n,n) :=
λ i j, conj (M[j, i])
postfix `†`:2000 := conj_transpose

structure is_unitary [class] {n} (U : mx (n,n)) := 
(uni_right : U * U† = I) 
(uni_left  : U† * U = I)

noncomputable definition mul_unitary {n} (U₁ U₂ : mx (n,n)) 
           [is_unitary U₁] [is_unitary U₂] : is_unitary (U₁ * U₂) := sorry

definition stack_unitary {m n} 
           (U₁ : mx (m,m)) (U₂ : mx (n,n))
           [is_unitary U₁] [is_unitary U₂] : is_unitary (U₁ ⊗ U₂) := sorry

definition gate := Σ (U : mx (2,2)), is_unitary U

definition qcirc (n) := Σ (U : mx (2^n,2^n)), is_unitary U

noncomputable definition qcirc_comp 
  {n} (q₁ : qcirc n) (q₂ : qcirc n) : qcirc n := 
⟨matrix.mul q₂.1 q₁.1, @mul_unitary _ q₂.1 q₁.1 q₂.2 q₁.2⟩
infixl `**`:97 := qcirc_comp

definition qcirc_stack
  {m n} (q₁ : qcirc m) (q₂ : qcirc n) : qcirc (m + n) :=
sorry--⟨q₁.1 ⊗ q₂.1, @stack_unitary _ _ q₁.1 q₂.1 q₁.2 q₂.2⟩
infixl `⊗`:100 := qcirc_stack

lemma I_unitary {n} : @is_unitary n Imx := sorry

noncomputable definition Ic {n} : qcirc n := ⟨Imx, I_unitary⟩

lemma slide {m n} (q₁ : qcirc m) (q₂ : qcirc n) :
      (q₁ ⊗ Ic) ** (Ic ⊗ q₂) = 
      (Ic ⊗ q₂) ** (q₁ ⊗ Ic) := sorry

constant π : ℝ
constant H     : gate
constant R     : ℝ → gate
--constant swap  : mx (4,4)
constant gate_circ {n} (g : fin n) (U : gate) : qcirc n
constant cgate {n} (c g : fin n) (U : gate) : qcirc n

constant cast_qcirc {m n} (q : qcirc m) (h : m = n) : qcirc n

noncomputable definition qft_helper : ∀ n, qcirc (n+1)
| 0     := gate_circ (fin.mk 0 sorry) H
| (m+1) := (cgate (fin.mk 0 sorry) (fin.mk (m+1) sorry) (R (π / 2^(m+1))))
           ** ((qft_helper m) ⊗ Ic)

noncomputable definition qft : ∀ n, qcirc (n+1)
| 0     := qft_helper 0
| (m+1) := cast_qcirc ((cast_qcirc ((@Ic 1) ⊗ (qft m)) (by inst_simp)) ** 
                                   (qft_helper (m+1))) (by inst_simp)












--some other matrix stuff

definition matrix_inv [instance] {T : Type} [comm_ring T] {n} : 
         has_inv (matrix T n n) := sorry
         
constant det {T : Type} [comm_ring T] {m} (A : matrix T m m) : T
notation `|`A`|` := det A

noncomputable definition kron_sum {m n} 
        (A : mx (n,n)) (B : mx (m,m)) : mx ((n*m),(n*m)) :=
        A ⊗ I + I ⊗ B
infixl `⊕`:100 := kron_sum

section

variables {T : Type} [comm_ring T]
variables {m n p q r s: ℕ}

lemma t_left_distrib (A B : mx (m,n)) (C : mx (p,q)) :
      (A + B) ⊗ C = A ⊗ C + B ⊗ C := sorry

lemma t_right_distrib (A : matrix T m n) (B C : matrix T p q) :
      A ⊗ (B + C) = A ⊗ B + A ⊗ C := sorry

lemma t_left_smul (k : T) (A : matrix T m n) (B : matrix T p q) :
      (k ⬝A) ⊗ B = k ⬝(A ⊗ B) := sorry

lemma t_right_smul (k : T) (A : matrix T m n) (B : matrix T p q) :
      A ⊗ (k ⬝B) = k ⬝(A ⊗ B) := sorry

lemma t_assoc (A : matrix T m n) (B : matrix T p q) (C : matrix T r s) :
      (A ⊗ B) ⊗ C == A ⊗ (B ⊗ C) := sorry

lemma t_mul (A : matrix T m n) (B : matrix T q r) 
            (C : matrix T n p) (D : matrix T r s) :
      matrix.mul (A ⊗ B) (C ⊗ D) = (matrix.mul A C) ⊗ (matrix.mul B D) := 
sorry

lemma t_inverse (A : matrix T m m) (B : matrix T n n) :
      (A ⊗ B)⁻¹ = A⁻¹ ⊗ B⁻¹ := sorry

postfix `ᵀ`:1500 := transpose

lemma t_trans (A : matrix T m n) (B : matrix T p q) :
      (A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ := sorry

lemma t_det (A : matrix T m m) (B : matrix T n n) :
      |A ⊗ B| = |A|^n * |B|^m := sorry



end

