import standard algebra.module
open algebra set prod prod.ops fin nat function

-- SDG

-- 1.1.1

variables {R : Type} [field R]

definition D := { d : R | d ^ 2 = 0 }

lemma zero_in_D : (0:R) ∈ D := sorry

definition kock_lawvere (f : ∀ d, d ∈ D → R) : 
           ∃! b : R, ∀ d (memD : d ∈ D), f d memD = f 0 zero_in_D + d * b := sorry

definition nat.to_R [coercion] (n : ℕ) : R := sorry

-- 1.1.3

lemma d0dd : ∀ d, d ∈ D → d * (0:R) = d * d := sorry

proposition cancel_d (a b : R) : (∀ d, d ∈ D → d * a = d * b) → a = b := sorry

proposition D_not_ideal : ¬ ∀ d₁ d₂ : R, d₁ ∈ D → d₂ ∈ D → d₁ + d₂ ∈ D := sorry

--definition D2 := { d : R × R | d.1 ^ 2 = 0 ∧ d.2 ^ 2 = 0 ∧ d.1 * d.2 = 0 }

definition D' (n : ℕ) := { d : vector R n | ∀ i j, d i * d j = 0 } 

--cartesian product notation? better name?
proposition D'n_ne_Dn : ∀ n, n ≥ 2 → D' n ≠ { d : vector R n | ∀ i, d i ∈ D } := sorry

-- 1.1.4

definition euclidean_module [class] (E : Type) [vector_space R E] := ∀ (f : ∀ d : R, d ∈ D → E),
           ∃! b : E, ∀ d (memD : d ∈ D), f d memD = f 0 zero_in_D + d • b

definition Rn_vector_space {n : ℕ} : vector_space R (vector R n) := sorry

--use typeclasses properly to make this cleaner?
proposition Rn_euclidean {n : ℕ} : @euclidean_module _ _ (vector R n) Rn_vector_space := sorry

--proposition : any product of Euclidean R-modules is a Euclidean R-module

--proposition function_euclidean_module (X E : Type) [euclidean_module E] 

-- 1.2

-- 1.2.1

definition derivative_exists (f : R → R) (a : R) : 
           Σ b, ∀ d (memD : d ∈ D), f (a + d) = f a + d * b := sorry

definition der (f : R → R) (a : R) : R :=
obtain b h, from derivative_exists f a, b
postfix `′`:80 := der

definition der' (f : R → R) : ℕ → R → R
| 0 := f
| (n+1) := (der' n)
notation f`₍`n`₎` := der' f n

definition function_field [instance] : vector_space R (R → R) := sorry
definition function_alg   [instance] : comm_ring (R → R) := sorry

section derivative

  variables (f g : R → R) (α : R)

  theorem der_add : (f + g)′ = f′ + g′ := sorry

  theorem der_smul : (α • f)′ = α • f′ := sorry

  theorem der_mul : (f * g)′ = f′ * g + f * g′ := sorry

  theorem chain_rule : (f ∘ g)′ = (f′ ∘ g) * g′ := sorry

end derivative

-- 1.2.2

proposition taylor (f : R → R) (x : R) (k : ℕ) : ∀ (d : vector R k) (memD : ∀ i, d i ∈ D), 
            let δ := ∑ i ← upto k, d i in
            f (x + δ) = ∑ n ← upto k, f₍n₎ x * δ ^ n / (nat.to_R (fact n)) := sorry

-- 1.2.3

definition directional_derivative_exists {V E : Type} [vector_space R V] [vector_space R E] 
           [@euclidean_module R _ E _] (f : V → E) (u a : V) : 
           Σ b, ∀ (d : R) (memD : d ∈ D), f (a + d • u) = (f a) + (d • b) := 
sorry

definition directional_derivative {V E : Type} [vector_space R V] [vector_space R E] 
           [@euclidean_module R _ E _] (f : V → E) (u a : V) : E := 
sorry
--obtain b h, from directional_derivative_exists f u a, b
prefix `∂`:80 := directional_derivative

--theorem linear_direction

-- 1.3

-- 1.3.1

structure preorder [class] (r : R → R → Prop) :=
(refl  : ∀ x, r x x)
(trans : ∀ x y z, r x y → r y z → r x z)
(add   : ∀ x y z, r x y → r (x + z) (y + z))
(mul   : ∀ x y, r 0 x → r 0 y → r 0 (x * y))
(zero_le_one  : r 0 1)
(one_nle_zero : ¬ r 1 0)
(zero_le_D : ∀ d, d ∈ D → r 0 d)
(D_le_zero : ∀ d, d ∈ D → r d 0)

section preorder

  variables {r : R → R → Prop} [preorder r]

  local infix `≼`:80 := r

  definition interval (a b : R) : set R := { x : R | a ≼ x ∧ x ≼ b }

  notation `'[`a`,`b`]` := interval a b

  proposition D_in_00 : D ⊆ '[(0:R), (0:R)] := sorry

end preorder


-- 2

definition is_microlinear_object (T : Type) : Type := sorry

-- 3.1.1

section

  variables {M : Type} [is_microlinear_object M] (m : M)

  definition is_tangent_vector := Σ (t : ∀ d : R, d ∈ D → M), t 0 zero_in_D = m

  
end
