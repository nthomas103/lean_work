import standard
open prod prod.ops subtype real nat fin algebra


--types

check (λ n : ℕ, n)
check (λ a b : ℕ, a + b)
check ℕ
check (λ a b : ℕ, a = b + 1)
check true
check λ n : ℕ, n ≥ 1
check λ (x : ℝ) (H : x ≠ 3), 1 / (x - 3)
check @nat.induction_on
check Prop
check Type₁
check Type₂


--defining functions

definition add_one : ℕ → ℕ :=
λ n : ℕ, n + 1

eval add_one 5


--higher-order functions

constant exp : ℝ → ℝ
constant gcd : ℕ → ℕ → ℕ
constant derivative : (ℝ → ℝ) → (ℝ → ℝ)
constant integral : (ℝ → ℝ) → ℝ → ℝ → ℝ
constant path_integral : ((ℝ → ℝ) → ℝ) → ℝ → ℝ → ℝ

definition do_twice : (ℕ → ℕ) → (ℕ → ℕ) :=
λ (f : ℕ → ℕ) (x : ℕ), f (f x)

eval do_twice add_one 4


--recursion

definition fib : ℕ → ℕ
| fib 0     := 1
| fib 1     := 1
| fib (a+2) := fib (a+1) + fib a

eval fib 0
eval fib 1
eval fib 2
eval fib 3
eval fib 4
eval fib 5
eval fib 6
eval fib 7

theorem fib_pos : ∀ n, 0 < fib n
| fib_pos 0 := zero_lt_one
| fib_pos 1 := zero_lt_one
| fib_pos (a+2) := calc
  0 = 0 + 0             : rfl
... < fib (a+1) + 0     : !add_lt_add_right !fib_pos
... < fib (a+1) + fib a : !add_lt_add_left  !fib_pos
... = fib (a+2)         : rfl

theorem nat_induct (P : ℕ → Prop) : ∀ n, P 0 → (∀ n, P n → P (n+1)) → P n
| 0     p₀  _     := p₀
| (n+1) p₀  pind  := pind n (nat_induct n p₀ pind)


--polymorphism

definition id_fun : Π (T : Type), T → T :=
λ (T : Type) (x : T), x

definition do_thrice : Π (T : Type), (T → T) → (T → T) :=
λ (T : Type) (f : T → T) (x : T), f (f (f x))



definition composition : Π (A B C : Type), (A → B) → (B → C) → (A → C) :=
λ (A B C : Type) (f : A → B) (g : B → C) (a : A), g (f a)

definition swap' : Π A B C, (A → B → C) → (B → A → C) := 
λ A B C f b a, f a b

definition swap {A B C} (f : A → B → C) (b : B) (a : A) : C := f a b



definition curry [reducible] {A B C} (f : A × B → C) : A → B → C :=
λ a b, f (a,b)

definition uncurry [reducible] {A B C} (f : A → B → C) : A × B → C :=
λ ab, f ab.1 ab.2



theorem uncurry_curry {A B C} (f : A → B → C) : curry (uncurry f) = f :=
!eq.refl
/-funext (λ a, funext (λ b,
  calc curry (uncurry f) a b = (uncurry f) (a,b) : rfl
             ...             = f (a,b).1 (a,b).2 : rfl
             ...             = f (a,b).1 b       : pr2.mk a b
             ...             = f a b             : pr1.mk a b))-/

reveal uncurry_curry
print uncurry_curry

theorem curry_uncurry {A B C} (f : A × B → C) : uncurry (curry f) = f := 
funext (by blast)
/-funext (λ ab, calc uncurry (curry f) ab = (curry f) ab.1 ab.2 : rfl
                           ...          = f (ab.1,ab.2)       : rfl
                           ...          = f ab                : eta)-/

print funext

reveal curry_uncurry
print curry_uncurry


--dependent types

constant safe_log : Π (x : ℝ), x > 0 → ℝ
constant safe_inv : Π (x : ℝ), x ≠ 0 → ℝ

constant differentiable : (ℝ → ℝ) → Prop
constant safe_deriv : Π (f : ℝ → ℝ), differentiable f → (ℝ → ℝ)

constant vector : Π (T : Type) (n : ℕ), fin n → T
constant matrix : Π (T : Type) (m n : ℕ), fin m → fin n → T

example : Π (a b : ℕ), a < b → a + a < b + b := sorry

definition prime (p : nat) := p ≥ 2 ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

print prime


--inductive types

namespace hide

inductive bool : Type :=
| tru : bool
| fal : bool

print bool.rec


inductive nat : Type :=
| o : nat
| s : nat → nat

print nat.rec


inductive list' : Type :=
| nil  : list'
| cons : nat → list' → list'

inductive list (T : Type) : Type :=
| nil {} : list T
| cons   : T → list T → list T

namespace list
notation h :: t  := cons h t
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

variable {T : Type}

definition length : list T → ℕ
| []       := 0
| (a :: l) := length l + 1

definition append : list T → list T → list T
| []        l₂ := l₂
| (h :: l₁) l₂ := h :: (append l₁ l₂)

notation l₁ ++ l₂ := append l₁ l₂

eval [1,2,3] ++ [3,2,(1:ℕ)]

definition mem : T → list T → Prop
| a [] := false
| a (b :: l) := a = b ∨ mem a l

variables {A B : Type}

definition map (f : A → B) : list A → list B
| []       := []
| (a :: l) := f a :: map l

end list



inductive btree : Type := 
| leaf : ℕ → btree
| node : ℕ → btree → btree → btree

print btree.rec



inductive eq (A : Type) : Type :=
| refl : ∀ a : A, a = a → eq A

print eq.rec



-- Curry-Howard correspondence

inductive and (A B : Prop) :=
| mk : A → B → and A B

inductive or (A B : Prop) :=
| inl : A → or A B
| inr : B → or A B

inductive false : Prop

print false

definition not (A : Prop) : Prop := A → false

print not

end hide

theorem my_stupid_theorem (p q : Prop) : p → p ∨ q :=
assume Hp : p, 
or.inl Hp

theorem and_comm (p q : Prop) : p ∧ q → q ∧ p :=
assume Hpq : p ∧ q,
and.intro (and.right Hpq) (and.left Hpq)



--structures: monoids, semigroups, groups, etc etc

namespace hide

structure has_mul (A : Type) :=
(mul : A → A → A)

print has_mul

inductive has_mul' (A : Type) :=
| mk : (A → A → A) → has_mul' A


structure semigroup (A : Type) extends has_mul A :=
(assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))

inductive semigroup' (A : Type) :=
| mk : ∀ (mul : A → A → A), (∀ a b c, mul (mul a b) c = mul a (mul b c)) → 
       semigroup' A


structure has_one (A : Type) :=
(one : A)

print has_one


structure has_inv (A : Type) :=
(inv : A → A)


structure monoid (A : Type) extends has_mul A, has_one A :=
(right_id : ∀ a, mul a one = a)
(left_id  : ∀ a, mul one a = a)


structure comm_semigroup (A : Type) extends semigroup A :=
(comm : ∀ a b, mul a b = mul b a)


structure comm_monoid (A : Type) extends comm_semigroup A, monoid A

print hide.comm_monoid


structure group (A : Type) extends monoid A, has_inv A :=
(mul_left_inv : ∀ a, mul (inv a) a = one)


end hide

section group_proofs

variables {G : Type} [group G]

example (a : G) (h₁ : a = a⁻¹) : a * a = 1 := calc
a * a = a⁻¹ * a : {h₁}
  ... = 1       : !group.mul_left_inv

example (a : G) (h₁ : a = a⁻¹) : a * a = 1 := by inst_simp


end group_proofs
