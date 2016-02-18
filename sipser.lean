import standard algebra.order_bigops
open algebra fin finset num nat fintype stream prod prod.ops list set
open sigma sigma.ops decidable

structure turing_machine (Q Γ : Type) :=
[fintypeQ : fintype Q]
[fintypeΓ : fintype Γ]
[dec_eqQ  : decidable_eq Q]
(b : Γ) --TODO maybe should require that b in not in the input
(q₀ : Q)
(qa : Q)
(qr : Q)
(qa_ne_qr : qa ≠ qr)
(δ : Q → Γ → Q × Γ × bool)

definition stream_sub {A : Type} 
           (s : stream A) (n : ℕ) (a : A) : stream A :=
λ m : ℕ, if m = n then a else s m

definition TM_move (b : bool) (n : ℕ) : ℕ :=
if b = bool.tt then n - 1 else n + 1

definition TM_compute_aux {Q Γ : Type} 
           (TM : turing_machine Q Γ) :
           Q → stream Γ → ℕ → ℕ → (Q × stream Γ × ℕ)
| q s n 0     := (q, s, n)
| q s n (t+1) := let out := (turing_machine.δ TM q (s n)) in
                     TM_compute_aux out.1.1
                       (stream_sub s n out.1.2) 
                       (TM_move out.2 n) t

definition TM_compute {Q Γ : Type} 
           (TM : turing_machine Q Γ) 
           (input : list Γ)
           (t : ℕ) 
           : Q × stream Γ × ℕ :=
TM_compute_aux TM (turing_machine.q₀ TM) 
               (input ++ (const (turing_machine.b TM))) 0 t

definition TM_accepts {Q Γ : Type}
           (TM : turing_machine Q Γ)
           (input : list Γ) :=
∃ t, (TM_compute TM input t).1.1 = turing_machine.qa TM
∧ ¬ ∃ t', t' < t → 
     (TM_compute TM input t).1.1 = turing_machine.qr TM

definition TM_rejects {Q Γ : Type}
           (TM : turing_machine Q Γ)
           (input : list Γ) :=
∃ t, (TM_compute TM input t).1.1 = turing_machine.qr TM
∧ ¬ ∃ t', t' < t → 
     (TM_compute TM input t).1.1 = turing_machine.qa TM

definition TM_halts {Q Γ : Type}
           (TM : turing_machine Q Γ)
           (input : list Γ) :=
TM_accepts TM input ∨ TM_rejects TM input

definition TM_halts_time {Q Γ : Type}
           (TM : turing_machine Q Γ)
           (input : list Γ) :=
Σ t, (TM_compute TM input t).1.1 ∈ 
                 '{turing_machine.qa TM, turing_machine.qr TM} ∧
¬ ∃ t', t' < t → 
     (TM_compute TM input t').1.1 ∈ 
                 '{turing_machine.qa TM, turing_machine.qr TM}

definition turing_recognizable {Γ : Type} (L : set (list Γ)) :=
∃ (Q : Type) (TM : turing_machine Q Γ), 
   ∀ s, s ∈ L → TM_accepts TM s

definition TM_decides {Q Γ : Type}
           (TM : turing_machine Q Γ)
           (L : set (list Γ)) : Prop := 
(∀ s, s ∈ L → TM_accepts TM s) ∧
(∀ s, s ∉ L → TM_rejects TM s)

definition turing_decidable {Γ : Type} (L : set (list Γ)) :=
∃ (Q : Type) (TM : turing_machine Q Γ), TM_decides TM L

/-
--not totally sure about this
definition turing_dec_to_dec {Γ : Type} (L : set (list Γ)) : 
           turing_decidable L → ∀ s, decidable (s ∈ L) :=
sorry
--example (A B C : Prop) (h₁ : A → B) (h₂ : ¬A → C) : 
-/

/-
constant encode {Q Γ : Type} (TM : turing_machine Q Γ) : list Γ
constant UQ : Type
constant UTM {Γ : Type} : turing_machine UQ Γ
constant UTM_spec {Q Γ : Type} (TM : turing_machine Q Γ) (input : list Γ) : 
         TM_accepts UTM ((encode TM) ++ input) = TM_accepts TM input ∧
         TM_rejects UTM ((encode TM) ++ input) = TM_rejects TM input
-/

--theorem TM_undecidable {Γ : Type} : ¬ turing_decidable 

definition list_append {A : Type} (F : list A) : 
                       list (list A) → list (list A)
| []       := []
| (l :: L) := (map (λ a : A, a :: l) F) ++ (list_append L)

definition Γ [reducible] : Type₁ := bool
/- alternatively:
constant {Γ : Type₁}
constant [finΓ : fintype Γ]
constant [Γ_dec_eq : decidable_eq Γ]

attribute [instance] finΓ Γ_dec_eq
-/

definition len_list : ℕ → list (list Γ)
| 0     := [[]]
| (n+1) := list_append (fintype.elems Γ) (len_list n)

definition len_finset (n : ℕ) : finset (list Γ) :=
to_finset (len_list n)

definition time_complexity {Q : Type}
           (TM : turing_machine Q Γ) 
           (halts : Π input, TM_halts_time TM input) (n : ℕ) : ℕ := 
Max input ∈ (len_finset n), (halts input).1

section o_notation
  open real

  definition big_O (f g : ℕ → ℕ) :=  
    ∃ c n0, ∀ n, n ≥ n0 → f n ≤ c * g n
  infixl `=O`:50 := big_O

  definition little_o (f g : ℕ → ℕ) := 
    ∀ (c : ℝ), ∃ n0, ∀n, n ≥ n0 → f n < c * g n
  infixl `=o`:50 := little_o
end o_notation

definition TIME (t : ℕ → ℕ) : set (set (list Γ)) :=
{L : set (list Γ) | 
  ∃ (Q : Type) (TM : turing_machine Q Γ) (halts : Π i, TM_halts_time TM i), 
    TM_decides TM L ∧ (@time_complexity Q TM halts =O t)}

definition P : set (set (list Γ)) := 
{L : set (list Γ) | ∃ k : ℕ, L ∈ TIME (λ n, n ^ k)} 

definition is_poly_time_verifiable (L : set (list Γ)) :=
  ∃ (Q : Type) (TM : turing_machine Q Γ) (halts : Π i, TM_halts_time TM i)
    (c : list Γ → list Γ), 
    L = {w | TM_accepts TM (w ++ (c w))} ∧ ∃ k : ℕ, 
    (λ n, Max i ∈ (len_finset n), (halts (i++(c i))).1) =O (λ n, n ^ k)
   
definition NP : set (set (list Γ)) :=
           { L | is_poly_time_verifiable L }

theorem P_ne_NP : P ≠ NP := sorry

