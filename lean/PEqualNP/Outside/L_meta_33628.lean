import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33628_aux

def ix (n : ℕ) (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

def rot (n : ℕ) (hn : 0 < n) (s : ℕ) (w : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  w (ix n hn (i.val + n - s % n))

def out (n : ℕ) (hn : 0 < n) (name c raw : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  let old := rot n hn 3 raw + name
  let y := fun j : Fin n => old j + old (ix n hn (j.val+2)) + old (ix n hn (j.val+n-2))
  y i + (1+y (ix n hn (i.val+1)))*y (ix n hn (i.val+2)) + rot n hn 4 raw i + c i

noncomputable def run (n h : ℕ) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w : Fin n → ZMod 2) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)

noncomputable def base (n : ℕ) (j : Fin 4) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2) then (1 : ZMod 2) else 0

noncomputable def even (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = 0 then z i else 0

def mix (n : ℕ) (hn : 0 < n) (w : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  let old := rot n hn 3 w
  old i + old (ix n hn (i.val+2)) + old (ix n hn (i.val+n-2))

noncomputable def tw (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (z : Fin n → ZMod 2) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (List.ofFn (fun i : Fin n =>
    let s : ℤ := if z i = 0 then 1 else -1
    let a : ℤ := if mark (ix n hn (i.val+n-2)) then 0 else s
    (!![1,s;1,a] : Matrix (Fin 2) (Fin 2) ℤ))).prod.trace

noncomputable def Ssum (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool)
    (D : Submodule (ZMod 2) (Fin n → ZMod 2)) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∑ z ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun z => z ∈ D), tw n hn mark z

def sgn (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

def dot (n : ℕ) (z x : Fin n → ZMod 2) : ZMod 2 := ∑ i, z i * x i

def adm (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (x : Fin n → ZMod 2) : Prop :=
  ∀ i, mark i = true → x (ix n hn (i.val+1)) * x (ix n hn (i.val+2)) = 0

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma z2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma z2_sub (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma fn_sub (n : ℕ) (a b : Fin n → ZMod 2) : a - b = a + b := by
  funext i
  exact z2_sub (a i) (b i)

lemma fn_add_self (n : ℕ) (a : Fin n → ZMod 2) : a + a = 0 := by
  funext i
  exact z2_add_self (a i)

lemma sgn_zero : sgn 0 = 1 := rfl

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> decide

lemma ix_val (n : ℕ) (hn : 0 < n) (j : ℕ) : (ix n hn j).val = j % n := rfl

lemma ix_eq_iff (n : ℕ) (hn : 0 < n) (a b : ℕ) : ix n hn a = ix n hn b ↔ a % n = b % n := by
  simp [ix, Fin.ext_iff]

lemma ix_self (n : ℕ) (hn : 0 < n) (a : Fin n) : ix n hn a.val = a := by
  ext
  exact Nat.mod_eq_of_lt a.2

lemma ix_add_n (n : ℕ) (hn : 0 < n) (a : ℕ) : ix n hn (a + n) = ix n hn a := by
  rw [ix_eq_iff, Nat.add_mod_right]

lemma ix_val_add (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    ix n hn ((ix n hn a).val + b) = ix n hn (a + b) := by
  rw [ix_eq_iff]
  simp only [ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma dot_comm (n : ℕ) (z x : Fin n → ZMod 2) : dot n z x = dot n x z := by
  unfold dot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma dot_add_left (n : ℕ) (z z' x : Fin n → ZMod 2) :
    dot n (z + z') x = dot n z x + dot n z' x := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.add_apply]; ring)

lemma dot_add_right (n : ℕ) (z x x' : Fin n → ZMod 2) :
    dot n z (x + x') = dot n z x + dot n z x' := by
  rw [dot_comm, dot_add_left, dot_comm n x z, dot_comm n x' z]

lemma dot_smul_left (n : ℕ) (a : ZMod 2) (z x : Fin n → ZMod 2) :
    dot n (a • z) x = a * dot n z x := by
  unfold dot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

lemma dot_zero_left (n : ℕ) (x : Fin n → ZMod 2) : dot n 0 x = 0 := by
  unfold dot
  simp

lemma dot_zero_right (n : ℕ) (z : Fin n → ZMod 2) : dot n z 0 = 0 := by
  unfold dot
  simp

def dotL (n : ℕ) (x : Fin n → ZMod 2) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun z => dot n z x
    map_add' := fun z z' => dot_add_left n z z' x
    map_smul' := fun a z => dot_smul_left n a z x }

lemma dotL_apply (n : ℕ) (x z : Fin n → ZMod 2) : dotL n x z = dot n z x := rfl

lemma mix_add (n : ℕ) (hn : 0 < n) (w w' : Fin n → ZMod 2) :
    mix n hn (w + w') = mix n hn w + mix n hn w' := by
  funext i
  simp only [mix, rot, Pi.add_apply]
  ring

lemma mix_smul (n : ℕ) (hn : 0 < n) (a : ZMod 2) (w : Fin n → ZMod 2) :
    mix n hn (a • w) = a • mix n hn w := by
  funext i
  simp only [mix, rot, Pi.smul_apply, smul_eq_mul]
  ring

def mixL (n : ℕ) (hn : 0 < n) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := mix n hn
    map_add' := mix_add n hn
    map_smul' := mix_smul n hn }

lemma mixL_apply (n : ℕ) (hn : 0 < n) (w : Fin n → ZMod 2) : mixL n hn w = mix n hn w := rfl

lemma mix_zero (n : ℕ) (hn : 0 < n) : mix n hn 0 = 0 := (mixL n hn).map_zero

lemma mix_sub (n : ℕ) (hn : 0 < n) (w w' : Fin n → ZMod 2) :
    mix n hn (w - w') = mix n hn w - mix n hn w' := (mixL n hn).map_sub w w'

lemma even_apply (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) :
    even n z i = if i.val % 2 = 0 then z i else 0 := by
  unfold even
  split_ifs <;> rfl

lemma even_add (n : ℕ) (z z' : Fin n → ZMod 2) : even n (z + z') = even n z + even n z' := by
  funext i
  simp only [even_apply, Pi.add_apply]
  split_ifs <;> simp

lemma even_smul (n : ℕ) (a : ZMod 2) (z : Fin n → ZMod 2) : even n (a • z) = a • even n z := by
  funext i
  simp only [even_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

noncomputable def evenL (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := even n
    map_add' := even_add n
    map_smul' := even_smul n }

lemma evenL_apply (n : ℕ) (z : Fin n → ZMod 2) : evenL n z = even n z := rfl

lemma even_zero (n : ℕ) : even n 0 = 0 := (evenL n).map_zero

lemma even_even (n : ℕ) (z : Fin n → ZMod 2) : even n (even n z) = even n z := by
  funext i
  simp only [even_apply]
  split_ifs <;> rfl

lemma dot_even (n : ℕ) (z x : Fin n → ZMod 2) : dot n (even n z) x = dot n z (even n x) := by
  unfold dot
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [even_apply]
  split_ifs <;> simp

lemma base_apply (n : ℕ) (j : Fin 4) (i : Fin n) :
    base n j i = if i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2)
      then (1 : ZMod 2) else 0 := by
  unfold base
  split_ifs <;> rfl

noncomputable def orth (n : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (LinearMap.pi (fun u : U => dotL n (τ u)))

lemma mem_orth (n : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) (z : Fin n → ZMod 2) :
    z ∈ orth n τ ↔ ∀ u, dot n z (τ u) = 0 := by
  unfold orth
  rw [LinearMap.mem_ker]
  constructor
  · intro hz u
    have := congrFun hz u
    simpa [dotL_apply] using this
  · intro hz
    funext u
    simpa [dotL_apply] using hz u

lemma Ssum_eq (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool)
    (D : Submodule (ZMod 2) (Fin n → ZMod 2)) [DecidablePred (fun z => z ∈ D)] :
    Ssum n hn mark D = ∑ z : Fin n → ZMod 2, if z ∈ D then tw n hn mark z else 0 := by
  unfold Ssum
  rw [Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun z _ => ?_)
  · congr
    funext a b
    exact Subsingleton.elim _ _
  · split_ifs <;> rfl

def h1_pw : (m : ℕ) → (Fin m → Matrix (Fin 2) (Fin 2) ℤ) → Fin 2 → (Fin m → Fin 2) → ℤ
  | 0, _, _, _ => 1
  | m + 1, A, u, x => A 0 u (x 0) * h1_pw m (fun i => A i.succ) (x 0) (fun i => x i.succ)

def h1_last : (m : ℕ) → Fin 2 → (Fin m → Fin 2) → Fin 2
  | 0, u, _ => u
  | m + 1, _, x => h1_last m (x 0) (fun i => x i.succ)

lemma h1_path [DecidableEq (Fin 2)] (m : ℕ) :
    ∀ (A : Fin m → Matrix (Fin 2) (Fin 2) ℤ) (u v : Fin 2),
    (List.ofFn A).prod u v =
      ∑ x : Fin m → Fin 2, if h1_last m u x = v then h1_pw m A u x else 0 := by
  induction m with
  | zero =>
    intro A u v
    rw [List.ofFn_zero, List.prod_nil, Matrix.one_apply, Fintype.sum_unique]
    rfl
  | succ m ih =>
    intro A u v
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    rw [← (Fin.consEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [Fin.consEquiv_apply, h1_pw, h1_last, Fin.cons_zero, Fin.cons_succ]
    split_ifs <;> simp

lemma h1_last_succ (m : ℕ) : ∀ (u : Fin 2) (x : Fin (m + 1) → Fin 2),
    h1_last (m + 1) u x = x (Fin.last m) := by
  induction m with
  | zero =>
    intro u x
    rfl
  | succ m ih =>
    intro u x
    rw [h1_last, ih, Fin.succ_last]

lemma h1_pw_eq (m : ℕ) : ∀ (A : Fin m → Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2)
    (x p : Fin m → Fin 2), (∀ i : Fin m, i.val = 0 → p i = u) →
    (∀ i j : Fin m, i.val = j.val + 1 → p i = x j) →
    h1_pw m A u x = ∏ i, A i (p i) (x i) := by
  induction m with
  | zero =>
    intro A u x p _ _
    simp [h1_pw]
  | succ m ih =>
    intro A u x p h0 h1
    rw [h1_pw, Fin.prod_univ_succ, h0 0 rfl]
    congr 1
    exact ih (fun i => A i.succ) (x 0) (fun i => x i.succ) (fun i => p i.succ)
      (fun i hi => h1 i.succ 0 (by simp [hi])) (fun i j hij => h1 i.succ j.succ (by simp [hij]))

lemma h1_trace0 [DecidableEq (Fin 2)] (n : ℕ) (hn : 0 < n)
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℤ) :
    (List.ofFn A).prod.trace =
      ∑ x : Fin n → Fin 2, ∏ i, A i (x (ix n hn (i.val + n - 1))) (x i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, h1_path, h1_last_succ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  apply h1_pw_eq
  · intro i hi
    congr 1
    ext
    simp [ix, hi]
  · intro i j hij
    congr 1
    have hj : i.val + (m + 1) - 1 = j.val + (m + 1) := by omega
    rw [hj, ix_add_n, ix_self]

lemma h1_trace [DecidableEq (Fin 2)] (n : ℕ) (hn : 0 < n)
    (A : Fin n → Matrix (Fin 2) (Fin 2) ℤ) :
    (List.ofFn A).prod.trace =
      ∑ x : Fin n → ZMod 2, ∏ i, A i (x (ix n hn (i.val + n - 1))) (x i) :=
  h1_trace0 n hn A

lemma h1_sgn_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

lemma h1_mat_apply (s a : ℤ) (u v : ZMod 2) :
    (!![1, s; 1, a] : Matrix (Fin 2) (Fin 2) ℤ) u v =
      if v = 0 then 1 else if u = 0 then s else a := by
  rcases z2_cases u with rfl | rfl <;> rcases z2_cases v with rfl | rfl <;> rfl

lemma h1_entry (P : Prop) [Decidable P] (zi : ZMod 2) [Decidable (zi = 0)] (u v : ZMod 2) :
    (!![1, (if zi = 0 then 1 else -1); 1, if P then 0 else (if zi = 0 then 1 else -1)] :
      Matrix (Fin 2) (Fin 2) ℤ) u v =
      if ¬ (P ∧ u = 1 ∧ v = 1) then sgn (zi * v) else 0 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rw [h1_mat_apply]
  by_cases hP : P <;> rcases z2_cases zi with rfl | rfl <;> rcases z2_cases u with rfl | rfl <;>
    rcases z2_cases v with rfl | rfl <;> simp [sgn, hP, h10]

lemma h1_f1 (n : ℕ) (hn : 0 < n) (i : Fin n) :
    ix n hn ((ix n hn (i.val + 2)).val + n - 2) = i := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact Subsingleton.elim _ _
  · have e : (ix n hn (i.val + 2)).val + n - 2 = (ix n hn (i.val + 2)).val + (n - 2) := by omega
    have e2 : i.val + 2 + (n - 2) = i.val + n := by omega
    rw [e, ix_val_add, e2, ix_add_n, ix_self]

lemma h1_f2 (n : ℕ) (hn : 0 < n) (i : Fin n) :
    ix n hn ((ix n hn (i.val + 2)).val + n - 1) = ix n hn (i.val + 1) := by
  have e : (ix n hn (i.val + 2)).val + n - 1 = (ix n hn (i.val + 2)).val + (n - 1) := by omega
  have e2 : i.val + 2 + (n - 1) = i.val + 1 + n := by omega
  rw [e, ix_val_add, e2, ix_add_n]

lemma h1_f3 (n : ℕ) (hn : 0 < n) (j : Fin n) :
    ix n hn ((ix n hn (j.val + n - 2)).val + 2) = j := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact Subsingleton.elim _ _
  · have e2 : j.val + n - 2 + 2 = j.val + n := by omega
    rw [ix_val_add, e2, ix_add_n, ix_self]

lemma h1_f4 (n : ℕ) (hn : 0 < n) (j : Fin n) :
    ix n hn ((ix n hn (j.val + n - 2)).val + 1) = ix n hn (j.val + n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact Subsingleton.elim _ _
  · have e2 : j.val + n - 2 + 1 = j.val + n - 1 := by omega
    rw [ix_val_add, e2]

lemma h1_adm_iff (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (x : Fin n → ZMod 2) :
    (∀ i : Fin n, ¬ (mark (ix n hn (i.val + n - 2)) = true ∧
      x (ix n hn (i.val + n - 1)) = 1 ∧ x i = 1)) ↔ adm n hn mark x := by
  constructor
  · intro H i hi
    have h := H (ix n hn (i.val + 2))
    rw [h1_f1, h1_f2] at h
    rcases z2_cases (x (ix n hn (i.val + 1))) with h1 | h1
    · rw [h1, zero_mul]
    · rcases z2_cases (x (ix n hn (i.val + 2))) with h2 | h2
      · rw [h2, mul_zero]
      · exact absurd ⟨hi, h1, h2⟩ h
  · rintro H j ⟨hm, h1, h2⟩
    have h := H (ix n hn (j.val + n - 2)) hm
    rw [h1_f3, h1_f4, h1, h2] at h
    exact absurd h (by decide)

open Classical in
lemma tw_eq_sum (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (z : Fin n → ZMod 2) :
    tw n hn mark z = ∑ x : Fin n → ZMod 2, if adm n hn mark x then sgn (dot n z x) else 0 := by
  unfold tw
  rw [@h1_trace (fun a b => Classical.propDecidable (a = b)) n hn]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [h1_entry]
  by_cases h : adm n hn mark x
  · rw [ite_eq_left h]
    have H := (h1_adm_iff n hn mark x).mpr h
    simp only [H, not_false_eq_true, ite_true]
    rw [← h1_sgn_sum]
    rfl
  · rw [ite_eq_right h]
    have H : ¬ ∀ i : Fin n, ¬ (mark (ix n hn (i.val + n - 2)) = true ∧
        x (ix n hn (i.val + n - 1)) = 1 ∧ x i = 1) :=
      fun h' => h ((h1_adm_iff n hn mark x).mp h')
    rw [not_forall] at H
    obtain ⟨i, hi⟩ := H
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, ite_false]

open Classical in
lemma h2_sum_sgn_linear {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (φ : V →ₗ[ZMod 2] ZMod 2) :
    (∑ x : V, sgn (φ x)) = if φ = 0 then (Fintype.card V : ℤ) else 0 := by
  split_ifs with hφ
  · subst hφ
    simp [sgn_zero]
  · have hne : ∃ x0 : V, φ x0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    rcases hne with ⟨x0, hx0⟩
    have hx0_one : φ x0 = 1 := by
      rcases z2_cases (φ x0) with h | h
      · exact absurd h hx0
      · exact h
    have hx00 : x0 + x0 = 0 := by
      have h3 : (1 + 1 : ZMod 2) • x0 = x0 + x0 := by rw [add_smul, one_smul]
      rw [← h3, z2_add_self, zero_smul]
    have hbij : Function.Bijective (fun x : V => x + x0) :=
      ⟨fun x y h => by
        have := congrArg (fun z => z + x0) h
        simpa [add_assoc, hx00] using this,
       fun y => ⟨y + x0, by simp [add_assoc, hx00]⟩⟩
    have hshift : (∑ x : V, sgn (φ x)) = ∑ x : V, sgn (φ (x + x0)) :=
      (Fintype.sum_bijective (fun x => x + x0) hbij _ _ fun _ => rfl).symm
    have hneg : (∑ x : V, sgn (φ (x + x0))) = -(∑ x : V, sgn (φ x)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have h1 : sgn 1 = -1 := by decide
      rw [map_add, hx0_one, sgn_add, h1]
      ring
    linarith

lemma h2_dotL_eq_zero (n : ℕ) (v : Fin n → ZMod 2) : dotL n v = 0 ↔ v = 0 := by
  classical
  constructor
  · intro h
    funext i
    have h1 := LinearMap.congr_fun h (Pi.single i 1)
    rw [dotL_apply] at h1
    unfold dot at h1
    simpa [Pi.single_apply] using h1
  · intro h
    subst h
    refine LinearMap.ext (fun z => ?_)
    rw [dotL_apply, dot_zero_right]
    rfl

lemma h2_sum_sgn_dot (n : ℕ) (v : Fin n → ZMod 2) :
    (∑ z : Fin n → ZMod 2, sgn (dot n z v)) = if v = 0 then (2:ℤ)^n else 0 := by
  classical
  have h := h2_sum_sgn_linear (dotL n v)
  have h2 : ∀ z, sgn (dot n z v) = sgn (dotL n v z) := fun z => rfl
  rw [Finset.sum_congr rfl (fun z _ => h2 z), h]
  by_cases hv : v = 0
  · rw [ite_eq_left hv, ite_eq_left ((h2_dotL_eq_zero n v).mpr hv)]
    simp
  · rw [ite_eq_right hv, ite_eq_right (fun h' => hv ((h2_dotL_eq_zero n v).mp h'))]

open Classical in
lemma h2_sum_sgn_tau (n : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Fintype U]
    (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) (z : Fin n → ZMod 2) :
    (∑ u : U, sgn (dot n z (τ u))) = if z ∈ orth n τ then (Fintype.card U : ℤ) else 0 := by
  have h := h2_sum_sgn_linear ((dotL n z).comp τ)
  have h1 : ((dotL n z).comp τ = 0) ↔ z ∈ orth n τ := by
    rw [mem_orth]
    constructor
    · intro h0 u
      have h3 := LinearMap.congr_fun h0 u
      rw [LinearMap.comp_apply, dotL_apply, dot_comm] at h3
      exact h3
    · intro h0
      refine LinearMap.ext (fun u => ?_)
      rw [LinearMap.comp_apply, dotL_apply, dot_comm, h0 u]
      rfl
  have h2 : ∀ u, sgn (dot n z (τ u)) = sgn ((dotL n z).comp τ u) := fun u => by
    rw [LinearMap.comp_apply, dotL_apply, dot_comm]
  rw [Finset.sum_congr rfl (fun u _ => h2 u), h]
  by_cases hz : z ∈ orth n τ
  · rw [ite_eq_left hz, ite_eq_left (h1.mpr hz)]
  · rw [ite_eq_right hz, ite_eq_right (fun h' => hz (h1.mp h'))]

open Classical in
lemma h2_inversion (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (x : Fin n → ZMod 2) :
    (∑ z : Fin n → ZMod 2, tw n hn mark z * sgn (dot n z x)) =
      if adm n hn mark x then (2:ℤ)^n else 0 := by
  have h1 : ∀ z : Fin n → ZMod 2, tw n hn mark z * sgn (dot n z x) =
      ∑ x' : Fin n → ZMod 2, if adm n hn mark x' then sgn (dot n z (x' + x)) else 0 := by
    intro z
    rw [tw_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    split_ifs
    · rw [dot_add_right, sgn_add]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl (fun z _ => h1 z), Finset.sum_comm]
  have h2 : ∀ x' : Fin n → ZMod 2,
      (∑ z : Fin n → ZMod 2, if adm n hn mark x' then sgn (dot n z (x' + x)) else 0) =
        if x' = x then (if adm n hn mark x then (2:ℤ)^n else 0) else 0 := by
    intro x'
    by_cases ha : adm n hn mark x'
    · simp only [ite_eq_left ha]
      rw [h2_sum_sgn_dot]
      by_cases hx : x' = x
      · subst hx
        rw [ite_eq_left (fn_add_self n x'), ite_eq_left rfl, ite_eq_left ha]
      · rw [ite_eq_right hx, ite_eq_right]
        intro h0
        apply hx
        have h3 : x' = x' + x + x := by rw [add_assoc, fn_add_self, add_zero]
        rw [h3, h0, zero_add]
    · simp only [ite_eq_right ha, Finset.sum_const_zero]
      by_cases hx : x' = x
      · subst hx
        rw [ite_eq_left rfl, ite_eq_right ha]
      · rw [ite_eq_right hx]
  rw [Finset.sum_congr rfl (fun x' _ => h2 x')]
  simp

lemma fourier_count (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) {U : Type} [AddCommGroup U]
    [Module (ZMod 2) U] [Finite U] (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (2:ℤ)^n * (Nat.card {u : U // adm n hn mark (τ u)} : ℤ) =
      (Nat.card U : ℤ) * Ssum n hn mark (orth n τ) := by
  classical
  have := Fintype.ofFinite U
  rw [Ssum_eq, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : (2:ℤ)^n * ((Finset.univ.filter (fun u : U => adm n hn mark (τ u))).card : ℤ) =
      ∑ u : U, ∑ z : Fin n → ZMod 2, tw n hn mark z * sgn (dot n z (τ u)) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [h2_inversion]
    split_ifs <;> simp
  rw [h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← Finset.mul_sum, h2_sum_sgn_tau]
  split_ifs <;> ring

lemma orth_card (n : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (τ : U →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card U * Nat.card (orth n τ) = 2^n * Nat.card {u : U // τ u = 0} := by
  classical
  have := Fintype.ofFinite U
  have key : (Fintype.card U : ℤ) * (Fintype.card (orth n τ) : ℤ) =
      (2:ℤ)^n * (Fintype.card {u : U // τ u = 0} : ℤ) := by
    have e1 : (∑ z : Fin n → ZMod 2, ∑ u : U, sgn (dot n z (τ u))) =
        (Fintype.card U : ℤ) * (Fintype.card (orth n τ) : ℤ) := by
      rw [Finset.sum_congr rfl (fun z _ => h2_sum_sgn_tau n τ z)]
      rw [Fintype.card_of_subtype (Finset.univ.filter (fun z => z ∈ orth n τ)) (by simp)]
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      split_ifs <;> simp
    have e2 : (∑ z : Fin n → ZMod 2, ∑ u : U, sgn (dot n z (τ u))) =
        (2:ℤ)^n * (Fintype.card {u : U // τ u = 0} : ℤ) := by
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun u _ => h2_sum_sgn_dot n (τ u))]
      rw [Fintype.card_of_subtype (Finset.univ.filter (fun u => τ u = 0)) (by simp)]
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      split_ifs <;> simp
    rw [← e1, e2]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact_mod_cast key

lemma h2_orth_card_subtype (n : ℕ) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card V * Nat.card (orth n V.subtype) = 2^n := by
  have h := orth_card n V.subtype
  have h1 : Nat.card {u : V // V.subtype u = 0} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, rfl⟩⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have ha := a.2
    have hb := b.2
    rw [Submodule.subtype_apply] at ha hb
    rw [ha, hb]
  rw [h, h1, mul_one]

lemma double_orth (n : ℕ) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) (x : Fin n → ZMod 2)
    (hx : ∀ z, (∀ v ∈ V, dot n z v = 0) → dot n z x = 0) : x ∈ V := by
  classical
  have h1 : Nat.card V * Nat.card (orth n V.subtype) = 2^n :=
    h2_orth_card_subtype n V
  have h2 : Nat.card (orth n V.subtype) * Nat.card (orth n (orth n V.subtype).subtype) = 2^n :=
    h2_orth_card_subtype n (orth n V.subtype)
  have hpos : 0 < Nat.card (orth n V.subtype) := Nat.card_pos
  have h3 : Nat.card (orth n (orth n V.subtype).subtype) = Nat.card V := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h2, mul_comm, h1]
  have hle : V ≤ orth n (orth n V.subtype).subtype := by
    intro v hv
    rw [mem_orth]
    intro u
    have h4 := (mem_orth n V.subtype u.1).mp u.2 ⟨v, hv⟩
    rw [dot_comm]
    exact h4
  have heq : V = orth n (orth n V.subtype).subtype := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have c1 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)]
      simp
    have c2 : Nat.card (orth n (orth n V.subtype).subtype) =
        2 ^ Module.finrank (ZMod 2) (orth n (orth n V.subtype).subtype) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := orth n (orth n V.subtype).subtype)]
      simp
    rw [c1, c2] at h3
    exact le_of_eq (Nat.pow_right_injective (le_refl 2) h3)
  rw [heq, mem_orth]
  intro u
  rw [dot_comm]
  refine hx u.1 (fun v hv => ?_)
  exact (mem_orth n V.subtype u.1).mp u.2 ⟨v, hv⟩

lemma lane_pure_span (n h : ℕ) (B D : Submodule (ZMod 2) (Fin n → ZMod 2)) (hBD : B ≤ D)
    (hB : ∀ z ∈ B, even n z ∈ B) (hD : ∀ z ∈ D, even n z ∈ D)
    (hfin : Module.finrank (ZMod 2) D ≤ h + Module.finrank (ZMod 2) B) :
    ∃ v : Fin h → (Fin n → ZMod 2), (∀ j, even n (v j) = v j ∨ even n (v j) = 0) ∧
      (∀ j, v j ∈ D) ∧ D ≤ B ⊔ Submodule.span (ZMod 2) (Set.range v) := by
  induction h generalizing B with
  | zero =>
    have hEq : B = D := Submodule.eq_of_le_of_finrank_le hBD (by simpa using hfin)
    refine ⟨fun _ => 0, fun j => j.elim0, fun j => j.elim0, ?_⟩
    rw [hEq]
    exact le_sup_left
  | succ h ih =>
    by_cases hEq : B = D
    · refine ⟨fun _ => 0, fun _ => Or.inl (even_zero n), fun _ => D.zero_mem, ?_⟩
      rw [hEq]
      exact le_sup_left
    · have hlt : B < D := lt_of_le_of_ne hBD hEq
      obtain ⟨z, hzD, hzB⟩ := IsConcreteLE.exists_of_lt hlt
      have hv0 : ∃ v0, v0 ∈ D ∧ v0 ∉ B ∧ (even n v0 = v0 ∨ even n v0 = 0) := by
        by_cases he : even n z ∈ B
        · refine ⟨z + even n z, D.add_mem hzD (hD z hzD), ?_, Or.inr ?_⟩
          · intro hmem
            apply hzB
            have h1 : z = (z + even n z) + even n z := by
              rw [add_assoc, fn_add_self, add_zero]
            rw [h1]
            exact B.add_mem hmem he
          · rw [even_add, even_even, fn_add_self]
        · exact ⟨even n z, hD z hzD, he, Or.inl (even_even n z)⟩
      obtain ⟨v0, hv0D, hv0B, hv0e⟩ := hv0
      have hv0span : v0 ∈ B ⊔ Submodule.span (ZMod 2) {v0} :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self v0)
      have hB'D : B ⊔ Submodule.span (ZMod 2) {v0} ≤ D := by
        refine sup_le hBD ?_
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hv0D
      have hB'even : ∀ w ∈ B ⊔ Submodule.span (ZMod 2) {v0},
          even n w ∈ B ⊔ Submodule.span (ZMod 2) {v0} := by
        intro w hw
        obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hc
        rw [even_add, even_smul]
        refine Submodule.add_mem _ (Submodule.mem_sup_left (hB b hb)) ?_
        refine Submodule.smul_mem _ _ ?_
        rcases hv0e with h1 | h1
        · rw [h1]
          exact hv0span
        · rw [h1]
          exact Submodule.zero_mem _
      have hlt' : B < B ⊔ Submodule.span (ZMod 2) {v0} := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro heq
        apply hv0B
        rw [heq]
        exact hv0span
      have hfr : Module.finrank (ZMod 2) B <
          Module.finrank (ZMod 2) (B ⊔ Submodule.span (ZMod 2) {v0} :
            Submodule (ZMod 2) (Fin n → ZMod 2)) :=
        Submodule.finrank_lt_finrank_of_lt hlt'
      obtain ⟨v', hv'e, hv'D, hv'span⟩ :=
        ih (B ⊔ Submodule.span (ZMod 2) {v0}) hB'D hB'even (by omega)
      refine ⟨fun j => Fin.cases v0 v' j, ?_, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa using hv0e
        · simpa using hv'e i
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa using hv0D
        · simpa using hv'D i
      · refine le_trans hv'span ?_
        refine sup_le (sup_le le_sup_left ?_) ?_
        · refine le_trans (Submodule.span_mono ?_) le_sup_right
          rintro _ rfl
          exact ⟨0, rfl⟩
        · refine le_trans (Submodule.span_mono ?_) le_sup_right
          rintro _ ⟨i, rfl⟩
          exact ⟨i.succ, rfl⟩

lemma h3_ix_shift (n : ℕ) (hn : 0 < n) (a s : ℕ) (hs : s ≤ n) :
    ix n hn ((ix n hn a).val + n - s) = ix n hn (a + (n - s)) := by
  have e : (ix n hn a).val + n - s = (ix n hn a).val + (n - s) := by omega
  rw [e, ix_val_add]

lemma h3_mix_apply (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w : Fin n → ZMod 2) (i : Fin n) :
    mix n hn w i = w (ix n hn (i.val + n - 3)) + w (ix n hn (i.val + n - 1)) +
      w (ix n hn (i.val + n - 5)) := by
  have h3 : 3 % n = 3 := Nat.mod_eq_of_lt (by omega)
  simp only [mix, rot, h3]
  rw [h3_ix_shift n hn _ 3 (by omega), h3_ix_shift n hn _ 3 (by omega)]
  have e1 : i.val + 2 + (n - 3) = i.val + n - 1 := by omega
  have e2 : i.val + n - 2 + (n - 3) = i.val + n - 5 + n := by omega
  rw [e1, e2, ix_add_n]

lemma h3_mix_ix (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w : Fin n → ZMod 2) (a : ℕ) :
    mix n hn w (ix n hn (a + 5)) = w (ix n hn (a + 2)) + w (ix n hn (a + 4)) +
      w (ix n hn a) := by
  rw [h3_mix_apply n hn h6n, h3_ix_shift n hn _ 3 (by omega), h3_ix_shift n hn _ 1 (by omega),
    h3_ix_shift n hn _ 5 (by omega)]
  have e1 : a + 5 + (n - 3) = a + 2 + n := by omega
  have e2 : a + 5 + (n - 1) = a + 4 + n := by omega
  have e3 : a + 5 + (n - 5) = a + n := by omega
  rw [e1, e2, e3, ix_add_n, ix_add_n, ix_add_n]

lemma h3_z2_mid (x y z : ZMod 2) (h : x + y + z = 0) : y = x + z := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;>
    rcases z2_cases z with rfl | rfl <;> revert h <;> decide

lemma h3_ker_step (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w : Fin n → ZMod 2)
    (hw : mix n hn w = 0) (a : ℕ) :
    w (ix n hn (a + 4)) = w (ix n hn (a + 2)) + w (ix n hn a) := by
  have h := congrFun hw (ix n hn (a + 5))
  rw [h3_mix_ix n hn h6n] at h
  exact h3_z2_mid _ _ _ h

lemma h3_ker_agree (n : ℕ) (hn : 0 < n) (h6n : 6 ≤ n) (w w' : Fin n → ZMod 2)
    (hw : mix n hn w = 0) (hw' : mix n hn w' = 0)
    (h4 : ∀ a : ℕ, a < 4 → w (ix n hn a) = w' (ix n hn a)) :
    ∀ m : ℕ, w (ix n hn m) = w' (ix n hn m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 4
    · exact h4 m hm
    · obtain ⟨a, rfl⟩ : ∃ a, m = a + 4 := ⟨m - 4, by omega⟩
      rw [h3_ker_step n hn h6n w hw a, h3_ker_step n hn h6n w' hw' a,
        ih (a + 2) (by omega), ih a (by omega)]

lemma ker_mix_card (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Nat.card {w : Fin n → ZMod 2 // mix n hn w = 0} ≤ 16 := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  have hinj : Function.Injective
      (fun (w : {w : Fin n → ZMod 2 // mix n hn w = 0}) (a : Fin 4) => w.1 (ix n hn a.val)) := by
    intro w w' hww
    apply Subtype.ext
    funext i
    have h4 : ∀ a : ℕ, a < 4 → w.1 (ix n hn a) = w'.1 (ix n hn a) := by
      intro a ha
      exact congrFun hww ⟨a, ha⟩
    have := h3_ker_agree n hn h6n w.1 w'.1 w.2 w'.2 h4 i.val
    rwa [ix_self] at this
  have hc := Nat.card_le_card_of_injective _ hinj
  have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rwa [h16] at hc

def h3_b (j : Fin 4) (q : ℕ) : ZMod 2 :=
  if q % 2 = j.val / 2 ∧ (q / 2 % 3 = j.val % 2 ∨ q / 2 % 3 = 2) then (1 : ZMod 2) else 0

lemma h3_b_mod (j : Fin 4) (q : ℕ) : h3_b j (q % 6) = h3_b j q := by
  have e1 : q % 6 % 2 = q % 2 := by omega
  have e2 : q % 6 / 2 % 3 = q / 2 % 3 := by omega
  unfold h3_b
  rw [e1, e2]

lemma h3_b_congr (j : Fin 4) (p q : ℕ) (h : p % 6 = q % 6) : h3_b j p = h3_b j q := by
  rw [← h3_b_mod j p, ← h3_b_mod j q, h]

lemma h3_base_ix (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (j : Fin 4) (a : ℕ) :
    base n j (ix n hn a) = h3_b j a := by
  rw [base_apply, ix_val]
  exact h3_b_congr j (a % n) a (Nat.mod_mod_of_dvd a h6)

lemma h3_b_fin : ∀ (j : Fin 4) (r : Fin 6),
    h3_b j (r.val + 3) + h3_b j (r.val + 1) + h3_b j (r.val + 5) = 0 := by
  decide

lemma h3_b_sum (j : Fin 4) (a : ℕ) :
    h3_b j (a + 3) + h3_b j (a + 1) + h3_b j (a + 5) = 0 := by
  have h := h3_b_fin j ⟨a % 6, Nat.mod_lt _ (by norm_num)⟩
  rw [h3_b_congr j (a + 3) (a % 6 + 3) (by omega), h3_b_congr j (a + 1) (a % 6 + 1) (by omega),
    h3_b_congr j (a + 5) (a % 6 + 5) (by omega)]
  exact h

def h3_shift (n : ℕ) (hn : 0 < n) (s : ℕ) (hs : s ≤ n) : Fin n ≃ Fin n where
  toFun i := ix n hn (i.val + s)
  invFun i := ix n hn (i.val + n - s)
  left_inv i := by
    show ix n hn ((ix n hn (i.val + s)).val + n - s) = i
    rw [h3_ix_shift n hn _ s hs]
    have e : i.val + s + (n - s) = i.val + n := by omega
    rw [e, ix_add_n, ix_self]
  right_inv i := by
    show ix n hn ((ix n hn (i.val + n - s)).val + s) = i
    rw [ix_val_add]
    have e : i.val + n - s + s = i.val + n := by omega
    rw [e, ix_add_n, ix_self]

lemma h3_sum_shift (n : ℕ) (hn : 0 < n) (s : ℕ) (hs : s ≤ n) (f g : Fin n → ZMod 2) :
    ∑ i, f i * g (ix n hn (i.val + n - s)) = ∑ i, f (ix n hn (i.val + s)) * g i := by
  rw [← Equiv.sum_comp (h3_shift n hn s hs) (fun i => f i * g (ix n hn (i.val + n - s)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e : ix n hn (((h3_shift n hn s hs) i).val + n - s) = i :=
    (h3_shift n hn s hs).left_inv i
  rw [e]
  rfl

lemma base_dot_mix (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (j : Fin 4) (w : Fin n → ZMod 2) :
    dot n (base n j) (mix n hn w) = 0 := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  unfold dot
  have e1 : ∀ i : Fin n, base n j i * mix n hn w i =
      base n j i * w (ix n hn (i.val + n - 3)) + base n j i * w (ix n hn (i.val + n - 1)) +
        base n j i * w (ix n hn (i.val + n - 5)) := by
    intro i
    rw [h3_mix_apply n hn h6n]
    ring
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    h3_sum_shift n hn 3 (by omega), h3_sum_shift n hn 1 (by omega),
    h3_sum_shift n hn 5 (by omega), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [h3_base_ix n hn h6, h3_base_ix n hn h6, h3_base_ix n hn h6, ← add_mul, ← add_mul,
    h3_b_sum, zero_mul]

lemma even_base (n : ℕ) (j : Fin 4) :
    even n (base n j) = base n j ∨ even n (base n j) = 0 := by
  by_cases hj : j.val / 2 = 0
  · left
    funext i
    rw [even_apply, base_apply]
    split_ifs with h1 h2 h2
    · rfl
    · rfl
    · exfalso
      omega
    · rfl
  · right
    funext i
    rw [even_apply, base_apply, Pi.zero_apply]
    split_ifs with h1 h2
    · exfalso
      omega
    · rfl
    · rfl

lemma h3_base_li (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    LinearIndependent (ZMod 2) (base n) := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ i : Fin n, g 0 * base n 0 i + g 1 * base n 1 i + g 2 * base n 2 i +
      g 3 * base n 3 i = 0 := by
    intro i
    have := congrFun hg i
    simpa [Fin.sum_univ_four] using this
  have h0 := key ⟨0, by omega⟩
  have h1 := key ⟨2, by omega⟩
  have h2 := key ⟨1, by omega⟩
  have h3 := key ⟨3, by omega⟩
  simp [base_apply] at h0 h1 h2 h3
  intro i
  fin_cases i <;> assumption

lemma base_span_finrank (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    4 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (base n))) := by
  rw [finrank_span_eq_card (h3_base_li n hn h6)]
  simp

lemma h3_span_le_orth (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Submodule.span (ZMod 2) (Set.range (base n)) ≤ orth n (mixL n hn) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, mem_orth]
  intro u
  exact base_dot_mix n hn h6 j u

lemma h3_orth_card_le (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Nat.card (orth n (mixL n hn)) ≤ 16 := by
  have h := orth_card n (mixL n hn)
  have hW : Nat.card (Fin n → ZMod 2) = 2 ^ n := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hk : Nat.card {u : Fin n → ZMod 2 // (mixL n hn) u = 0} ≤ 16 := ker_mix_card n hn h6
  rw [hW] at h
  have h2 : Nat.card (orth n (mixL n hn)) = Nat.card {u : Fin n → ZMod 2 // (mixL n hn) u = 0} :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (by positivity)) h
  rw [h2]
  exact hk

lemma h3_orth_eq_span (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Submodule.span (ZMod 2) (Set.range (base n)) = orth n (mixL n hn) := by
  refine Submodule.eq_of_le_of_finrank_le (h3_span_le_orth n hn h6) ?_
  refine le_trans ?_ (base_span_finrank n hn h6)
  have hc := h3_orth_card_le n hn h6
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hc

lemma mix_surj (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (x : Fin n → ZMod 2)
    (hx : ∀ j, dot n (base n j) x = 0) : ∃ w, mix n hn w = x := by
  have hB : Submodule.span (ZMod 2) (Set.range (base n)) ≤ LinearMap.ker (dotL n x) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, dotL_apply]
    exact hx j
  have hR : x ∈ LinearMap.range (mixL n hn) := by
    refine double_orth n _ x (fun z hz => ?_)
    have hzO : z ∈ orth n (mixL n hn) := by
      rw [mem_orth]
      intro u
      exact hz _ (LinearMap.mem_range_self _ u)
    rw [← h3_orth_eq_span n hn h6] at hzO
    have := hB hzO
    rwa [LinearMap.mem_ker, dotL_apply] at this
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hR
  exact ⟨w, hw⟩

def h4_bit (x : ZMod 2) : ℕ := if x = 0 then 0 else 1

lemma h4_bit_le (x : ZMod 2) : h4_bit x ≤ 1 := by
  unfold h4_bit
  split_ifs <;> omega

lemma h4_bit_eq_iff (x y : ZMod 2) : h4_bit x = h4_bit y ↔ x - y = 0 := by
  revert x y
  decide

lemma h4_run_succ (n h : ℕ) (ask : Fin (h+1) → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w : Fin n → ZMod 2) :
    run n (h+1) ask w = 2 * run n h (fun j => ask j.castSucc) w +
      h4_bit (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w) w) := by
  unfold run h4_bit
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  congr

lemma run_eq_iff (n h : ℕ) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w0 : Fin n → ZMod 2) :
    ∃ p : Fin h → ℕ, ∀ w, run n h ask w = run n h ask w0 ↔ ∀ j, ask j (p j) (w - w0) = 0 := by
  induction h with
  | zero =>
    refine ⟨fun _ => 0, fun w => ?_⟩
    constructor
    · intro _ j
      exact j.elim0
    · intro _
      rfl
  | succ h ih =>
    obtain ⟨p', hp'⟩ := ih (fun j => ask j.castSucc)
    refine ⟨@Fin.snoc h (fun _ => ℕ) p' (run n h (fun j => ask j.castSucc) w0), fun w => ?_⟩
    rw [h4_run_succ, h4_run_succ, Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← hp' w]
    have hb1 := h4_bit_le (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w) w)
    have hb2 := h4_bit_le (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w0) w0)
    constructor
    · intro he
      have h1 : run n h (fun j => ask j.castSucc) w = run n h (fun j => ask j.castSucc) w0 := by
        omega
      refine ⟨h1, ?_⟩
      rw [h1] at he
      have h2 : h4_bit (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w0) w) =
          h4_bit (ask (Fin.last h) (run n h (fun j => ask j.castSucc) w0) w0) := by
        omega
      rw [h4_bit_eq_iff, ← map_sub] at h2
      exact h2
    · rintro ⟨h1, h2⟩
      rw [h1]
      congr 1
      rw [h4_bit_eq_iff, ← map_sub]
      exact h2

lemma cell_structure (n h : ℕ) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w0 : Fin n → ZMod 2) :
    ∃ K : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ w, run n h ask w = run n h ask w0 ↔ w - w0 ∈ K) ∧ 2^n ≤ Nat.card K * 2^h := by
  obtain ⟨p, hp⟩ := run_eq_iff n h ask w0
  refine ⟨LinearMap.ker (LinearMap.pi (fun j => ask j (p j))), fun w => ?_, ?_⟩
  · rw [hp w, LinearMap.mem_ker]
    constructor
    · intro hj
      funext j
      exact hj j
    · intro hj j
      exact congrFun hj j
  · have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi (fun j => ask j (p j)))
    have h2 : Module.finrank (ZMod 2)
        (LinearMap.range (LinearMap.pi (fun j => ask j (p j)))) ≤ h := by
      have h3 := Submodule.finrank_le (LinearMap.range (LinearMap.pi (fun j => ask j (p j))))
      rwa [Module.finrank_fin_fun] at h3
    rw [Module.finrank_fin_fun] at h1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

def h5_m0 (n : ℕ) (hn : 0 < n) (name : Fin n → ZMod 2) (j : Fin n) : ZMod 2 :=
  name j + name (ix n hn (j.val+2)) + name (ix n hn (j.val+n-2))

def h5_L (n : ℕ) (hn : 0 < n) (name : Fin n → ZMod 2) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  { toFun := fun w i => mix n hn w i + mix n hn w (ix n hn (i.val+2))
      + h5_m0 n hn name (ix n hn (i.val+1)) * mix n hn w (ix n hn (i.val+2))
      + h5_m0 n hn name (ix n hn (i.val+2)) * mix n hn w (ix n hn (i.val+1))
      + rot n hn 4 w i
    map_add' := fun w w' => by
      funext i
      simp only [mix_add, Pi.add_apply, rot]
      ring
    map_smul' := fun a w => by
      funext i
      simp only [mix_smul, Pi.smul_apply, smul_eq_mul, rot, RingHom.id_apply]
      ring }

lemma out_affine (n : ℕ) (hn : 0 < n) (name c : Fin n → ZMod 2) :
    ∃ (L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (c0 : Fin n → ZMod 2),
      ∀ (w : Fin n → ZMod 2) (i : Fin n), out n hn name c w i =
        mix n hn w (ix n hn (i.val+1)) * mix n hn w (ix n hn (i.val+2)) + (L w + c0) i := by
  refine ⟨h5_L n hn name, fun i => h5_m0 n hn name i + h5_m0 n hn name (ix n hn (i.val+2))
    + h5_m0 n hn name (ix n hn (i.val+1)) * h5_m0 n hn name (ix n hn (i.val+2)) + c i,
    fun w i => ?_⟩
  simp only [out, h5_L, h5_m0, mix, rot, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  ring

noncomputable def h5_KZ (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  K ⊓ Submodule.comap (mixL n hn) (LinearMap.ker (evenL n))

lemma h5_mem_KZ (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (x : Fin n → ZMod 2) : x ∈ h5_KZ n hn K ↔ x ∈ K ∧ even n (mix n hn x) = 0 := by
  unfold h5_KZ
  rw [Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker, mixL_apply, evenL_apply]

lemma h5_odd_KZ (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (κ : ↥(h5_KZ n hn K)) : even n (mix n hn (κ : Fin n → ZMod 2)) = 0 :=
  ((h5_mem_KZ n hn K _).1 κ.2).2

noncomputable def h5_tau (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (↥K × ↥(h5_KZ n hn K)) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  ((evenL n).comp ((mixL n hn).comp K.subtype)).coprod
    ((mixL n hn).comp (h5_KZ n hn K).subtype)

lemma h5_tau_apply (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (u : ↥K × ↥(h5_KZ n hn K)) :
    h5_tau n hn K u =
      even n (mix n hn (u.1 : Fin n → ZMod 2)) + mix n hn (u.2 : Fin n → ZMod 2) := rfl

lemma h5_base_mem (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (j : Fin 4) :
    base n j ∈ orth n (h5_tau n hn K) := by
  rw [mem_orth]
  intro u
  rw [h5_tau_apply, dot_add_right, base_dot_mix n hn h6, add_zero, ← dot_even]
  rcases even_base n j with h | h
  · rw [h, base_dot_mix n hn h6]
  · rw [h, dot_zero_left]

lemma h5_even_mem (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (z : Fin n → ZMod 2) (hz : z ∈ orth n (h5_tau n hn K)) :
    even n z ∈ orth n (h5_tau n hn K) := by
  rw [mem_orth] at hz ⊢
  intro u
  have h := hz (u.1, 0)
  rw [h5_tau_apply] at h
  simp only [ZeroMemClass.coe_zero, mix_zero, add_zero] at h
  rw [h5_tau_apply, dot_even, even_add, even_even, h5_odd_KZ, add_zero]
  exact h

lemma h5_tau_zero (n : ℕ) (hn : 0 < n) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (u : ↥K × ↥(h5_KZ n hn K)) (h : h5_tau n hn K u = 0) :
    even n (mix n hn (u.1 : Fin n → ZMod 2)) = 0 ∧ mix n hn (u.2 : Fin n → ZMod 2) = 0 := by
  rw [h5_tau_apply] at h
  have h1 := congrArg (even n) h
  rw [even_add, even_even, h5_odd_KZ, add_zero, even_zero] at h1
  rw [h1, zero_add] at h
  exact ⟨h1, h⟩

lemma h5_card_ker (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card {u : ↥K × ↥(h5_KZ n hn K) // h5_tau n hn K u = 0} ≤
      Nat.card (h5_KZ n hn K) * 16 := by
  have h3 : Nat.card {u : ↥K × ↥(h5_KZ n hn K) // h5_tau n hn K u = 0} ≤
      Nat.card (↥(h5_KZ n hn K) × {w : Fin n → ZMod 2 // mix n hn w = 0}) := by
    refine Nat.card_le_card_of_injective (fun u =>
      (⟨(u.1.1 : Fin n → ZMod 2),
        (h5_mem_KZ n hn K _).2 ⟨u.1.1.2, (h5_tau_zero n hn K u.1 u.2).1⟩⟩,
       ⟨(u.1.2 : Fin n → ZMod 2), (h5_tau_zero n hn K u.1 u.2).2⟩)) ?_
    intro u v huv
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at huv
    exact Subtype.ext (Prod.ext (Subtype.ext huv.1) (Subtype.ext huv.2))
  rw [Nat.card_prod] at h3
  exact le_trans h3 (Nat.mul_le_mul_left _ (ker_mix_card n hn h6))

lemma h5_card_D (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card (orth n (h5_tau n hn K)) * Nat.card K ≤ 2^n * 16 := by
  have h1 := orth_card n (h5_tau n hn K)
  rw [Nat.card_prod] at h1
  have h2 := h5_card_ker n hn h6 K
  have hpos : 0 < Nat.card (h5_KZ n hn K) := Nat.card_pos
  have h4 : Nat.card (h5_KZ n hn K) * (Nat.card (orth n (h5_tau n hn K)) * Nat.card K) ≤
      Nat.card (h5_KZ n hn K) * (2^n * 16) := by
    calc Nat.card (h5_KZ n hn K) * (Nat.card (orth n (h5_tau n hn K)) * Nat.card K)
        = Nat.card K * Nat.card (h5_KZ n hn K) * Nat.card (orth n (h5_tau n hn K)) := by ring
      _ = 2^n * Nat.card {u : ↥K × ↥(h5_KZ n hn K) // h5_tau n hn K u = 0} := h1
      _ ≤ 2^n * (Nat.card (h5_KZ n hn K) * 16) := Nat.mul_le_mul_left _ h2
      _ = Nat.card (h5_KZ n hn K) * (2^n * 16) := by ring
  exact Nat.le_of_mul_le_mul_left h4 hpos

def h5_P (n : ℕ) (hn : 0 < n) (i : Fin n) (x : Fin n → ZMod 2) : ZMod 2 :=
  x (ix n hn (i.val+1)) * x (ix n hn (i.val+2))

def h5_g (n : ℕ) (hn : 0 < n) (i : Fin n) (x x' : Fin n → ZMod 2) : ZMod 2 :=
  x (ix n hn (i.val+1)) * x' (ix n hn (i.val+2)) + x' (ix n hn (i.val+1)) * x (ix n hn (i.val+2))

lemma h5_par (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) :
    ((ix n hn (i.val+1)).val % 2 = 0 ∧ (ix n hn (i.val+2)).val % 2 = 1) ∨
    ((ix n hn (i.val+1)).val % 2 = 1 ∧ (ix n hn (i.val+2)).val % 2 = 0) := by
  rw [ix_val, ix_val, Nat.mod_mod_of_dvd _ h2, Nat.mod_mod_of_dvd _ h2]
  omega

lemma h5_odd (n : ℕ) (x : Fin n → ZMod 2) (h : even n x = 0) (j : Fin n)
    (hj : j.val % 2 = 0) : x j = 0 := by
  have h1 := congrFun h j
  rw [even_apply] at h1
  split_ifs at h1
  exact h1

lemma h5_evn1 (n : ℕ) (x : Fin n → ZMod 2) (j : Fin n) (hj : j.val % 2 = 1) :
    even n x j = 0 := by
  rw [even_apply]
  split_ifs with h
  · omega
  · rfl

lemma h5_evn0 (n : ℕ) (x : Fin n → ZMod 2) (j : Fin n) (hj : j.val % 2 = 0) :
    even n x j = x j := by
  rw [even_apply]
  split_ifs
  rfl

lemma h5_P_add (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) (x x' : Fin n → ZMod 2)
    (h : even n x' = 0) : h5_P n hn i (x + x') = h5_P n hn i x + h5_g n hn i x x' := by
  unfold h5_P h5_g
  simp only [Pi.add_apply]
  rcases h5_par n hn h2 i with ⟨ha, -⟩ | ⟨-, hb⟩
  · rw [h5_odd n x' h _ ha]
    ring
  · rw [h5_odd n x' h _ hb]
    ring

lemma h5_g_odd (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) (x x' : Fin n → ZMod 2)
    (h : even n x = 0) (h' : even n x' = 0) : h5_g n hn i x x' = 0 := by
  unfold h5_g
  rcases h5_par n hn h2 i with ⟨ha, -⟩ | ⟨-, hb⟩
  · rw [h5_odd n x h _ ha, h5_odd n x' h' _ ha]
    ring
  · rw [h5_odd n x h _ hb, h5_odd n x' h' _ hb]
    ring

lemma h5_g_add (n : ℕ) (hn : 0 < n) (i : Fin n) (x y x' : Fin n → ZMod 2) :
    h5_g n hn i (x + y) x' = h5_g n hn i x x' + h5_g n hn i y x' := by
  unfold h5_g
  simp only [Pi.add_apply]
  ring

lemma h5_P_even (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (i : Fin n) (x x' : Fin n → ZMod 2)
    (h : even n x' = 0) : h5_P n hn i (even n x + x') = h5_g n hn i x x' := by
  unfold h5_P h5_g
  simp only [Pi.add_apply]
  rcases h5_par n hn h2 i with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [h5_odd n x' h _ ha, h5_evn0 n x _ ha, h5_evn1 n x _ hb]
    ring
  · rw [h5_odd n x' h _ hb, h5_evn1 n x _ ha, h5_evn0 n x _ hb]
    ring

lemma h5_fib (α β γ : Type) [Finite α] [Finite β] [Finite γ] (S : α → β → Prop)
    (T : α → γ → Prop) (h : ∀ a, Nat.card {b // S a b} ≤ Nat.card {c // T a c}) :
    Nat.card {p : α × β // S p.1 p.2} ≤ Nat.card {p : α × γ // T p.1 p.2} := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype S),
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype T), Nat.card_sigma, Nat.card_sigma]
  exact Finset.sum_le_sum (fun a _ => h a)

lemma h5_fib2 (α β γ : Type) [Finite α] [Finite β] [Finite γ] (S : β → α → Prop)
    (T : γ → α → Prop) (h : ∀ a, Nat.card {b // S b a} ≤ Nat.card {c // T c a}) :
    Nat.card {p : β × α // S p.1 p.2} ≤ Nat.card {p : γ × α // T p.1 p.2} := by
  have h1 := h5_fib α β γ (fun a b => S b a) (fun a c => T c a) h
  have e1 : Nat.card {p : β × α // S p.1 p.2} = Nat.card {p : α × β // S p.2 p.1} :=
    Nat.card_congr ((Equiv.prodComm β α).subtypeEquiv (fun p => Iff.rfl))
  have e2 : Nat.card {p : γ × α // T p.1 p.2} = Nat.card {p : α × γ // T p.2 p.1} :=
    Nat.card_congr ((Equiv.prodComm γ α).subtypeEquiv (fun p => Iff.rfl))
  rw [e1, e2]
  exact h1

def h5_G (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (Y0 e : Fin n → ZMod 2) (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (k : ↥K) : Prop :=
  ∀ i, mark i = true →
    h5_P n hn i (Y0 + mix n hn (k : Fin n → ZMod 2)) = (N (k : Fin n → ZMod 2) + e) i

def h5_T1 (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (Y0 : Fin n → ZMod 2) (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : ↥K)
    (κ : ↥(h5_KZ n hn K)) : Prop :=
  ∀ i, mark i = true →
    h5_g n hn i (Y0 + mix n hn (k : Fin n → ZMod 2)) (mix n hn (κ : Fin n → ZMod 2)) =
      N (κ : Fin n → ZMod 2) i

def h5_T0 (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (k : ↥K) (κ : ↥(h5_KZ n hn K)) : Prop :=
  ∀ i, mark i = true →
    h5_g n hn i (mix n hn (k : Fin n → ZMod 2)) (mix n hn (κ : Fin n → ZMod 2)) = 0

lemma h5_step1_key (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k g0 g : ↥K)
    (hg0 : h5_G n hn mark K Y0 e N g0)
    (hm0 : (g0 : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K)
    (hg : h5_G n hn mark K Y0 e N g)
    (hd : (g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2) ∈ h5_KZ n hn K) :
    h5_T1 n hn mark K Y0 N k ⟨(g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2), hd⟩ := by
  intro i hi
  have o1 : even n (mix n hn ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2))) = 0 :=
    ((h5_mem_KZ n hn K _).1 hd).2
  have o2 : even n (mix n hn ((g0 : Fin n → ZMod 2) - (k : Fin n → ZMod 2))) = 0 :=
    ((h5_mem_KZ n hn K _).1 hm0).2
  have e1 : Y0 + mix n hn (g : Fin n → ZMod 2) = (Y0 + mix n hn (g0 : Fin n → ZMod 2)) +
      mix n hn ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2)) := by
    rw [mix_sub]
    abel
  have e2 : Y0 + mix n hn (g0 : Fin n → ZMod 2) = (Y0 + mix n hn (k : Fin n → ZMod 2)) +
      mix n hn ((g0 : Fin n → ZMod 2) - (k : Fin n → ZMod 2)) := by
    rw [mix_sub]
    abel
  have h1 := hg i hi
  rw [e1, h5_P_add n hn h2 i _ _ o1, hg0 i hi, e2, h5_g_add,
    h5_g_odd n hn h2 i _ _ o2 o1, add_zero] at h1
  show h5_g n hn i (Y0 + mix n hn (k : Fin n → ZMod 2))
    (mix n hn ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2))) =
    N ((g : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2)) i
  rw [map_sub, Pi.sub_apply]
  simp only [Pi.add_apply] at h1
  linear_combination h1

lemma h5_step1_fib (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (k : ↥K) :
    Nat.card {g : ↥K // h5_G n hn mark K Y0 e N g ∧
      (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K} ≤
    Nat.card {κ : ↥(h5_KZ n hn K) // h5_T1 n hn mark K Y0 N k κ} := by
  rcases isEmpty_or_nonempty {g : ↥K // h5_G n hn mark K Y0 e N g ∧
      (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K} with hE | ⟨⟨g0, hg0, hm0⟩⟩
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  · have hd : ∀ g : {g : ↥K // h5_G n hn mark K Y0 e N g ∧
        (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K},
        (g.1 : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2) ∈ h5_KZ n hn K := by
      intro g
      have h := (h5_KZ n hn K).sub_mem g.2.2 hm0
      rw [sub_sub_sub_cancel_right] at h
      exact h
    refine Nat.card_le_card_of_injective (fun g =>
      ⟨⟨(g.1 : Fin n → ZMod 2) - (g0 : Fin n → ZMod 2), hd g⟩,
        h5_step1_key n hn h2 mark K Y0 e N k g0 g.1 hg0 hm0 g.2.1 (hd g)⟩) ?_
    intro g g' hgg
    simp only [Subtype.mk.injEq, sub_left_inj] at hgg
    exact Subtype.ext (Subtype.ext hgg)

lemma h5_step2_fib (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (κ : ↥(h5_KZ n hn K)) :
    Nat.card {k : ↥K // h5_T1 n hn mark K Y0 N k κ} ≤
    Nat.card {k : ↥K // h5_T0 n hn mark K k κ} := by
  rcases isEmpty_or_nonempty {k : ↥K // h5_T1 n hn mark K Y0 N k κ} with hE | ⟨⟨k0, hk0⟩⟩
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  · refine Nat.card_le_card_of_injective (fun k => ⟨k.1 - k0, ?_⟩) ?_
    · intro i hi
      have e1 : Y0 + mix n hn (k.1 : Fin n → ZMod 2) = (Y0 + mix n hn (k0 : Fin n → ZMod 2)) +
          mix n hn ((k.1 - k0 : ↥K) : Fin n → ZMod 2) := by
        rw [Submodule.coe_sub, mix_sub]
        abel
      have h1 := k.2 i hi
      rw [e1, h5_g_add, hk0 i hi] at h1
      exact add_left_cancel (h1.trans (add_zero _).symm)
    · intro k k' hkk
      exact Subtype.ext (sub_left_inj.mp (congrArg Subtype.val hkk))

lemma h5_step1 (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card (h5_KZ n hn K) * Nat.card {k : ↥K // h5_G n hn mark K Y0 e N k} ≤
    Nat.card {p : ↥K × ↥(h5_KZ n hn K) // h5_T1 n hn mark K Y0 N p.1 p.2} := by
  have h1 : Nat.card (↥(h5_KZ n hn K) × {k : ↥K // h5_G n hn mark K Y0 e N k}) ≤
      Nat.card {p : ↥K × ↥K // h5_G n hn mark K Y0 e N p.2 ∧
        (p.2 : Fin n → ZMod 2) - (p.1 : Fin n → ZMod 2) ∈ h5_KZ n hn K} := by
    refine Nat.card_le_card_of_injective (fun q =>
      ⟨(⟨(q.2.1 : Fin n → ZMod 2) - (q.1 : Fin n → ZMod 2),
        K.sub_mem q.2.1.2 ((h5_mem_KZ n hn K _).1 q.1.2).1⟩, q.2.1), ⟨q.2.2, ?_⟩⟩) ?_
    · show (q.2.1 : Fin n → ZMod 2) - ((q.2.1 : Fin n → ZMod 2) - (q.1 : Fin n → ZMod 2)) ∈
        h5_KZ n hn K
      rw [sub_sub_cancel]
      exact q.1.2
    · intro q q' hqq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at hqq
      have h3 : q.2 = q'.2 := Subtype.ext hqq.2
      have h4 := hqq.1
      rw [hqq.2] at h4
      exact Prod.ext (Subtype.ext (sub_right_injective h4)) h3
  rw [Nat.card_prod] at h1
  exact le_trans h1 (h5_fib ↥K ↥K ↥(h5_KZ n hn K)
    (fun k g => h5_G n hn mark K Y0 e N g ∧
      (g : Fin n → ZMod 2) - (k : Fin n → ZMod 2) ∈ h5_KZ n hn K)
    (fun k κ => h5_T1 n hn mark K Y0 N k κ)
    (fun k => h5_step1_fib n hn h2 mark K Y0 e N k))

lemma h5_step3 (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card {p : ↥K × ↥(h5_KZ n hn K) // h5_T0 n hn mark K p.1 p.2} =
    Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun u => ?_))
  constructor
  · intro h i hi
    rw [h5_tau_apply]
    exact (h5_P_even n hn h2 i _ _ (h5_odd_KZ n hn K u.2)).trans (h i hi)
  · intro h i hi
    have h1 := h i hi
    rw [h5_tau_apply] at h1
    exact (h5_P_even n hn h2 i _ _ (h5_odd_KZ n hn K u.2)).symm.trans h1

lemma h5_pairs (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (mark : Fin n → Bool)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (Y0 e : Fin n → ZMod 2)
    (N : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Nat.card (h5_KZ n hn K) * Nat.card {k : ↥K // h5_G n hn mark K Y0 e N k} ≤
    Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} := by
  rw [← h5_step3 n hn h2 mark K]
  exact le_trans (h5_step1 n hn h2 mark K Y0 e N)
    (h5_fib2 ↥(h5_KZ n hn K) ↥K ↥K (fun k κ => h5_T1 n hn mark K Y0 N k κ)
      (fun k κ => h5_T0 n hn mark K k κ) (fun κ => h5_step2_fib n hn mark K Y0 N κ))

lemma h5_move : ∀ X s t : ZMod 2, X + s = t ↔ X = s + t := by
  decide

lemma h5_good (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (name c : Fin n → ZMod 2)
    (K : Submodule (ZMod 2) (Fin n → ZMod 2)) (w0 : Fin n → ZMod 2)
    (A L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b c0 : Fin n → ZMod 2)
    (hL : ∀ (w : Fin n → ZMod 2) (i : Fin n), out n hn name c w i =
        mix n hn w (ix n hn (i.val+1)) * mix n hn w (ix n hn (i.val+2)) + (L w + c0) i) :
    Nat.card {k : K // ∀ i, mark i = true →
        out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
          (A (w0 + (k : Fin n → ZMod 2)) + b) i} =
    Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun k =>
    forall_congr' (fun i => imp_congr_right (fun _ => ?_))))
  have e : (L (w0 + (k : Fin n → ZMod 2)) + c0) i + (A (w0 + (k : Fin n → ZMod 2)) + b) i =
      ((L + A) (k : Fin n → ZMod 2) + (L w0 + c0 + A w0 + b)) i := by
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    ring
  rw [hL, mix_add, h5_move, e]
  exact Iff.rfl

lemma cell_count (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (w0 : Fin n → ZMod 2) (A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : Fin n → ZMod 2) :
    ∃ D : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ j, base n j ∈ D) ∧ (∀ z ∈ D, even n z ∈ D) ∧
      Nat.card D * Nat.card K ≤ 2^n * 16 ∧
      (2:ℤ)^n * (Nat.card {k : K // ∀ i, mark i = true →
        out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
          (A (w0 + (k : Fin n → ZMod 2)) + b) i} : ℤ) ≤
      (Nat.card K : ℤ) * Ssum n hn mark D := by
  obtain ⟨L, c0, hL⟩ := out_affine n hn name c
  have h2 : 2 ∣ n := Dvd.dvd.trans (by norm_num) h6
  refine ⟨orth n (h5_tau n hn K), h5_base_mem n hn h6 K, h5_even_mem n hn K,
    h5_card_D n hn h6 K, ?_⟩
  have hp := h5_pairs n hn h2 mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A)
  have hf := fourier_count n hn mark (h5_tau n hn K)
  rw [Nat.card_prod] at hf
  rw [h5_good n hn mark name c K w0 A L b c0 hL]
  have hpos : (0:ℤ) < (Nat.card (h5_KZ n hn K) : ℤ) := Nat.cast_pos.mpr Nat.card_pos
  have hp' : (Nat.card (h5_KZ n hn K) : ℤ) *
      (Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ)
      ≤ (Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} : ℤ) := by
    exact_mod_cast hp
  have h3 : (Nat.card (h5_KZ n hn K) : ℤ) * ((2:ℤ)^n *
      (Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ))
      ≤ (Nat.card (h5_KZ n hn K) : ℤ) *
        ((Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K))) := by
    calc (Nat.card (h5_KZ n hn K) : ℤ) * ((2:ℤ)^n * (Nat.card {k : ↥K //
          h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ))
        = (2:ℤ)^n * ((Nat.card (h5_KZ n hn K) : ℤ) * (Nat.card {k : ↥K //
          h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ)) := by ring
      _ ≤ (2:ℤ)^n *
          (Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} : ℤ) :=
        mul_le_mul_of_nonneg_left hp' (by positivity)
      _ = ((Nat.card K * Nat.card (h5_KZ n hn K) : ℕ) : ℤ) *
          Ssum n hn mark (orth n (h5_tau n hn K)) := hf
      _ = (Nat.card (h5_KZ n hn K) : ℤ) *
          ((Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K))) := by
        push_cast
        ring
  exact le_of_mul_le_mul_left h3 hpos

lemma h6_cell (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (h : ℕ) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2))
    (w0 : Fin n → ZMod 2) :
    ∃ D : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ j, base n j ∈ D) ∧ (∀ z ∈ D, even n z ∈ D) ∧
      Module.finrank (ZMod 2) D ≤ h+4 ∧
      (2:ℤ)^n * (Nat.card {w : Fin n → ZMod 2 // (∀ i, mark i = true →
        out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i) ∧
          run n h ask w = run n h ask w0} : ℤ) ≤
      (Nat.card {w : Fin n → ZMod 2 // run n h ask w = run n h ask w0} : ℤ) *
        Ssum n hn mark D := by
  obtain ⟨K, hK, hKc⟩ := cell_structure n h ask w0
  obtain ⟨D, hb, he, hDK, hcount⟩ :=
    cell_count n hn h6 mark name c K w0 (A (run n h ask w0)) (b (run n h ask w0))
  refine ⟨D, hb, he, ?_, ?_⟩
  · have h1 : Nat.card D * 2^n ≤ 2^(h+4) * 2^n := by
      calc Nat.card D * 2^n ≤ Nat.card D * (Nat.card K * 2^h) := Nat.mul_le_mul_left _ hKc
        _ = Nat.card D * Nat.card K * 2^h := by ring
        _ ≤ 2^n * 16 * 2^h := Nat.mul_le_mul_right _ hDK
        _ = 2^(h+4) * 2^n := by ring
    have h2 : Nat.card D ≤ 2^(h+4) := Nat.le_of_mul_le_mul_right h1 (by positivity)
    have h3 : Nat.card D = 2 ^ Module.finrank (ZMod 2) D := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
      simp
    rw [h3] at h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  · have hrun : ∀ k : K, run n h ask (w0 + (k : Fin n → ZMod 2)) = run n h ask w0 := by
      intro k
      rw [hK, add_sub_cancel_left]
      exact k.2
    have e2 : Nat.card K = Nat.card {w : Fin n → ZMod 2 // run n h ask w = run n h ask w0} :=
      Nat.card_congr
        { toFun := fun k => ⟨w0 + (k : Fin n → ZMod 2), hrun k⟩
          invFun := fun w => ⟨w.1 - w0, (hK _).mp w.2⟩
          left_inv := fun k => Subtype.ext (add_sub_cancel_left _ _)
          right_inv := fun w => Subtype.ext (add_sub_cancel _ _) }
    have e1 : Nat.card {k : K // ∀ i, mark i = true →
        out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
          (A (run n h ask w0) (w0 + (k : Fin n → ZMod 2)) + b (run n h ask w0)) i} =
        Nat.card {w : Fin n → ZMod 2 // (∀ i, mark i = true →
          out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i) ∧
            run n h ask w = run n h ask w0} :=
      Nat.card_congr
        { toFun := fun k => ⟨w0 + (k.1 : Fin n → ZMod 2), by
            refine ⟨?_, hrun k.1⟩
            rw [hrun k.1]
            exact k.2⟩
          invFun := fun w => ⟨⟨w.1 - w0, (hK _).mp w.2.2⟩, by
            have hw := w.2.1
            rw [w.2.2] at hw
            have hc : w0 + (w.1 - w0) = w.1 := add_sub_cancel _ _
            show ∀ i, mark i = true → out n hn name c (w0 + (w.1 - w0)) i =
              (A (run n h ask w0) (w0 + (w.1 - w0)) + b (run n h ask w0)) i
            rw [hc]
            exact hw⟩
          left_inv := fun k => Subtype.ext (Subtype.ext (add_sub_cancel_left _ _))
          right_inv := fun w => Subtype.ext (add_sub_cancel _ _) }
    rw [← e1, ← e2]
    exact hcount

lemma h6_card_filter {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    Nat.card {a : α // P a} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma h6_fiber_sum {α : Type} [Fintype α] [Nonempty α] (f : α → ℕ) (P : α → Prop)
    (hcell : ∀ a0, (Nat.card α : ℤ) * (Nat.card {a : α // P a ∧ f a = f a0} : ℤ) ≤
      (Nat.card {a : α // f a = f a0} : ℤ) * ((Nat.card {a : α // P a} : ℤ) - 1)) : False := by
  classical
  have hG : Nat.card {a : α // P a} =
      ∑ p ∈ Finset.univ.image f, Nat.card {a : α // P a ∧ f a = p} := by
    rw [h6_card_filter, Finset.card_eq_sum_card_fiberwise
      (f := f) (t := Finset.univ.image f) (fun a _ => Finset.mem_coe.mpr
        (Finset.mem_image_of_mem f (Finset.mem_univ a)))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [h6_card_filter, Finset.filter_filter]
  have hC : Nat.card α = ∑ p ∈ Finset.univ.image f, Nat.card {a : α // f a = p} := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := f) (t := Finset.univ.image f) (fun a _ => Finset.mem_coe.mpr
        (Finset.mem_image_of_mem f (Finset.mem_univ a)))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [h6_card_filter]
  have hsum : ∑ p ∈ Finset.univ.image f,
      (Nat.card α : ℤ) * (Nat.card {a : α // P a ∧ f a = p} : ℤ) ≤
      ∑ p ∈ Finset.univ.image f,
        (Nat.card {a : α // f a = p} : ℤ) * ((Nat.card {a : α // P a} : ℤ) - 1) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp hp
    exact hcell a0
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hG' : (Nat.card {a : α // P a} : ℤ) =
      ∑ p ∈ Finset.univ.image f, (Nat.card {a : α // P a ∧ f a = p} : ℤ) := by
    exact_mod_cast hG
  have hC' : (Nat.card α : ℤ) =
      ∑ p ∈ Finset.univ.image f, (Nat.card {a : α // f a = p} : ℤ) := by
    exact_mod_cast hC
  rw [← hG', ← hC'] at hsum
  have hpos : (0:ℤ) < (Nat.card α : ℤ) := by
    exact_mod_cast Nat.card_pos
  nlinarith

lemma upper (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (h : ℕ) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)) :
    ∃ D : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ j, base n j ∈ D) ∧ (∀ z ∈ D, even n z ∈ D) ∧
      Module.finrank (ZMod 2) D ≤ h+4 ∧
      (Nat.card {w : Fin n → ZMod 2 // ∀ i, mark i = true →
        out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i} : ℤ) ≤
      Ssum n hn mark D := by
  by_contra hcon
  have hW : ((2:ℤ)^n) = (Nat.card (Fin n → ZMod 2) : ℤ) := by
    simp [Nat.card_eq_fintype_card]
  refine h6_fiber_sum (run n h ask) (fun w => ∀ i, mark i = true →
    out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i) (fun w0 => ?_)
  obtain ⟨D, hb, he, hf, hc⟩ := h6_cell n hn h6 h mark name c ask A b w0
  have hlt := lt_of_not_ge (fun hle => hcon ⟨D, hb, he, hf, hle⟩)
  rw [← hW]
  refine le_trans hc (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  linarith

lemma h4_z2_pred : ∀ x y s t l c : ZMod 2,
    (x * y + (l + c) = t * x + s * y + l + (s * t + c) ↔ (x - s) * (y - t) = 0) := by
  decide

lemma h4_out_pred (n : ℕ) (hn : 0 < n) (name c wp : Fin n → ZMod 2) :
    ∃ (A' : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b' : Fin n → ZMod 2),
      ∀ (w : Fin n → ZMod 2) (i : Fin n), out n hn name c w i = (A' w + b') i ↔
        mix n hn (w - wp) (ix n hn (i.val+1)) * mix n hn (w - wp) (ix n hn (i.val+2)) = 0 := by
  obtain ⟨L, c0, hL⟩ := out_affine n hn name c
  refine ⟨LinearMap.pi (fun i =>
      ((mix n hn wp (ix n hn (i.val+2))) • ((LinearMap.proj (ix n hn (i.val+1))) ∘ₗ mixL n hn) +
      (mix n hn wp (ix n hn (i.val+1))) • ((LinearMap.proj (ix n hn (i.val+2))) ∘ₗ mixL n hn) +
      (LinearMap.proj i) ∘ₗ L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)),
    fun i => mix n hn wp (ix n hn (i.val+1)) * mix n hn wp (ix n hn (i.val+2)) + c0 i, ?_⟩
  intro w i
  rw [hL w i, mix_sub]
  simp only [Pi.add_apply, Pi.sub_apply, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, mixL_apply, smul_eq_mul]
  exact h4_z2_pred _ _ _ _ _ _

lemma h4_count (n : ℕ) (N : Submodule (ZMod 2) (Fin n → ZMod 2))
    (r : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (P : (Fin n → ZMod 2) → Prop)
    (hr1 : ∀ w, w - r w ∈ N) (hr2 : ∀ w, ∀ u ∈ N, r (r w + u) = r w) :
    Nat.card N * Nat.card {w : Fin n → ZMod 2 // P (w - r w)} =
      2^n * Nat.card {u : N // P (u : Fin n → ZMod 2)} := by
  have hΦ : Function.Involutive (fun x : (Fin n → ZMod 2) × N =>
      ((r x.1 + (x.2 : Fin n → ZMod 2), ⟨x.1 - r x.1, hr1 x.1⟩) : (Fin n → ZMod 2) × N)) := by
    rintro ⟨w, u⟩
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show r (r w + (u : Fin n → ZMod 2)) + (w - r w) = w
      rw [hr2 w u u.2, add_sub_cancel]
    · show r w + (u : Fin n → ZMod 2) - r (r w + (u : Fin n → ZMod 2)) = u
      rw [hr2 w u u.2, add_sub_cancel_left]
  have e1 : {x : (Fin n → ZMod 2) × N // P (x.1 - r x.1)} ≃
      {x : (Fin n → ZMod 2) × N // P (x.2 : Fin n → ZMod 2)} :=
    Equiv.subtypeEquiv (Function.Involutive.toPerm _ hΦ) (fun x => Iff.rfl)
  have e2 : {x : (Fin n → ZMod 2) × N // P (x.1 - r x.1)} ≃
      {w : Fin n → ZMod 2 // P (w - r w)} × N :=
    Equiv.prodSubtypeFstEquivSubtypeProd (p := fun w => P (w - r w))
  have e3 : {x : (Fin n → ZMod 2) × N // P (x.2 : Fin n → ZMod 2)} ≃
      (Fin n → ZMod 2) × {u : N // P (u : Fin n → ZMod 2)} :=
    { toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
      invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := Nat.card_congr (e2.symm.trans (e1.trans e3))
  rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h1
  rw [mul_comm, h1]

lemma h4_nonadaptive_aux (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool) (name c : Fin n → ZMod 2)
    (N : Submodule (ZMod 2) (Fin n → ZMod 2)) (R : (Fin n → ZMod 2) → ℕ)
    (hR : ∀ w w', R w = R w' ↔ w - w' ∈ N) :
    ∃ (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)),
      Nat.card N * Nat.card {w : Fin n → ZMod 2 // ∀ i, mark i = true →
        out n hn name c w i = (A (R w) w + b (R w)) i} =
      2^n * Nat.card {u : N // adm n hn mark (mix n hn (u : Fin n → ZMod 2))} := by
  have hrep : ∀ w, R (Function.invFun R (R w)) = R w := fun w => Function.invFun_eq ⟨w, rfl⟩
  choose A b hAb using fun p : ℕ => h4_out_pred n hn name c (Function.invFun R p)
  refine ⟨A, b, ?_⟩
  have hgood : ∀ w, (∀ i, mark i = true → out n hn name c w i = (A (R w) w + b (R w)) i) ↔
      adm n hn mark (mix n hn (w - Function.invFun R (R w))) := by
    intro w
    unfold adm
    exact forall_congr' (fun i => imp_congr_right (fun _ => hAb _ w i))
  rw [Nat.card_congr (Equiv.subtypeEquivRight hgood)]
  refine h4_count n N (fun w => Function.invFun R (R w)) (fun x => adm n hn mark (mix n hn x))
    (fun w => (hR w _).mp (hrep w).symm) (fun w u hu => ?_)
  refine congrArg (Function.invFun R) (((hR _ _).mpr ?_).trans (hrep w))
  rw [add_sub_cancel_left]
  exact hu

lemma nonadaptive_count (n : ℕ) (hn : 0 < n) (h : ℕ) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (φ : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)),
      Nat.card (LinearMap.ker (LinearMap.pi φ)) *
        Nat.card {w : Fin n → ZMod 2 // ∀ i, mark i = true → out n hn name c w i =
          (A (run n h (fun j _ => φ j) w) w + b (run n h (fun j _ => φ j) w)) i} =
      2^n * Nat.card {u : LinearMap.ker (LinearMap.pi φ) //
        adm n hn mark (mix n hn (u : Fin n → ZMod 2))} := by
  refine h4_nonadaptive_aux n hn mark name c _ _ ?_
  intro w w'
  obtain ⟨p, hp⟩ := run_eq_iff n h (fun j _ => φ j) w'
  rw [hp w, LinearMap.mem_ker]
  constructor
  · intro hj
    funext j
    exact hj j
  · intro hj j
    exact congrFun hj j

lemma h6_orth_eq (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (h : ℕ)
    (D : Submodule (ZMod 2) (Fin n → ZMod 2)) (hbase : ∀ j, base n j ∈ D)
    (v : Fin h → (Fin n → ZMod 2)) (hvD : ∀ j, v j ∈ D)
    (hspan : D ≤ Submodule.span (ZMod 2) (Set.range (base n)) ⊔
      Submodule.span (ZMod 2) (Set.range v))
    (φ : Fin h → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hφ : ∀ j w, φ j w = dot n (v j) (mix n hn w)) :
    orth n ((mixL n hn).comp (LinearMap.ker (LinearMap.pi φ)).subtype) = D := by
  apply le_antisymm
  · intro z hz
    rw [mem_orth] at hz
    apply double_orth n D z
    intro x hx
    have hxb : ∀ j, dot n (base n j) x = 0 := by
      intro j
      rw [dot_comm]
      exact hx _ (hbase j)
    obtain ⟨w, rfl⟩ := mix_surj n hn h6 x hxb
    have hwN : w ∈ LinearMap.ker (LinearMap.pi φ) := by
      rw [LinearMap.mem_ker]
      funext j
      show φ j w = 0
      rw [hφ, dot_comm]
      exact hx _ (hvD j)
    have hzw := hz ⟨w, hwN⟩
    rw [dot_comm]
    exact hzw
  · refine le_trans hspan (sup_le ?_ ?_)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, mem_orth]
      intro u
      exact base_dot_mix n hn h6 j _
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, mem_orth]
      intro u
      have hu := u.2
      rw [LinearMap.mem_ker] at hu
      have huj : φ j u.1 = 0 := congrFun hu j
      rw [hφ] at huj
      exact huj

lemma lower (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (h : ℕ) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hbase : ∀ j, base n j ∈ D) (heven : ∀ z ∈ D, even n z ∈ D)
    (hfin : Module.finrank (ZMod 2) D ≤ h+4) :
    ∃ (ask : Fin h → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (A : ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ℕ → (Fin n → ZMod 2)),
      (∃ v : Fin h → (Fin n → ZMod 2),
        (∀ j, even n (v j) = v j ∨ even n (v j) = 0) ∧
        (∀ j p w, ask j p w = ∑ i, v j i * mix n hn w i)) ∧
      Ssum n hn mark D ≤ (Nat.card {w : Fin n → ZMod 2 // ∀ i, mark i = true →
        out n hn name c w i = (A (run n h ask w) w + b (run n h ask w)) i} : ℤ) := by
  have hBD : Submodule.span (ZMod 2) (Set.range (base n)) ≤ D := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact hbase j
  have hBe : ∀ z ∈ Submodule.span (ZMod 2) (Set.range (base n)),
      even n z ∈ Submodule.span (ZMod 2) (Set.range (base n)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rcases even_base n j with h1 | h1
      · rw [h1]
        exact Submodule.subset_span ⟨j, rfl⟩
      · rw [h1]
        exact Submodule.zero_mem _
    | zero =>
      rw [even_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [even_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [even_smul]
      exact Submodule.smul_mem _ a hx
  have hfin' : Module.finrank (ZMod 2) D ≤
      h + Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (base n))) := by
    have h4 := base_span_finrank n hn h6
    omega
  obtain ⟨v, hv1, hv2, hv3⟩ := lane_pure_span n h _ D hBD hBe heven hfin'
  have hφ : ∀ j w, ((dotL n (v j)).comp (mixL n hn)) w = dot n (v j) (mix n hn w) := by
    intro j w
    show dot n (mix n hn w) (v j) = dot n (v j) (mix n hn w)
    exact dot_comm n _ _
  obtain ⟨A, b, hAb⟩ :=
    nonadaptive_count n hn h mark name c (fun j => (dotL n (v j)).comp (mixL n hn))
  refine ⟨fun j _ => (dotL n (v j)).comp (mixL n hn), A, b, ⟨v, hv1, ?_⟩, ?_⟩
  · intro j p w
    exact hφ j w
  · have hF := fourier_count n hn mark ((mixL n hn).comp (LinearMap.ker (LinearMap.pi
      (fun j => (dotL n (v j)).comp (mixL n hn)))).subtype)
    rw [h6_orth_eq n hn h6 h D hbase v hv2 hv3 _ hφ] at hF
    have hAbZ := congrArg (fun k : ℕ => (k : ℤ)) hAb
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hAbZ
    have hEq := hAbZ.trans hF
    have hNpos : (0:ℤ) < (Nat.card (LinearMap.ker (LinearMap.pi
        (fun j => (dotL n (v j)).comp (mixL n hn)))) : ℤ) := by
      exact_mod_cast Nat.card_pos
    exact le_of_eq (mul_left_cancel₀ hNpos.ne' hEq).symm

lemma final (t : ℕ) (ht : 0 < t) (h : ℕ) (mark : Fin (6*t) → Bool)
    (name c : Fin (6*t) → ZMod 2) (k : ℕ) (fixed : Bool) :
    (∃ (ask : Fin h → ℕ → (Fin (6*t) → ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (A : ℕ → (Fin (6*t) → ZMod 2) →ₗ[ZMod 2] (Fin (6*t) → ZMod 2))
        (b : ℕ → (Fin (6*t) → ZMod 2)),
      (fixed = true → ∃ v : Fin h → (Fin (6*t) → ZMod 2),
        (∀ j, even (6*t) (v j) = v j ∨ even (6*t) (v j) = 0) ∧
        (∀ j p w, ask j p w =
          ∑ i, v j i * mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w i)) ∧
      k ≤ Nat.card {w : Fin (6*t) → ZMod 2 // ∀ i, mark i = true →
        out (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) name c w i =
          (A (run (6*t) h ask w) w + b (run (6*t) h ask w)) i}) ↔
    ∃ D : Submodule (ZMod 2) (Fin (6*t) → ZMod 2),
      (∀ j, base (6*t) j ∈ D) ∧ (∀ z ∈ D, even (6*t) z ∈ D) ∧
      Module.finrank (ZMod 2) D ≤ h+4 ∧
      (k : ℤ) ≤ Ssum (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) mark D := by
  have h6 : 6 ∣ 6*t := Dvd.intro t rfl
  constructor
  · rintro ⟨ask, A, b, -, hk⟩
    obtain ⟨D, h1, h2, h3, h4⟩ :=
      upper (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) h6 h mark name c ask A b
    exact ⟨D, h1, h2, h3, le_trans (Nat.cast_le.mpr hk) h4⟩
  · rintro ⟨D, h1, h2, h3, h4⟩
    obtain ⟨ask, A, b, hv, hc⟩ :=
      lower (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) h6 h mark name c D h1 h2 h3
    exact ⟨ask, A, b, fun _ => hv, Nat.cast_le.mp (le_trans h4 hc)⟩

end PEqualNP.Outside.L_meta_33628_aux

namespace PEqualNP.Outside.L_meta_33628_aux

def markT (n : ℕ) : Fin n → Bool := fun _ => true

def es (n s : ℕ) : Fin n → ZMod 2 := fun i => if i.val = s then 1 else 0

noncomputable def Bsp (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (base n))

noncomputable def D0 (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Bsp n ⊔ Submodule.span (ZMod 2) {es n 0}

abbrev C4 := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

noncomputable def bc (n : ℕ) (c : C4) : Fin n → ZMod 2 :=
  c.1 • base n 0 + c.2.1 • base n 1 + c.2.2.1 • base n 2 + c.2.2.2 • base n 3

noncomputable def SigB (n : ℕ) (hn : 0 < n) (u : Fin n → ZMod 2) : ℤ :=
  ∑ c : C4, tw n hn (markT n) (bc n c + u)

noncomputable def wt (n : ℕ) (z : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => z i ≠ 0)).card

noncomputable def Iset (n : ℕ) (hn : 0 < n) : Finset (Fin n → ZMod 2) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter (fun x => adm n hn (markT n) x)

def blocked (n : ℕ) (hn : 0 < n) (s : Fin n) (x : Fin n → ZMod 2) : Prop :=
  x (ix n hn (s.val + n - 1)) = 1 ∨ x (ix n hn (s.val + 1)) = 1

noncomputable def cntB (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ((Iset n hn).filter (fun x => ∀ s ∈ S, blocked n hn s x)).card

end PEqualNP.Outside.L_meta_33628_aux

namespace PEqualNP.Outside.L_meta_33628_aux

lemma bc_mem (n : ℕ) (c : C4) : bc n c ∈ Bsp n := by
  unfold bc Bsp
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))

lemma st_mem_Bsp (n : ℕ) (z : Fin n → ZMod 2) :
    z ∈ Bsp n ↔ ∃ c : C4, z = bc n c := by
  unfold Bsp
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(g 0, g 1, g 2, g 3), ?_⟩
    rw [← hg, Fin.sum_univ_four]
    rfl
  · rintro ⟨c, rfl⟩
    refine ⟨![c.1, c.2.1, c.2.2.1, c.2.2.2], ?_⟩
    rw [Fin.sum_univ_four]
    rfl

lemma mem_Bsp_iff (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (z : Fin n → ZMod 2) :
    z ∈ Bsp n ↔ ∃ c : C4, z = bc n c := by
  have _h := hn
  have _h' := h6
  exact st_mem_Bsp n z

lemma st_z2_eq (a b : ZMod 2) (h : a - b = 0) : a = b := sub_eq_zero.mp h

lemma bc_inj (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) : Function.Injective (bc n) := by
  intro c d h
  have li := h3_base_li n hn h6
  rw [Fintype.linearIndependent_iff] at li
  have key := li ![c.1 - d.1, c.2.1 - d.2.1, c.2.2.1 - d.2.2.1, c.2.2.2 - d.2.2.2] (by
    rw [Fin.sum_univ_four]
    have : bc n c - bc n d = 0 := sub_eq_zero.mpr h
    unfold bc at this
    show (c.1 - d.1) • base n 0 + (c.2.1 - d.2.1) • base n 1 + (c.2.2.1 - d.2.2.1) • base n 2
      + (c.2.2.2 - d.2.2.2) • base n 3 = 0
    rw [← this]
    simp only [sub_smul]
    abel)
  have e0 : c.1 - d.1 = 0 := key 0
  have e1 : c.2.1 - d.2.1 = 0 := key 1
  have e2 : c.2.2.1 - d.2.2.1 = 0 := key 2
  have e3 : c.2.2.2 - d.2.2.2 = 0 := key 3
  obtain ⟨c1, c2, c3, c4⟩ := c
  obtain ⟨d1, d2, d3, d4⟩ := d
  simp only [sub_eq_zero] at e0 e1 e2 e3
  rw [e0, e1, e2, e3]

lemma st_Ssum_image {α : Type} [Fintype α] (n : ℕ) (hn : 0 < n) (mark : Fin n → Bool)
    (D : Submodule (ZMod 2) (Fin n → ZMod 2)) (f : α → (Fin n → ZMod 2))
    (hf : Function.Injective f) (hD : ∀ z, z ∈ D ↔ ∃ a, z = f a) :
    Ssum n hn mark D = ∑ a, tw n hn mark (f a) := by
  classical
  rw [Ssum_eq, ← Finset.sum_filter]
  have e : (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun z => z ∈ D) =
      Finset.univ.image f := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hD]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  rw [e]
  exact Finset.sum_image (fun a _ b _ h => hf h)

lemma Ssum_Bsp (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (mark : Fin n → Bool) :
    Ssum n hn mark (Bsp n) = ∑ c : C4, tw n hn mark (bc n c) :=
  st_Ssum_image n hn mark (Bsp n) (bc n) (bc_inj n hn h6) (st_mem_Bsp n)

lemma st_z2_sum {M : Type} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ a : ZMod 2, f a = f 0 + f 1 := by
  have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [this, Finset.sum_pair (by decide)]

lemma Ssum_sup (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (mark : Fin n → Bool)
    (u : Fin n → ZMod 2) (hu : u ∉ Bsp n) :
    Ssum n hn mark (Bsp n ⊔ Submodule.span (ZMod 2) {u}) =
      ∑ c : C4, (tw n hn mark (bc n c) + tw n hn mark (bc n c + u)) := by
  have hinj : Function.Injective (fun p : C4 × ZMod 2 => bc n p.1 + p.2 • u) := by
    rintro ⟨c, a⟩ ⟨d, b⟩ h
    simp only at h
    have hab : a = b := by
      by_contra hne
      have hs : (a - b) • u = bc n d - bc n c := by
        rw [sub_smul, sub_eq_sub_iff_add_eq_add, add_comm, h]
      have hab1 : a - b = 1 := by
        rcases z2_cases (a - b) with h0 | h1
        · exact absurd (sub_eq_zero.mp h0) hne
        · exact h1
      rw [hab1, one_smul] at hs
      exact hu (hs ▸ Submodule.sub_mem _ (bc_mem n d) (bc_mem n c))
    subst hab
    have : c = d := bc_inj n hn h6 (add_right_cancel h)
    rw [this]
  rw [st_Ssum_image n hn mark _ _ hinj]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [st_z2_sum]
    simp
  · intro z
    rw [Submodule.mem_sup]
    constructor
    · rintro ⟨y, hy, w, hw, rfl⟩
      obtain ⟨c, rfl⟩ := (st_mem_Bsp n y).mp hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      exact ⟨(c, a), rfl⟩
    · rintro ⟨⟨c, a⟩, rfl⟩
      exact ⟨bc n c, bc_mem n c, a • u,
        Submodule.mem_span_singleton.mpr ⟨a, rfl⟩, rfl⟩

lemma es0_not_mem (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) : es n 0 ∉ Bsp n := by
  have h6n : 6 ≤ n := Nat.le_of_dvd hn h6
  intro h
  obtain ⟨c, hc⟩ := (st_mem_Bsp n _).mp h
  have v0 := congrFun hc ⟨0, by omega⟩
  have v2 := congrFun hc ⟨2, by omega⟩
  have v4 := congrFun hc ⟨4, by omega⟩
  simp only [es, bc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, base_apply] at v0 v2 v4
  obtain ⟨c1, c2, c3, c4⟩ := c
  simp at v0 v2 v4
  subst v2
  rw [← v0] at v4
  simp at v4

end PEqualNP.Outside.L_meta_33628_aux

namespace PEqualNP.Outside.L_meta_33628_aux

def fm_M (a : ZMod 2) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (if a = 0 then 1 else -1); 1, 0]

def fm_beta (c : C4) (r : ℕ) : ZMod 2 :=
  c.1 * h3_b 0 r + c.2.1 * h3_b 1 r + c.2.2.1 * h3_b 2 r + c.2.2.2 * h3_b 3 r

def fm_P (c : C4) : Matrix (Fin 2) (Fin 2) ℤ :=
  ((List.range 6).map (fun r => fm_M (fm_beta c (r % 6)))).prod

def fm_Q (c : C4) : Matrix (Fin 2) (Fin 2) ℤ :=
  ((List.range 6).map (fun r => fm_M (fm_beta c (r % 6) + if r = 0 then 1 else 0))).prod

lemma fm_tw (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) :
    tw n hn (markT n) z = (List.ofFn (fun i : Fin n => fm_M (z i))).prod.trace := by
  unfold tw markT fm_M
  simp only [ite_true]
  congr 3
  all_goals first
    | (funext b; exact Subsingleton.elim _ _)
    | (funext i; split_ifs <;> rfl)

lemma fm_ofFn (n : ℕ) (g : ℕ → Matrix (Fin 2) (Fin 2) ℤ) :
    List.ofFn (fun i : Fin n => g i.val) = (List.range n).map g := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

lemma fm_base (t : ℕ) (ht : 0 < 6 * t) (j : Fin 4) (i : Fin (6 * t)) :
    base (6 * t) j i = h3_b j (i.val % 6) := by
  have h := h3_base_ix (6 * t) ht (Dvd.intro t rfl) j i.val
  rw [ix_self] at h
  rw [h, h3_b_mod]

lemma fm_bc (t : ℕ) (ht : 0 < 6 * t) (c : C4) (i : Fin (6 * t)) :
    bc (6 * t) c i = fm_beta c (i.val % 6) := by
  simp only [bc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, fm_base t ht, fm_beta]

lemma fm_pow (c : C4) (t : ℕ) :
    ((List.range (6 * t)).map (fun i => fm_M (fm_beta c (i % 6)))).prod = fm_P c ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 6 * (t + 1) = 6 * t + 6 by ring, List.range_add, List.map_append, List.prod_append,
      ih, List.map_map, pow_succ]
    congr 1
    unfold fm_P
    congr 2
    funext i
    simp only [Function.comp_apply]
    rw [show (6 * t + i) % 6 = i % 6 by omega]

lemma fm_tw_bc (k : ℕ) (ht : 0 < 6 * (k + 1)) (c : C4) :
    tw (6 * (k + 1)) ht (markT _) (bc (6 * (k + 1)) c) = (fm_P c ^ (k + 1)).trace := by
  rw [fm_tw, ← fm_pow c (k + 1), ← fm_ofFn]
  congr 3
  funext i
  rw [fm_bc _ ht]

lemma fm_tw_bce (k : ℕ) (ht : 0 < 6 * (k + 1)) (c : C4) :
    tw (6 * (k + 1)) ht (markT _) (bc (6 * (k + 1)) c + es (6 * (k + 1)) 0) =
      (fm_Q c * fm_P c ^ k).trace := by
  rw [fm_tw]
  have e : (fun i : Fin (6 * (k + 1)) => fm_M ((bc (6 * (k + 1)) c + es (6 * (k + 1)) 0) i)) =
      fun i : Fin (6 * (k + 1)) =>
        (fun r : ℕ => fm_M (fm_beta c (r % 6) + if r = 0 then 1 else 0)) i.val := by
    funext i
    simp only [Pi.add_apply, fm_bc _ ht, es]
  have e2 : List.map ((fun r : ℕ => fm_M (fm_beta c (r % 6) + if r = 0 then 1 else 0)) ∘
      fun x => 6 + x) (List.range (6 * k)) =
      List.map (fun i => fm_M (fm_beta c (i % 6))) (List.range (6 * k)) := by
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [show (6 + i) % 6 = i % 6 by omega, ite_eq_right_iff.mpr (fun h => by omega), add_zero]
  rw [e, fm_ofFn (6 * (k + 1)) (fun r : ℕ => fm_M (fm_beta c (r % 6) + if r = 0 then 1 else 0)),
    show 6 * (k + 1) = 6 + 6 * k by ring, List.range_add, List.map_append,
    List.prod_append, List.map_map, e2, fm_pow c k]
  rfl

def fm_Y (c : C4) (k : ℕ) : ℤ := ((fm_P c + fm_Q c) * fm_P c ^ k).trace

lemma fm_det : ∀ c : C4, (fm_P c).det = 1 := by
  intro c; simp only [Matrix.det_fin_two]; revert c; decide

lemma fm_ch (A : Matrix (Fin 2) (Fin 2) ℤ) : A ^ 2 = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, sq]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, smul_eq_mul] <;> simp <;> ring

lemma fm_pow_rec (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = 1) (k : ℕ) :
    A ^ (k + 2) = A.trace • A ^ (k + 1) - A ^ k := by
  rw [pow_add, fm_ch, hA, one_smul, mul_sub, mul_one, mul_smul_comm, ← pow_succ]

lemma fm_Y_rec (c : C4) (k : ℕ) : fm_Y c (k + 2) = (fm_P c).trace * fm_Y c (k + 1) - fm_Y c k := by
  unfold fm_Y
  rw [fm_pow_rec _ (fm_det c), mul_sub, mul_smul_comm, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul]

lemma fm_uniq (x : ℤ) (u v : ℕ → ℤ) (hu : ∀ k, u (k + 2) = x * u (k + 1) - u k)
    (hv : ∀ k, v (k + 2) = x * v (k + 1) - v k) (h0 : u 0 = v 0) (h1 : u 1 = v 1) :
    ∀ k, u k = v k := by
  have H : ∀ k, u k = v k ∧ u (k + 1) = v (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih => exact ⟨ih.2, by rw [hu, hv, ih.1, ih.2]⟩
  exact fun k => (H k).1

def fm_A (x : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, x]

def fm_seq (x lo hi : ℤ) (t : ℕ) : ℤ := ((fm_A x ^ t).mulVec ![lo, hi]) 0

lemma fm_seq_rec (x lo hi : ℤ) (k : ℕ) :
    fm_seq x lo hi (k + 2) = x * fm_seq x lo hi (k + 1) - fm_seq x lo hi k := by
  have hd : (fm_A x).det = 1 := by simp [fm_A, Matrix.det_fin_two]
  have ht : (fm_A x).trace = x := by simp [fm_A, Matrix.trace_fin_two]
  unfold fm_seq
  rw [fm_pow_rec _ hd, ht, Matrix.sub_mulVec, Matrix.smul_mulVec]
  simp

lemma fm_seq1 (x lo hi : ℤ) : fm_seq x lo hi 1 = hi := by
  simp [fm_seq, fm_A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma fm_seq2 (x lo hi : ℤ) : fm_seq x lo hi 2 = x * hi - lo := by
  rw [fm_seq_rec x lo hi 0, fm_seq1]
  simp [fm_seq]

lemma fm_z2sum (f : ZMod 2 → ℤ) : ∑ a, f a = f 0 + f 1 := Fin.sum_univ_two f

def fm_S18 (k : ℕ) : ℤ := fm_Y (0,0,0,0) k
def fm_S6 (k : ℕ) : ℤ := fm_Y (0,0,0,1) k + fm_Y (0,0,1,0) k + fm_Y (0,0,1,1) k +
  fm_Y (0,1,0,0) k + fm_Y (1,0,0,0) k + fm_Y (1,1,0,0) k
def fm_S2 (k : ℕ) : ℤ := fm_Y (0,1,1,0) k + fm_Y (1,0,1,1) k + fm_Y (1,1,0,1) k
def fm_Sm (k : ℕ) : ℤ := fm_Y (0,1,0,1) k + fm_Y (0,1,1,1) k + fm_Y (1,0,0,1) k +
  fm_Y (1,0,1,0) k + fm_Y (1,1,1,0) k + fm_Y (1,1,1,1) k

lemma fm_tr18 : (fm_P (0,0,0,0)).trace = 18 := by decide
lemma fm_tr6 : (fm_P (0,0,0,1)).trace = 6 ∧ (fm_P (0,0,1,0)).trace = 6 ∧
    (fm_P (0,0,1,1)).trace = 6 ∧ (fm_P (0,1,0,0)).trace = 6 ∧ (fm_P (1,0,0,0)).trace = 6 ∧
    (fm_P (1,1,0,0)).trace = 6 := by decide
lemma fm_tr2 : (fm_P (0,1,1,0)).trace = 2 ∧ (fm_P (1,0,1,1)).trace = 2 ∧
    (fm_P (1,1,0,1)).trace = 2 := by decide
lemma fm_trm : (fm_P (0,1,0,1)).trace = -2 ∧ (fm_P (0,1,1,1)).trace = -2 ∧
    (fm_P (1,0,0,1)).trace = -2 ∧ (fm_P (1,0,1,0)).trace = -2 ∧ (fm_P (1,1,1,0)).trace = -2 ∧
    (fm_P (1,1,1,1)).trace = -2 := by decide

lemma fm_S18_rec (k : ℕ) : fm_S18 (k + 2) = 18 * fm_S18 (k + 1) - fm_S18 k := by
  unfold fm_S18; rw [fm_Y_rec, fm_tr18]

lemma fm_S6_rec (k : ℕ) : fm_S6 (k + 2) = 6 * fm_S6 (k + 1) - fm_S6 k := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := fm_tr6
  unfold fm_S6; simp only [fm_Y_rec, h1, h2, h3, h4, h5, h6]; ring

lemma fm_S2_rec (k : ℕ) : fm_S2 (k + 2) = 2 * fm_S2 (k + 1) - fm_S2 k := by
  obtain ⟨h1, h2, h3⟩ := fm_tr2
  unfold fm_S2; simp only [fm_Y_rec, h1, h2, h3]; ring

lemma fm_Sm_rec (k : ℕ) : fm_Sm (k + 2) = (-2) * fm_Sm (k + 1) - fm_Sm k := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := fm_trm
  unfold fm_Sm; simp only [fm_Y_rec, h1, h2, h3, h4, h5, h6]; ring

lemma fm_v0 : fm_S18 0 = 26 ∧ fm_S6 0 = 52 ∧ fm_S2 0 = 6 ∧ fm_Sm 0 = -20 := by
  unfold fm_S18 fm_S6 fm_S2 fm_Sm fm_Y
  simp only [pow_zero, mul_one]
  decide

lemma fm_v1 : fm_S18 1 = 466 ∧ fm_S6 1 = 300 ∧ fm_S2 1 = 6 ∧ fm_Sm 1 = 28 := by
  unfold fm_S18 fm_S6 fm_S2 fm_Sm fm_Y
  simp only [pow_one]
  decide

lemma fm_S18_eq (k : ℕ) : fm_S18 k = 2 * fm_seq 18 1 13 (k + 1) := by
  refine fm_uniq 18 _ (fun k => 2 * fm_seq 18 1 13 (k + 1)) fm_S18_rec ?_ ?_ ?_ k
  · intro k; simp only [fm_seq_rec 18 1 13 (k + 1)]; ring
  · rw [fm_v0.1, fm_seq1]; norm_num
  · rw [fm_v1.1, fm_seq2]; norm_num

lemma fm_S6_eq (k : ℕ) : fm_S6 k = 2 * fm_seq 6 6 26 (k + 1) := by
  refine fm_uniq 6 _ (fun k => 2 * fm_seq 6 6 26 (k + 1)) fm_S6_rec ?_ ?_ ?_ k
  · intro k; simp only [fm_seq_rec 6 6 26 (k + 1)]; ring
  · rw [fm_v0.2.1, fm_seq1]; norm_num
  · rw [fm_v1.2.1, fm_seq2]; norm_num

lemma fm_S2_eq (k : ℕ) : fm_S2 k = 6 := by
  refine fm_uniq 2 _ (fun _ => 6) fm_S2_rec ?_ fm_v0.2.2.1 fm_v1.2.2.1 k
  intro k; norm_num

lemma fm_Sm_eq (k : ℕ) : fm_Sm k = 2 * ((6 + 4 * ((k + 1 : ℕ) : ℤ)) * (-1 : ℤ) ^ (k + 1)) := by
  refine fm_uniq (-2) _ (fun k => 2 * ((6 + 4 * ((k + 1 : ℕ) : ℤ)) * (-1 : ℤ) ^ (k + 1)))
    fm_Sm_rec ?_ ?_ ?_ k
  · intro k; push_cast; ring
  · rw [fm_v0.2.2.2]; norm_num
  · rw [fm_v1.2.2.2]; norm_num

lemma fm_sum (k : ℕ) : ∑ c : C4, fm_Y c k = fm_S18 k + fm_S6 k + fm_S2 k + fm_Sm k := by
  simp only [Fintype.sum_prod_type, fm_z2sum]
  unfold fm_S18 fm_S6 fm_S2 fm_Sm
  ring

lemma fm_pair (k : ℕ) (ht : 0 < 6 * (k + 1)) (c : C4) :
    tw (6 * (k + 1)) ht (markT _) (bc (6 * (k + 1)) c) +
      tw (6 * (k + 1)) ht (markT _) (bc (6 * (k + 1)) c + es (6 * (k + 1)) 0) = fm_Y c k := by
  rw [fm_tw_bc, fm_tw_bce, fm_Y, add_mul, Matrix.trace_add, pow_succ']

lemma formula (t : ℕ) (ht : 0 < t) :
    Ssum (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) (markT (6*t)) (D0 (6*t)) =
      2*((((!![0,1;-1,18] : Matrix (Fin 2) (Fin 2) ℤ)^t).mulVec ![1,13]) 0 +
         (((!![0,1;-1,6] : Matrix (Fin 2) (Fin 2) ℤ)^t).mulVec ![6,26]) 0 + 3 +
         (6+4*(t : ℤ))*(-1 : ℤ)^t) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have h6 : 6 ∣ 6 * (k + 1) := Dvd.intro _ rfl
  have hn : 0 < 6 * (k + 1) := Nat.mul_pos (Nat.zero_lt_succ 5) ht
  unfold D0
  rw [Ssum_sup _ hn h6 _ _ (es0_not_mem _ hn h6)]
  rw [Finset.sum_congr rfl (fun c _ => fm_pair k hn c), fm_sum, fm_S18_eq, fm_S6_eq, fm_S2_eq,
    fm_Sm_eq]
  unfold fm_seq fm_A
  ring

end PEqualNP.Outside.L_meta_33628_aux

namespace PEqualNP.Outside.L_meta_33628_aux

open Finset

noncomputable def kc_B (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n → ZMod 2) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (Iset n hn).filter (fun x => ∀ s ∈ S, blocked n hn s x)

lemma kc_cntB (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) : cntB n hn S = (kc_B n hn S).card := rfl

lemma kc_mem_B (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    x ∈ kc_B n hn S ↔ x ∈ Iset n hn ∧ ∀ s ∈ S, blocked n hn s x := by
  unfold kc_B
  simp only [Finset.mem_filter]

lemma kc_LR (n : ℕ) (hn : 0 < n) (s : Fin n) :
    ix n hn ((ix n hn (s.val + n - 1)).val + 1) = s := by
  rw [ix_val_add]
  have e : s.val + n - 1 + 1 = s.val + n := by omega
  rw [e, ix_add_n, ix_self]

lemma kc_RL (n : ℕ) (hn : 0 < n) (s : Fin n) :
    ix n hn ((ix n hn (s.val + 1)).val + n - 1) = s := by
  rw [h3_ix_shift n hn _ 1 (by omega)]
  have e : s.val + 1 + (n - 1) = s.val + n := by omega
  rw [e, ix_add_n, ix_self]

lemma kc_RR (n : ℕ) (hn : 0 < n) (s : Fin n) :
    ix n hn ((ix n hn (s.val + 1)).val + 1) = ix n hn (s.val + 2) := by
  rw [ix_val_add]

lemma kc_R_inj (n : ℕ) (hn : 0 < n) (a b : Fin n)
    (h : ix n hn (a.val + 1) = ix n hn (b.val + 1)) : a = b := by
  rw [← kc_RL n hn a, ← kc_RL n hn b, h]

lemma kc_L_inj (n : ℕ) (hn : 0 < n) (a b : Fin n)
    (h : ix n hn (a.val + n - 1) = ix n hn (b.val + n - 1)) : a = b := by
  rw [← kc_LR n hn a, ← kc_LR n hn b, h]

lemma kc_R_eq_iff (n : ℕ) (hn : 0 < n) (j s : Fin n) :
    ix n hn (j.val + 1) = s ↔ j = ix n hn (s.val + n - 1) := by
  constructor
  · intro h
    rw [← h, kc_RL]
  · intro h
    rw [h, kc_LR]

lemma kc_LeqR (n : ℕ) (hn : 0 < n) (a s : Fin n)
    (h : ix n hn (a.val + n - 1) = ix n hn (s.val + 1)) : a = ix n hn (s.val + 2) := by
  rw [← kc_LR n hn a, h, kc_RR]

lemma kc_ReqL (n : ℕ) (hn : 0 < n) (a s : Fin n)
    (h : ix n hn (a.val + 1) = ix n hn (s.val + n - 1)) : s = ix n hn (a.val + 2) := by
  rw [← kc_LeqR n hn s a h.symm]

lemma kc_mc (a n : ℕ) (_hn : 0 < n) (h : a < 2 * n) :
    (a < n ∧ a % n = a) ∨ (n ≤ a ∧ a % n = a - n) := by
  by_cases ha : a < n
  · exact Or.inl ⟨ha, Nat.mod_eq_of_lt ha⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma kc_R_ne (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) (s : Fin n) : ix n hn (s.val + 1) ≠ s := by
  intro h
  have := congrArg Fin.val h
  rw [ix_val] at this
  have hs := s.2
  rcases kc_mc (s.val + 1) n hn (by omega) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega

lemma kc_par (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (a : ℕ) : (ix n hn a).val % 2 = a % 2 := by
  rw [ix_val]
  exact Nat.mod_mod_of_dvd a h2

lemma kc_mem_Iset (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) :
    x ∈ Iset n hn ↔ ∀ j : Fin n, x j * x (ix n hn (j.val + 1)) = 0 := by
  unfold Iset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, adm, markT, forall_const]
  constructor
  · intro H j
    have h := H (ix n hn (j.val + n - 1))
    rw [kc_LR, ix_val_add] at h
    have e : j.val + n - 1 + 2 = j.val + 1 + n := by omega
    rw [e, ix_add_n] at h
    exact h
  · intro H i
    have h := H (ix n hn (i.val + 1))
    rw [kc_RR] at h
    exact h

lemma kc_indR (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) (hx : x ∈ Iset n hn) (j : Fin n)
    (h : x j = 1) : x (ix n hn (j.val + 1)) = 0 := by
  have := (kc_mem_Iset n hn x).mp hx j
  rwa [h, one_mul] at this

lemma kc_indL (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) (hx : x ∈ Iset n hn) (j : Fin n)
    (h : x j = 1) : x (ix n hn (j.val + n - 1)) = 0 := by
  have := (kc_mem_Iset n hn x).mp hx (ix n hn (j.val + n - 1))
  rwa [kc_LR, h, mul_one] at this

lemma kc_ne1 (a : ZMod 2) (h : a ≠ 1) : a = 0 := by
  rcases z2_cases a with h' | h'
  · exact h'
  · exact absurd h' h

lemma kc_Iset_mono (n : ℕ) (hn : 0 < n) (x y : Fin n → ZMod 2) (hx : x ∈ Iset n hn)
    (h : ∀ j, y j = x j ∨ y j = 0) : y ∈ Iset n hn := by
  rw [kc_mem_Iset] at hx ⊢
  intro j
  rcases h j with h1 | h1
  · rcases h (ix n hn (j.val + 1)) with h3 | h3
    · rw [h1, h3]; exact hx j
    · rw [h3, mul_zero]
  · rw [h1, zero_mul]

lemma kc_Iset_set (n : ℕ) (hn : 0 < n) (h2 : 2 ≤ n) (x y : Fin n → ZMod 2) (i : Fin n)
    (hx : x ∈ Iset n hn) (hL : x (ix n hn (i.val + n - 1)) = 0) (hR : x (ix n hn (i.val + 1)) = 0)
    (h : ∀ j, j ≠ i → y j = x j) : y ∈ Iset n hn := by
  rw [kc_mem_Iset] at hx ⊢
  intro j
  by_cases hj : j = i
  · subst hj
    rw [h _ (kc_R_ne n hn h2 j), hR, mul_zero]
  · rw [h j hj]
    by_cases hr : ix n hn (j.val + 1) = i
    · have := (kc_R_eq_iff n hn j i).mp hr
      rw [this, hL, zero_mul]
    · rw [h _ hr]
      exact hx j

lemma kc_tw (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) :
    tw n hn (markT n) z = ∑ x ∈ Iset n hn, sgn (dot n z x) := by
  rw [tw_eq_sum]
  unfold Iset
  rw [Finset.sum_filter]
  exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) (fun x _ => by congr)

lemma kc_upd0_keep (n : ℕ) (f : Fin n → ZMod 2) (i j : Fin n) (h : f j = 0) :
    Function.update f i 0 j = 0 := by
  by_cases hj : j = i
  · subst hj; exact Function.update_self _ _ _
  · rw [Function.update_of_ne hj]; exact h

lemma kc_nz (a : ZMod 2) (h : a ≠ 0) : a = 1 := (z2_cases a).resolve_left h

lemma kc_dot_single (n : ℕ) (z x : Fin n → ZMod 2) (s : Fin n) :
    dot n z (x + Pi.single s 1) = dot n z x + z s := by
  rw [dot_add_right]
  congr 1
  unfold dot
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ s) h

lemma kc_single_ne (n : ℕ) (s i : Fin n) (h : i ≠ s) (x : Fin n → ZMod 2) :
    (x + Pi.single s (1 : ZMod 2) : Fin n → ZMod 2) i = x i := by
  simp [Pi.single_apply, h]

lemma kc_blk_toggle (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (s s' : Fin n)
    (hp : s.val % 2 = s'.val % 2) (x : Fin n → ZMod 2) :
    blocked n hn s' (x + Pi.single s 1) ↔ blocked n hn s' x := by
  have hL : ix n hn (s'.val + n - 1) ≠ s := by
    intro h
    have := kc_par n hn h2 (s'.val + n - 1)
    rw [h] at this
    obtain ⟨m, hm⟩ := h2
    omega
  have hR : ix n hn (s'.val + 1) ≠ s := by
    intro h
    have := kc_par n hn h2 (s'.val + 1)
    rw [h] at this
    omega
  unfold blocked
  rw [kc_single_ne n s _ hL, kc_single_ne n s _ hR]

noncomputable def kc_U (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    Finset (Fin n) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  S.filter (fun s => ¬ blocked n hn s x)

lemma kc_mem_U (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) (s : Fin n) :
    s ∈ kc_U n hn S x ↔ s ∈ S ∧ ¬ blocked n hn s x := by
  unfold kc_U
  simp only [Finset.mem_filter]

noncomputable def kc_A (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) : Finset (Fin n → ZMod 2) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (Iset n hn).filter (fun x => ¬ ∀ s ∈ S, blocked n hn s x)

lemma kc_mem_A (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    x ∈ kc_A n hn S ↔ x ∈ Iset n hn ∧ ¬ ∀ s ∈ S, blocked n hn s x := by
  unfold kc_A
  simp only [Finset.mem_filter]

lemma kc_U_toggle (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (S : Finset (Fin n)) (p : ℕ)
    (hpar : ∀ s ∈ S, s.val % 2 = p) (s : Fin n) (hs : s ∈ S) (x : Fin n → ZMod 2) :
    kc_U n hn S (x + Pi.single s 1) = kc_U n hn S x := by
  ext t
  rw [kc_mem_U, kc_mem_U]
  constructor
  · rintro ⟨ht, hb⟩
    refine ⟨ht, ?_⟩
    rwa [kc_blk_toggle n hn h2 s t (by rw [hpar s hs, hpar t ht]) x] at hb
  · rintro ⟨ht, hb⟩
    refine ⟨ht, ?_⟩
    rwa [kc_blk_toggle n hn h2 s t (by rw [hpar s hs, hpar t ht]) x]

lemma kc_U_ne (n : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2)
    (hx : x ∈ kc_A n hn S) : (kc_U n hn S x).Nonempty := by
  rw [kc_mem_A] at hx
  obtain ⟨s, hs, hb⟩ := not_forall₂.mp hx.2
  exact ⟨s, (kc_mem_U n hn S x s).mpr ⟨hs, hb⟩⟩

lemma kc_min_congr (n : ℕ) {T T' : Finset (Fin n)} (h : T = T') (hT : T.Nonempty)
    (hT' : T'.Nonempty) : T.min' hT = T'.min' hT' := by
  subst h
  rfl

lemma kc_unblk (n : ℕ) (hn : 0 < n) (s : Fin n) (x : Fin n → ZMod 2) (h : ¬ blocked n hn s x) :
    x (ix n hn (s.val + n - 1)) = 0 ∧ x (ix n hn (s.val + 1)) = 0 := by
  unfold blocked at h
  rw [not_or] at h
  exact ⟨kc_ne1 _ h.1, kc_ne1 _ h.2⟩

lemma kc_gmem (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (S : Finset (Fin n)) (p : ℕ)
    (hpar : ∀ s ∈ S, s.val % 2 = p) (x : Fin n → ZMod 2) (t : Fin n) (hx : x ∈ kc_A n hn S)
    (ht : t ∈ kc_U n hn S x) : x + Pi.single t 1 ∈ kc_A n hn S := by
  have h2' : 2 ≤ n := by
    obtain ⟨m, hm⟩ := h2
    omega
  rw [kc_mem_A] at hx ⊢
  rw [kc_mem_U] at ht
  have hu := kc_unblk n hn t x ht.2
  refine ⟨kc_Iset_set n hn h2' x _ t hx.1 hu.1 hu.2 (fun j hj => kc_single_ne n t j hj x), ?_⟩
  intro H
  have := H t ht.1
  rw [kc_blk_toggle n hn h2 t t rfl x] at this
  exact ht.2 this

lemma kc_sgn_flip (a : ZMod 2) : sgn a + sgn (a + 1) = 0 := by
  rcases z2_cases a with h | h <;> rw [h] <;> decide

lemma kc_inv (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (S : Finset (Fin n)) (p : ℕ)
    (hpar : ∀ s ∈ S, s.val % 2 = p) (hz : ∀ s ∈ S, z s = 1) :
    ∑ x ∈ kc_A n hn S, sgn (dot n z x) = 0 := by
  have hmem : ∀ x (hx : x ∈ kc_A n hn S),
      x + Pi.single ((kc_U n hn S x).min' (kc_U_ne n hn S x hx)) 1 ∈ kc_A n hn S :=
    fun x hx => kc_gmem n hn h2 S p hpar x _ hx (Finset.min'_mem _ _)
  refine Finset.sum_involution
    (fun x hx => x + Pi.single ((kc_U n hn S x).min' (kc_U_ne n hn S x hx)) 1) ?_ ?_ hmem ?_
  · intro x hx
    have ht := Finset.min'_mem _ (kc_U_ne n hn S x hx)
    rw [kc_mem_U] at ht
    rw [kc_dot_single, hz _ ht.1]
    exact kc_sgn_flip _
  · intro x hx _ h
    have := congrFun h ((kc_U n hn S x).min' (kc_U_ne n hn S x hx))
    rw [Pi.add_apply, Pi.single_eq_same] at this
    have h1 : (1 : ZMod 2) = 0 := add_left_cancel (this.trans (add_zero _).symm)
    exact absurd h1 (by decide)
  · intro x hx
    have ht := Finset.min'_mem _ (kc_U_ne n hn S x hx)
    rw [kc_mem_U] at ht
    rw [kc_min_congr n (kc_U_toggle n hn h2 S p hpar _ ht.1 x) _ (kc_U_ne n hn S x hx)]
    rw [add_assoc, fn_add_self, add_zero]

lemma kc_split (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (S : Finset (Fin n))
    (p : ℕ) (hpar : ∀ s ∈ S, s.val % 2 = p) (hz : ∀ s ∈ S, z s = 1) :
    tw n hn (markT n) z = ∑ x ∈ kc_B n hn S, sgn (dot n z x) := by
  rw [kc_tw]
  have hU : Iset n hn = kc_B n hn S ∪ kc_A n hn S := by
    ext x
    simp only [Finset.mem_union, kc_mem_B, kc_mem_A]
    tauto
  have hD : Disjoint (kc_B n hn S) (kc_A n hn S) := by
    rw [Finset.disjoint_left]
    intro x h1 h3
    rw [kc_mem_B] at h1
    rw [kc_mem_A] at h3
    exact h3.2 h1.2
  rw [hU, Finset.sum_union hD, kc_inv n hn h2 z S p hpar hz, add_zero]

lemma tw_abs_le (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (p : ℕ) :
    |tw n hn (markT n) z| ≤
      (cntB n hn (Finset.univ.filter (fun s => z s ≠ 0 ∧ s.val % 2 = p)) : ℤ) := by
  have hp1 : ∀ s ∈ Finset.univ.filter (fun s => z s ≠ 0 ∧ s.val % 2 = p), s.val % 2 = p := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact hs.2.2
  have hp2 : ∀ s ∈ Finset.univ.filter (fun s => z s ≠ 0 ∧ s.val % 2 = p), z s = 1 := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact kc_nz _ hs.2.1
  rw [kc_split n hn h2 z _ p hp1 hp2, kc_cntB]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rcases z2_cases (dot n z x) with h | h <;> rw [h] <;> decide

lemma kc_dot0 (n : ℕ) (hn : 0 < n) (z x : Fin n → ZMod 2)
    (hx : x ∈ kc_B n hn (Finset.univ.filter (fun s => z s ≠ 0))) : dot n z x = 0 := by
  rw [kc_mem_B] at hx
  unfold dot
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : z i = 0
  · rw [hi, zero_mul]
  have hb := hx.2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  rcases z2_cases (x i) with h | h
  · rw [h, mul_zero]
  exfalso
  rcases hb with hb | hb
  · rw [kc_indL n hn x hx.1 i h] at hb
    exact absurd hb (by decide)
  · rw [kc_indR n hn x hx.1 i h] at hb
    exact absurd hb (by decide)

lemma tw_pure (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (p : ℕ)
    (hz : ∀ s, z s ≠ 0 → s.val % 2 = p) :
    tw n hn (markT n) z = (cntB n hn (Finset.univ.filter (fun s => z s ≠ 0)) : ℤ) := by
  have hp1 : ∀ s ∈ Finset.univ.filter (fun s => z s ≠ 0), s.val % 2 = p := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact hz s hs.2
  have hp2 : ∀ s ∈ Finset.univ.filter (fun s => z s ≠ 0), z s = 1 := by
    intro s hs
    rw [Finset.mem_filter] at hs
    exact kc_nz _ hs.2
  rw [kc_split n hn h2 z _ p hp1 hp2, kc_cntB]
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun x hx => by rw [kc_dot0 n hn z x hx]; rfl)]
  simp

lemma cntB_anti (n : ℕ) (hn : 0 < n) (S T : Finset (Fin n)) (h : S ⊆ T) :
    cntB n hn T ≤ cntB n hn S := by
  rw [kc_cntB, kc_cntB]
  apply Finset.card_le_card
  intro x hx
  rw [kc_mem_B] at hx ⊢
  exact ⟨hx.1, fun s hs => hx.2 s (h hs)⟩

lemma kc_clr_val (n : ℕ) (f : Fin n → ZMod 2) (a b j : Fin n) (hja : j ≠ a) (hjb : j ≠ b) :
    Function.update (Function.update f a 0) b 0 j = f j := by
  rw [Function.update_of_ne hjb, Function.update_of_ne hja]

lemma kc_val_ix (n : ℕ) (hn : 0 < n) (a : Fin n) (b : ℕ) (h : a = ix n hn b) : a.val = b % n := by
  rw [h, ix_val]

lemma kc_B_maps (n : ℕ) (hn : 0 < n) (s : Fin n) (S' : Finset (Fin n)) (hs : s ∉ S')
    (hsp : ∀ t ∈ S', t.val ≠ (s.val + 2) % n ∧ s.val ≠ (t.val + 2) % n)
    (x : Fin n → ZMod 2) (hx : x ∈ kc_B n hn (insert s S')) :
    Function.update (Function.update x (ix n hn (s.val + n - 1)) 0) (ix n hn (s.val + 1)) 0 ∈
      kc_B n hn S' \ kc_B n hn (insert s S') := by
  rw [kc_mem_B] at hx
  rw [Finset.mem_sdiff, kc_mem_B, kc_mem_B]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply kc_Iset_mono n hn x _ hx.1
    intro j
    by_cases hR : j = ix n hn (s.val + 1)
    · right
      rw [hR, Function.update_self]
    by_cases hL : j = ix n hn (s.val + n - 1)
    · right
      rw [Function.update_of_ne hR, hL, Function.update_self]
    · left
      exact kc_clr_val n x _ _ j hL hR
  · intro t ht
    have hb := hx.2 t (Finset.mem_insert_of_mem ht)
    have hts : t ≠ s := fun h => hs (h ▸ ht)
    have hLL : ix n hn (t.val + n - 1) ≠ ix n hn (s.val + n - 1) :=
      fun h => hts (kc_L_inj n hn t s h)
    have hLR : ix n hn (t.val + n - 1) ≠ ix n hn (s.val + 1) :=
      fun h => (hsp t ht).1 (kc_val_ix n hn _ _ (kc_LeqR n hn t s h))
    have hRL : ix n hn (t.val + 1) ≠ ix n hn (s.val + n - 1) :=
      fun h => (hsp t ht).2 (kc_val_ix n hn _ _ (kc_ReqL n hn t s h))
    have hRR : ix n hn (t.val + 1) ≠ ix n hn (s.val + 1) :=
      fun h => hts (kc_R_inj n hn t s h)
    unfold blocked at hb ⊢
    rw [kc_clr_val n x _ _ _ hLL hLR, kc_clr_val n x _ _ _ hRL hRR]
    exact hb
  · intro H
    have h := H.2 s (Finset.mem_insert_self _ _)
    unfold blocked at h
    rw [Function.update_self,
      kc_upd0_keep n _ _ _ (Function.update_self _ _ _)] at h
    rcases h with h | h <;> exact absurd h (by decide)

lemma kc_step (n : ℕ) (hn : 0 < n) (s : Fin n) (S' : Finset (Fin n)) (hs : s ∉ S')
    (hsp : ∀ t ∈ S', t.val ≠ (s.val + 2) % n ∧ s.val ≠ (t.val + 2) % n) :
    5 * cntB n hn (insert s S') ≤ 4 * cntB n hn S' := by
  classical
  rw [kc_cntB, kc_cntB]
  have hsub : kc_B n hn (insert s S') ⊆ kc_B n hn S' := by
    intro x hx
    rw [kc_mem_B] at hx ⊢
    exact ⟨hx.1, fun t ht => hx.2 t (Finset.mem_insert_of_mem ht)⟩
  have hinj : (kc_B n hn (insert s S')).card ≤
      ((kc_B n hn S' \ kc_B n hn (insert s S')) ×ˢ
        (Finset.univ : Finset (ZMod 2 × ZMod 2))).card := by
    apply Finset.card_le_card_of_injOn (fun x => (Function.update (Function.update x
      (ix n hn (s.val + n - 1)) 0) (ix n hn (s.val + 1)) 0,
      (x (ix n hn (s.val + n - 1)), x (ix n hn (s.val + 1)))))
    · intro x hx
      rw [Finset.mem_coe] at hx
      rw [Finset.mem_coe, Finset.mem_product]
      exact ⟨kc_B_maps n hn s S' hs hsp x hx, Finset.mem_univ _⟩
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2, h3⟩ := hxy
      funext j
      by_cases hR : j = ix n hn (s.val + 1)
      · rw [hR]
        exact h3
      by_cases hL : j = ix n hn (s.val + n - 1)
      · rw [hL]
        exact h2
      have := congrFun h1 j
      rwa [kc_clr_val n x _ _ j hL hR, kc_clr_val n y _ _ j hL hR] at this
  rw [Finset.card_product, Finset.card_univ, Finset.card_sdiff_of_subset hsub] at hinj
  have h4 : Fintype.card (ZMod 2 × ZMod 2) = 4 := by
    rw [Fintype.card_prod, ZMod.card]
  rw [h4] at hinj
  have := Finset.card_le_card hsub
  omega

lemma kc_B_empty (n : ℕ) (hn : 0 < n) : kc_B n hn ∅ = Iset n hn := by
  ext x
  rw [kc_mem_B]
  simp

lemma decay (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (S : Finset (Fin n))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, s'.val ≠ (s.val + 2) % n) :
    5 ^ S.card * cntB n hn S ≤ 4 ^ S.card * (Iset n hn).card := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [kc_cntB, kc_B_empty]; simp
  | insert s S' hs ih =>
    have hS' : ∀ a ∈ S', ∀ b ∈ S', b.val ≠ (a.val + 2) % n := fun a ha b hb =>
      hS a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
    have hI := ih hS'
    have hstep := kc_step n hn s S' hs (fun t ht =>
      ⟨hS s (Finset.mem_insert_self _ _) t (Finset.mem_insert_of_mem ht),
       hS t (Finset.mem_insert_of_mem ht) s (Finset.mem_insert_self _ _)⟩)
    rw [Finset.card_insert_of_notMem hs, pow_succ, pow_succ]
    calc 5 ^ S'.card * 5 * cntB n hn (insert s S')
        = 5 ^ S'.card * (5 * cntB n hn (insert s S')) := by ring
      _ ≤ 5 ^ S'.card * (4 * cntB n hn S') := Nat.mul_le_mul_left _ hstep
      _ = 4 * (5 ^ S'.card * cntB n hn S') := by ring
      _ ≤ 4 * (4 ^ S'.card * (Iset n hn).card) := Nat.mul_le_mul_left _ hI
      _ = 4 ^ S'.card * 4 * (Iset n hn).card := by ring

lemma kc_card_upd (n : ℕ) (A : Finset (Fin n → ZMod 2)) (i : Fin n) (a : ZMod 2) :
    A.card ≤ 2 * (A.image (fun x => Function.update x i a)).card := by
  classical
  apply Finset.card_le_mul_card_image
  intro b _
  calc (A.filter (fun x => Function.update x i a = b)).card
      ≤ ({Function.update b i 0, Function.update b i 1} : Finset (Fin n → ZMod 2)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        have hx' : x = Function.update b i (x i) := by
          rw [← hx.2, Function.update_idem, Function.update_eq_self]
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases z2_cases (x i) with h | h
        · left
          rw [hx', h]
        · right
          rw [hx', h]
    _ ≤ 2 := Finset.card_le_two

lemma kc_upd0_mem (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) (i : Fin n) (hx : x ∈ Iset n hn) :
    Function.update x i 0 ∈ Iset n hn := by
  apply kc_Iset_mono n hn x _ hx
  intro j
  by_cases hj : j = i
  · right
    rw [hj, Function.update_self]
  · left
    exact Function.update_of_ne hj _ _

lemma kc_low_mem (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (s s' : Fin n) (h1 : s ≠ s')
    (h2 : s'.val ≠ (s.val + 2) % n) (x : Fin n → ZMod 2) (hx : x ∈ Iset n hn) :
    Function.update (Function.update (Function.update (Function.update (Function.update x
      (ix n hn (s'.val + n - 1)) 0) (ix n hn (s'.val + 1)) 0) s 0) (ix n hn (s.val + 2)) 0)
      (ix n hn (s.val + 1)) 1 ∈ kc_B n hn {s} \ kc_B n hn {s, s'} := by
  set w := Function.update (Function.update (Function.update (Function.update x
      (ix n hn (s'.val + n - 1)) 0) (ix n hn (s'.val + 1)) 0) s 0) (ix n hn (s.val + 2)) 0
    with hw
  have hwI : w ∈ Iset n hn :=
    kc_upd0_mem n hn _ _ (kc_upd0_mem n hn _ _ (kc_upd0_mem n hn _ _ (kc_upd0_mem n hn _ _ hx)))
  have wL : w (ix n hn (s'.val + n - 1)) = 0 :=
    kc_upd0_keep n _ _ _ (kc_upd0_keep n _ _ _ (kc_upd0_keep n _ _ _ (Function.update_self _ _ _)))
  have wR : w (ix n hn (s'.val + 1)) = 0 :=
    kc_upd0_keep n _ _ _ (kc_upd0_keep n _ _ _ (Function.update_self _ _ _))
  have ws : w s = 0 := kc_upd0_keep n _ _ _ (Function.update_self _ _ _)
  have ws2 : w (ix n hn (s.val + 2)) = 0 := Function.update_self _ _ _
  have hyI : Function.update w (ix n hn (s.val + 1)) 1 ∈ Iset n hn := by
    apply kc_Iset_set n hn (by omega) w _ (ix n hn (s.val + 1)) hwI
    · rw [kc_RL]; exact ws
    · rw [kc_RR]; exact ws2
    · intro j hj
      exact Function.update_of_ne hj _ _
  have hne1 : ix n hn (s'.val + n - 1) ≠ ix n hn (s.val + 1) :=
    fun h => h2 (kc_val_ix n hn _ _ (kc_LeqR n hn s' s h))
  have hne2 : ix n hn (s'.val + 1) ≠ ix n hn (s.val + 1) :=
    fun h => h1 (kc_R_inj n hn s' s h).symm
  rw [Finset.mem_sdiff, kc_mem_B, kc_mem_B]
  refine ⟨⟨hyI, ?_⟩, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    right
    exact Function.update_self _ _ _
  · intro H
    have hb := H.2 s' (by simp)
    unfold blocked at hb
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2, wL, wR] at hb
    rcases hb with hb | hb <;> exact absurd hb (by decide)

lemma lower32 (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (s s' : Fin n) (h1 : s ≠ s')
    (h2 : s'.val ≠ (s.val + 2) % n) :
    (Iset n hn).card ≤ 32 * (cntB n hn {s} - cntB n hn {s, s'}) := by
  classical
  have c1 := kc_card_upd n (Iset n hn) (ix n hn (s'.val + n - 1)) 0
  have c2 := kc_card_upd n ((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)) (ix n hn (s'.val + 1)) 0
  have c3 := kc_card_upd n (((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)).image
    (fun x => Function.update x (ix n hn (s'.val + 1)) 0)) s 0
  have c4 := kc_card_upd n ((((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)).image
    (fun x => Function.update x (ix n hn (s'.val + 1)) 0)).image
    (fun x => Function.update x s 0)) (ix n hn (s.val + 2)) 0
  have c5 := kc_card_upd n (((((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)).image
    (fun x => Function.update x (ix n hn (s'.val + 1)) 0)).image
    (fun x => Function.update x s 0)).image
    (fun x => Function.update x (ix n hn (s.val + 2)) 0)) (ix n hn (s.val + 1)) 1
  have hsub : ((((((Iset n hn).image
    (fun x => Function.update x (ix n hn (s'.val + n - 1)) 0)).image
    (fun x => Function.update x (ix n hn (s'.val + 1)) 0)).image
    (fun x => Function.update x s 0)).image
    (fun x => Function.update x (ix n hn (s.val + 2)) 0)).image
    (fun x => Function.update x (ix n hn (s.val + 1)) 1)) ⊆
      kc_B n hn {s} \ kc_B n hn {s, s'} := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨w4, ⟨w3, ⟨w2, ⟨w1, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hy
    exact kc_low_mem n hn h6 s s' h1 h2 x hx
  have hsub2 : kc_B n hn {s, s'} ⊆ kc_B n hn {s} := by
    intro x hx
    rw [kc_mem_B] at hx ⊢
    exact ⟨hx.1, fun t ht => hx.2 t (by rw [Finset.mem_singleton] at ht; simp [ht])⟩
  rw [kc_cntB, kc_cntB, ← Finset.card_sdiff_of_subset hsub2]
  have := Finset.card_le_card hsub
  omega

lemma kc_tau_R (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : m ≤ n) (j : Fin n) :
    h3_shift n hn m hm (ix n hn (j.val + 1)) = ix n hn ((h3_shift n hn m hm j).val + 1) := by
  show ix n hn ((ix n hn (j.val + 1)).val + m) = ix n hn ((ix n hn (j.val + m)).val + 1)
  rw [ix_val_add, ix_val_add, add_right_comm]

lemma kc_taui_R (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : m ≤ n) (j : Fin n) :
    (h3_shift n hn m hm).symm (ix n hn (j.val + 1)) =
      ix n hn (((h3_shift n hn m hm).symm j).val + 1) := by
  show ix n hn ((ix n hn (j.val + 1)).val + n - m) = ix n hn ((ix n hn (j.val + n - m)).val + 1)
  rw [h3_ix_shift n hn _ m hm, ix_val_add]
  congr 1
  omega

lemma kc_Iset_comp (n : ℕ) (hn : 0 < n) (σ : Fin n ≃ Fin n)
    (hσ : ∀ j : Fin n, σ (ix n hn (j.val + 1)) = ix n hn ((σ j).val + 1))
    (x : Fin n → ZMod 2) (hx : x ∈ Iset n hn) : x ∘ σ ∈ Iset n hn := by
  rw [kc_mem_Iset] at hx ⊢
  intro j
  simp only [Function.comp]
  rw [hσ]
  exact hx (σ j)

lemma tw_rot (n : ℕ) (hn : 0 < n) (k : ℕ) (z : Fin n → ZMod 2) :
    tw n hn (markT n) (rot n hn k z) = tw n hn (markT n) z := by
  have hm : k % n ≤ n := Nat.le_of_lt (Nat.mod_lt _ hn)
  have hr : rot n hn k z = z ∘ (h3_shift n hn (k % n) hm).symm := rfl
  rw [hr, kc_tw, kc_tw]
  refine Finset.sum_nbij' (fun x => x ∘ (h3_shift n hn (k % n) hm))
    (fun y => y ∘ (h3_shift n hn (k % n) hm).symm) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact kc_Iset_comp n hn _ (kc_tau_R n hn _ hm) x hx
  · intro y hy
    exact kc_Iset_comp n hn _ (kc_taui_R n hn _ hm) y hy
  · intro x _
    funext i
    simp
  · intro y _
    funext i
    simp
  · intro x _
    congr 1
    unfold dot
    rw [← Equiv.sum_comp (h3_shift n hn (k % n) hm)]
    simp

lemma kc_small_r (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (k r : ℕ)
    (hk : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = r ∧ s.val + 2 < n)).card) :
    5 ^ k * |tw n hn (markT n) z| ≤ 4 ^ k * ((Iset n hn).card : ℤ) := by
  obtain ⟨S, hS, hc⟩ := Finset.exists_subset_card_eq hk
  have hmem : ∀ s ∈ S, z s ≠ 0 ∧ s.val % 4 = r ∧ s.val + 2 < n := by
    intro s hs
    have := hS hs
    rw [Finset.mem_filter] at this
    exact this.2
  have hdec := decay n hn h6 S (by
    intro a ha b hb heq
    have h3 := hmem a ha
    have h4 := hmem b hb
    rw [Nat.mod_eq_of_lt (by omega)] at heq
    omega)
  have hsub : S ⊆ Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 2 = r % 2) := by
    intro s hs
    rw [Finset.mem_filter]
    have := hmem s hs
    exact ⟨Finset.mem_univ _, this.1, by omega⟩
  have hab := tw_abs_le n hn h2 z (r % 2)
  have hanti := cntB_anti n hn _ _ hsub
  rw [hc] at hdec
  have hd : (5 : ℤ) ^ k * (cntB n hn S : ℤ) ≤ 4 ^ k * ((Iset n hn).card : ℤ) := by
    exact_mod_cast hdec
  calc (5 : ℤ) ^ k * |tw n hn (markT n) z|
      ≤ 5 ^ k * (cntB n hn (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 2 = r % 2)) : ℤ) :=
        mul_le_mul_of_nonneg_left hab (by positivity)
    _ ≤ 5 ^ k * (cntB n hn S : ℤ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hanti) (by positivity)
    _ ≤ _ := hd

lemma kc_T_card (n : ℕ) :
    (Finset.univ.filter (fun s : Fin n => n ≤ s.val + 2)).card ≤ 2 := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun s : Fin n => n ≤ s.val + 2)) (t := Finset.range 2) (fun s : Fin n => s.val + 2 - n)
    (by
      intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs
      rw [Finset.mem_coe, Finset.mem_range]
      have := s.2
      show s.val + 2 - n < 2
      omega)
    (by
      intro s hs t ht hst
      rw [Finset.mem_coe, Finset.mem_filter] at hs ht
      simp only at hst
      apply Fin.ext
      omega)
  simpa using h

lemma kc_wt_le (n : ℕ) (z : Fin n → ZMod 2) :
    wt n z ≤ (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 0 ∧ s.val + 2 < n)).card +
      (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 1 ∧ s.val + 2 < n)).card +
      (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 2 ∧ s.val + 2 < n)).card +
      (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 3 ∧ s.val + 2 < n)).card + 2 := by
  classical
  have hT := kc_T_card n
  unfold wt
  refine le_trans (Finset.card_le_card (t :=
    (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 0 ∧ s.val + 2 < n)) ∪
    (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 1 ∧ s.val + 2 < n)) ∪
    (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 2 ∧ s.val + 2 < n)) ∪
    (Finset.univ.filter (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 3 ∧ s.val + 2 < n)) ∪
    (Finset.univ.filter (fun s : Fin n => n ≤ s.val + 2))) ?_) ?_
  · intro s hs
    rw [Finset.mem_filter] at hs
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : s.val + 2 < n
    · have h4 : s.val % 4 = 0 ∨ s.val % 4 = 1 ∨ s.val % 4 = 2 ∨ s.val % 4 = 3 := by omega
      rcases h4 with h4 | h4 | h4 | h4 <;> simp [hs.2, h4, hlt]
    · right
      omega
  · refine le_trans (Finset.card_union_le _ _) ?_
    refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Finset.card_union_le _ _) _) _) _) ?_
    omega

lemma tw_small (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (h2 : 2 ∣ n) (z : Fin n → ZMod 2) (k : ℕ)
    (hz : 4 * k + 2 ≤ wt n z) :
    5 ^ k * |tw n hn (markT n) z| ≤ 4 ^ k * ((Iset n hn).card : ℤ) := by
  have hw := kc_wt_le n z
  by_cases c0 : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 0 ∧ s.val + 2 < n)).card
  · exact kc_small_r n hn h6 h2 z k 0 c0
  by_cases c1 : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 1 ∧ s.val + 2 < n)).card
  · exact kc_small_r n hn h6 h2 z k 1 c1
  by_cases c2 : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 2 ∧ s.val + 2 < n)).card
  · exact kc_small_r n hn h6 h2 z k 2 c2
  by_cases c3 : k ≤ (Finset.univ.filter
      (fun s : Fin n => z s ≠ 0 ∧ s.val % 4 = 3 ∧ s.val + 2 < n)).card
  · exact kc_small_r n hn h6 h2 z k 3 c3
  omega

end PEqualNP.Outside.L_meta_33628_aux

namespace PEqualNP.Outside.L_meta_33628_aux

def cl_gg (c : C4) (a : ℕ) : ZMod 2 :=
  c.1 * h3_b 0 a + c.2.1 * h3_b 1 a + c.2.2.1 * h3_b 2 a + c.2.2.2 * h3_b 3 a

lemma cl_gg_mod (c : C4) (a : ℕ) : cl_gg c (a % 6) = cl_gg c a := by
  unfold cl_gg
  rw [h3_b_mod, h3_b_mod, h3_b_mod, h3_b_mod]

lemma cl_gg_congr (c : C4) (a b : ℕ) (h : a % 6 = b % 6) : cl_gg c a = cl_gg c b := by
  rw [← cl_gg_mod c a, ← cl_gg_mod c b, h]

lemma cl_bc_ix (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (c : C4) (a : ℕ) :
    bc n c (ix n hn a) = cl_gg c a := by
  unfold bc cl_gg
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h3_base_ix n hn h6]

lemma cl_bc_apply (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (c : C4) (i : Fin n) :
    bc n c i = cl_gg c i.val := by
  rw [← cl_bc_ix n hn h6, ix_self]

lemma cl_bc_zero (n : ℕ) : bc n 0 = 0 := by
  unfold bc
  funext i
  simp

lemma cl_pat : ∀ c : C4, c ≠ 0 → ∃ r1 r2 : Fin 6, r1 ≠ r2 ∧ cl_gg c r1.val ≠ 0 ∧
    cl_gg c r2.val ≠ 0 := by
  unfold cl_gg h3_b
  decide

lemma cl_shift : ∀ c : C4, ∀ d : Fin 6, ∃ c' : C4, ∀ r : Fin 6,
    cl_gg c' r.val = cl_gg c (r.val + 6 - d.val) := by
  unfold cl_gg h3_b
  decide

lemma cl_wt_tri (n : ℕ) (a b : Fin n → ZMod 2) : wt n a ≤ wt n (a + b) + wt n b := by
  unfold wt
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.add_apply] at hi ⊢
  by_cases hb : b i = 0
  · left
    rw [hb, add_zero]
    exact hi
  · right
    exact hb

lemma cl_wt_es0 (n : ℕ) (hn : 0 < n) : wt n (es n 0) ≤ 1 := by
  unfold wt
  have h : Finset.univ.filter (fun i => es n 0 i ≠ 0) ⊆ {(⟨0, hn⟩ : Fin n)} := by
    intro i hi
    have hi2 := (Finset.mem_filter.1 hi).2
    simp only [Finset.mem_singleton, Fin.ext_iff]
    by_contra h
    exact hi2 (by simp only [es]; exact if_neg h)
  exact le_trans (Finset.card_le_card h) (by simp)

lemma cl_wt_bc (n t : ℕ) (hn : 0 < n) (hnt : n = 6 * t) (c : C4) (hc : c ≠ 0) :
    2 * t ≤ wt n (bc n c) := by
  have h6 : 6 ∣ n := ⟨t, hnt⟩
  obtain ⟨r1, r2, hr, h1, h2⟩ := cl_pat c hc
  have hr' : r1.val ≠ r2.val := fun h => hr (Fin.ext h)
  have r1l := r1.isLt
  have r2l := r2.isLt
  let g : ℕ → ℕ := fun k => if k < t then 6 * k + r1.val else 6 * (k - t) + r2.val
  have hg : ∀ k ∈ Finset.range (2 * t), g k < n := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [g]
    split_ifs <;> omega
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range (2 * t))
    (t := Finset.univ.filter (fun i => bc n c i ≠ 0)) (fun k => ix n hn (g k)) ?_ ?_
  · rw [Finset.card_range] at hcard
    exact hcard
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [cl_bc_ix n hn h6]
    simp only [g]
    split_ifs
    · rw [cl_gg_congr c _ r1.val (by omega)]
      exact h1
    · rw [cl_gg_congr c _ r2.val (by omega)]
      exact h2
  · intro k hk k' hk' he
    have a1 := hg k hk
    have a2 := hg k' hk'
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    have := (ix_eq_iff n hn _ _).1 he
    rw [Nat.mod_eq_of_lt a1, Nat.mod_eq_of_lt a2] at this
    simp only [g] at this
    split_ifs at this <;> omega

lemma cl_rot_add (n : ℕ) (hn : 0 < n) (k : ℕ) (a b : Fin n → ZMod 2) :
    rot n hn k (a + b) = rot n hn k a + rot n hn k b := by
  funext i
  rfl

lemma cl_rot_bc (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (k : ℕ) (c : C4) :
    ∃ c' : C4, bc n c' = rot n hn k (bc n c) ∧ ∀ r : Fin 6,
      cl_gg c' r.val = cl_gg c (r.val + 6 - k % 6) := by
  obtain ⟨c', hc'⟩ := cl_shift c ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩
  refine ⟨c', ?_, hc'⟩
  funext i
  unfold rot
  rw [cl_bc_apply n hn h6, cl_bc_ix n hn h6]
  have hkn : k % n < n := Nat.mod_lt _ hn
  have hk6 : k % n % 6 = k % 6 := Nat.mod_mod_of_dvd k h6
  obtain ⟨t, ht⟩ := h6
  rw [← cl_gg_mod c' i.val]
  have hi6 := hc' ⟨i.val % 6, Nat.mod_lt _ (by norm_num)⟩
  simp only at hi6
  rw [hi6]
  apply cl_gg_congr
  have := i.isLt
  omega

lemma cl_SigB_rot (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (k : ℕ) (w : Fin n → ZMod 2) :
    SigB n hn (rot n hn k w) = SigB n hn w := by
  choose σ hσ1 hσ2 using cl_rot_bc n hn h6 k
  have hinj : Function.Injective σ := by
    intro c1 c2 he
    apply bc_inj n hn h6
    funext i
    rw [cl_bc_apply n hn h6, cl_bc_apply n hn h6]
    have key := fun r : Fin 6 => (hσ2 c1 r).symm.trans ((congrArg (fun c => cl_gg c r.val) he).trans (hσ2 c2 r))
    have hr := key ⟨(i.val % 6 + k % 6) % 6, Nat.mod_lt _ (by norm_num)⟩
    simp only at hr
    rw [cl_gg_congr c1 i.val _ (show i.val % 6 = ((i.val % 6 + k % 6) % 6 + 6 - k % 6) % 6 by omega),
      cl_gg_congr c2 i.val _ (show i.val % 6 = ((i.val % 6 + k % 6) % 6 + 6 - k % 6) % 6 by omega)]
    exact hr
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.1 hinj
  unfold SigB
  rw [← Equiv.sum_comp (Equiv.ofBijective σ hbij)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [Equiv.ofBijective_apply]
  rw [hσ1, ← cl_rot_add, tw_rot]

lemma cl_es_rot (n : ℕ) (hn : 0 < n) (s : Fin n) : rot n hn s.val (es n 0) = es n s.val := by
  funext i
  unfold rot es
  rw [ix_val, Nat.mod_eq_of_lt s.isLt]
  have hi := i.isLt
  have hs := s.isLt
  have e : (i.val + n - s.val) % n = 0 ↔ i.val = s.val := by
    rcases Nat.lt_or_ge (i.val + n - s.val) n with h | h
    · rw [Nat.mod_eq_of_lt h]
      omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      omega
  by_cases h : i.val = s.val
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h]

lemma cl_tw_es (n : ℕ) (hn : 0 < n) (h2 : 2 ∣ n) (s : Fin n) :
    tw n hn (markT n) (es n s.val) = (cntB n hn {s} : ℤ) := by
  have hsupp : Finset.univ.filter (fun i => es n s.val i ≠ 0) = {s} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and, es, Fin.ext_iff]
    split_ifs <;> simp_all
  rw [tw_pure n hn h2 (es n s.val) (s.val % 2), hsupp]
  intro i hi
  have : i.val = s.val := by
    by_contra h
    exact hi (by simp only [es]; simp [h])
  rw [this]

lemma cl_tw_es_eq (n : ℕ) (hn : 0 < n) (s : Fin n) :
    tw n hn (markT n) (es n s.val) = tw n hn (markT n) (es n 0) := by
  rw [← cl_es_rot n hn s, tw_rot]

lemma cl_SB (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Ssum n hn (markT n) (Bsp n) = SigB n hn 0 := by
  rw [Ssum_Bsp n hn h6]
  unfold SigB
  simp only [add_zero]

lemma cl_SS (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (u : Fin n → ZMod 2) (hu : u ∉ Bsp n) :
    Ssum n hn (markT n) (Bsp n ⊔ Submodule.span (ZMod 2) {u}) = SigB n hn 0 + SigB n hn u := by
  rw [Ssum_sup n hn h6 _ u hu, Finset.sum_add_distrib]
  unfold SigB
  simp only [add_zero]

lemma cl_SD0 (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Ssum n hn (markT n) (D0 n) = SigB n hn 0 + SigB n hn (es n 0) := by
  unfold D0
  exact cl_SS n hn h6 _ (es0_not_mem n hn h6)

lemma cl_split (n : ℕ) (hn : 0 < n) (w : Fin n → ZMod 2) :
    SigB n hn w = tw n hn (markT n) w +
      ∑ c ∈ (Finset.univ : Finset C4).erase 0, tw n hn (markT n) (bc n c + w) := by
  unfold SigB
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : C4)), cl_bc_zero, zero_add]

lemma cl_err (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (h2 : 2 ∣ n) (w : Fin n → ZMod 2)
    (hw : ∀ c : C4, c ≠ 0 → 238 ≤ wt n (bc n c + w)) :
    (5 : ℤ) ^ 59 * |SigB n hn w - tw n hn (markT n) w| ≤
      16 * 4 ^ 59 * ((Iset n hn).card : ℤ) := by
  rw [cl_split, add_sub_cancel_left]
  have hI : (0 : ℤ) ≤ 4 ^ 59 * ((Iset n hn).card : ℤ) := by positivity
  have hcard : (((Finset.univ : Finset C4).erase 0).card : ℤ) ≤ 16 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    decide
  calc (5 : ℤ) ^ 59 * |∑ c ∈ (Finset.univ : Finset C4).erase 0, tw n hn (markT n) (bc n c + w)|
      ≤ (5 : ℤ) ^ 59 * ∑ c ∈ (Finset.univ : Finset C4).erase 0, |tw n hn (markT n) (bc n c + w)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∑ c ∈ (Finset.univ : Finset C4).erase 0, (5 : ℤ) ^ 59 * |tw n hn (markT n) (bc n c + w)| :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ c ∈ (Finset.univ : Finset C4).erase 0, (4 : ℤ) ^ 59 * ((Iset n hn).card : ℤ) := by
        refine Finset.sum_le_sum (fun c hc => ?_)
        exact tw_small n hn h6 h2 _ 59 (hw c (Finset.ne_of_mem_erase hc))
    _ = (((Finset.univ : Finset C4).erase 0).card : ℤ) * (4 ^ 59 * ((Iset n hn).card : ℤ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 16 * 4 ^ 59 * ((Iset n hn).card : ℤ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hcard hI

lemma cl_lower (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (h2 : 2 ∣ n) :
    ((Iset n hn).card : ℤ) ≤ 32 * tw n hn (markT n) (es n 0) := by
  have h := lower32 n hn h6 ⟨0, hn⟩ ⟨4, by omega⟩ (by simp [Fin.ext_iff])
    (by simp only; rw [Nat.mod_eq_of_lt (by omega)]; omega)
  have h' : (Iset n hn).card ≤ 32 * cntB n hn {(⟨0, hn⟩ : Fin n)} :=
    le_trans h (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have e := cl_tw_es n hn h2 ⟨0, hn⟩
  simp only at e
  rw [e]
  exact_mod_cast h'

lemma cl_mod2 (n x : ℕ) (hx : x < n) (h6 : 6 ≤ n) :
    (x + 2) % n = if x + 2 < n then x + 2 else x + 2 - n := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma cl_pick (n : ℕ) (h6 : 6 ≤ n) (a b : Fin n) :
    b.val ≠ (a.val + 2) % n ∨ a.val ≠ (b.val + 2) % n := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  rw [cl_mod2 n _ a.isLt h6] at h1
  rw [cl_mod2 n _ b.isLt h6] at h2
  have := a.isLt
  have := b.isLt
  split_ifs at h1 h2 <;> omega

lemma cl_pure_bound (n : ℕ) (hn : 0 < n) (h6 : 6 ≤ n) (h2 : 2 ∣ n) (u : Fin n → ZMod 2) (p : ℕ)
    (hp : ∀ s, u s ≠ 0 → s.val % 2 = p) (hw : 2 ≤ wt n u) :
    32 * tw n hn (markT n) u + ((Iset n hn).card : ℤ) ≤ 32 * tw n hn (markT n) (es n 0) := by
  have key : ∀ s s' : Fin n, s ≠ s' → s'.val ≠ (s.val + 2) % n →
      s ∈ Finset.univ.filter (fun i => u i ≠ 0) → s' ∈ Finset.univ.filter (fun i => u i ≠ 0) →
      32 * tw n hn (markT n) u + ((Iset n hn).card : ℤ) ≤ 32 * tw n hn (markT n) (es n 0) := by
    intro s s' hne hs2 hs hs'
    have l32 := lower32 n hn h6 s s' hne hs2
    have a1 := cntB_anti n hn {s, s'} (Finset.univ.filter (fun i => u i ≠ 0)) (by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx <;> rw [hx] <;> assumption)
    have a2 := cntB_anti n hn {s} {s, s'} (by simp)
    have l32' : ((Iset n hn).card : ℤ) ≤
        32 * ((cntB n hn {s} : ℤ) - (cntB n hn {s, s'} : ℤ)) := by
      have : ((cntB n hn {s} - cntB n hn {s, s'} : ℕ) : ℤ) =
          (cntB n hn {s} : ℤ) - (cntB n hn {s, s'} : ℤ) := Nat.cast_sub a2
      rw [← this]
      exact_mod_cast l32
    have a1' : (cntB n hn (Finset.univ.filter (fun i => u i ≠ 0)) : ℤ) ≤
        (cntB n hn {s, s'} : ℤ) := by exact_mod_cast a1
    rw [tw_pure n hn h2 u p hp, ← cl_tw_es_eq n hn s, cl_tw_es n hn h2 s]
    linarith
  have hc : 1 < (Finset.univ.filter (fun i => u i ≠ 0)).card := hw
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hc
  rcases cl_pick n h6 a b with h | h
  · exact key a b hab h ha hb
  · exact key b a (Ne.symm hab) h hb ha

lemma cl_hw_es (n t : ℕ) (hn : 0 < n) (hnt : n = 6 * t) (h240 : 240 ≤ t) :
    ∀ c : C4, c ≠ 0 → 238 ≤ wt n (bc n c + es n 0) := by
  intro c hc
  have h1 := cl_wt_bc n t hn hnt c hc
  have h2 := cl_wt_tri n (bc n c) (es n 0)
  have h3 := cl_wt_es0 n hn
  omega

lemma cl_hw_u (n t : ℕ) (hn : 0 < n) (hnt : n = 6 * t) (h240 : 240 ≤ t) (u : Fin n → ZMod 2)
    (hmin : ∀ c : C4, wt n u ≤ wt n (bc n c + u)) :
    ∀ c : C4, c ≠ 0 → 238 ≤ wt n (bc n c + u) := by
  intro c hc
  have h1 := cl_wt_bc n t hn hnt c hc
  have h2 := cl_wt_tri n (bc n c) u
  have h3 := hmin c
  omega

lemma cl_es0_nonneg (n t : ℕ) (hn : 0 < n) (hnt : n = 6 * t) (h240 : 240 ≤ t) :
    0 ≤ SigB n hn (es n 0) := by
  have h6 : 6 ≤ n := by omega
  have h2 : 2 ∣ n := ⟨3 * t, by omega⟩
  have hE := cl_err n hn h6 h2 _ (cl_hw_es n t hn hnt h240)
  have hL := cl_lower n hn h6 h2
  set A : ℤ := 5 ^ 59 with hA
  set Bq : ℤ := 4 ^ 59 with hBq
  have hAB : 2048 * Bq ≤ A := by rw [hA, hBq]; norm_num
  have hB0 : 0 ≤ Bq := by positivity
  set T0 := tw n hn (markT n) (es n 0)
  set E0 := SigB n hn (es n 0) - T0
  set I : ℤ := ((Iset n hn).card : ℤ)
  have hI0 : 0 ≤ I := by positivity
  have hT0 : 0 ≤ T0 := by linarith
  have k1 : Bq * I ≤ Bq * (32 * T0) := mul_le_mul_of_nonneg_left hL hB0
  have k2 : 0 ≤ (A - 512 * Bq) * T0 := mul_nonneg (by linarith) hT0
  have k3 : A * (-E0) ≤ A * |E0| :=
    mul_le_mul_of_nonneg_left (neg_le_abs E0) (by positivity)
  have k4 : A * 0 ≤ A * SigB n hn (es n 0) := by
    have : SigB n hn (es n 0) = T0 + E0 := by ring
    rw [this]
    nlinarith
  exact le_of_mul_le_mul_left k4 (by positivity)

lemma cl_ineq (n t : ℕ) (hn : 0 < n) (hnt : n = 6 * t) (h240 : 240 ≤ t) (u : Fin n → ZMod 2)
    (p : ℕ) (hp : ∀ s, u s ≠ 0 → s.val % 2 = p)
    (hmin : ∀ c : C4, wt n u ≤ wt n (bc n c + u)) (hw : 2 ≤ wt n u) :
    SigB n hn u ≤ SigB n hn (es n 0) := by
  have h6 : 6 ≤ n := by omega
  have h2 : 2 ∣ n := ⟨3 * t, by omega⟩
  have hE := cl_err n hn h6 h2 _ (cl_hw_es n t hn hnt h240)
  have hEu := cl_err n hn h6 h2 _ (cl_hw_u n t hn hnt h240 u hmin)
  have hP := cl_pure_bound n hn h6 h2 u p hp hw
  set A : ℤ := 5 ^ 59 with hA
  set Bq : ℤ := 4 ^ 59 with hBq
  have hAB : 2048 * Bq ≤ A := by rw [hA, hBq]; norm_num
  have hB0 : 0 ≤ Bq := by positivity
  set T0 := tw n hn (markT n) (es n 0)
  set E0 := SigB n hn (es n 0) - T0
  set Tu := tw n hn (markT n) u
  set Eu := SigB n hn u - Tu
  set I : ℤ := ((Iset n hn).card : ℤ)
  have hI0 : 0 ≤ I := by positivity
  have k1 : A * Eu ≤ A * |Eu| := mul_le_mul_of_nonneg_left (le_abs_self Eu) (by positivity)
  have k2 : A * (-E0) ≤ A * |E0| := mul_le_mul_of_nonneg_left (neg_le_abs E0) (by positivity)
  have k3 : (2048 * Bq) * I ≤ A * I := mul_le_mul_of_nonneg_right hAB hI0
  have k4 : A * (32 * (Eu - E0)) ≤ A * I := by nlinarith
  have k5 : 32 * (Eu - E0) ≤ I := le_of_mul_le_mul_left k4 (by positivity)
  have e1 : SigB n hn u = Tu + Eu := by ring
  have e2 : SigB n hn (es n 0) = T0 + E0 := by ring
  rw [e1, e2]
  linarith

lemma cl_wt_lt (n : ℕ) (u v : Fin n → ZMod 2) (hsub : ∀ i, v i ≠ 0 → u i ≠ 0) (i0 : Fin n)
    (h0 : u i0 ≠ 0) (h1 : v i0 = 0) : wt n v < wt n u := by
  unfold wt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i0, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h0⟩
    · rw [Finset.mem_filter]
      exact fun h => h.2 h1
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hsub i hi.2⟩

lemma cl_finrankB (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Module.finrank (ZMod 2) (Bsp n) = 4 := by
  unfold Bsp
  rw [finrank_span_eq_card (h3_base_li n hn h6)]
  simp

lemma cl_D_eq (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hB : Bsp n ≤ D) (hf : Module.finrank (ZMod 2) D ≤ 1 + 4) (u : Fin n → ZMod 2)
    (huD : u ∈ D) (huB : u ∉ Bsp n) : Bsp n ⊔ Submodule.span (ZMod 2) {u} = D := by
  have hle : Bsp n ⊔ Submodule.span (ZMod 2) {u} ≤ D :=
    sup_le hB ((Submodule.span_singleton_le_iff_mem u D).2 huD)
  have hlt : Bsp n < Bsp n ⊔ Submodule.span (ZMod 2) {u} := by
    refine lt_of_le_of_ne le_sup_left (fun h => huB ?_)
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [cl_finrankB n hn h6] at h1
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

lemma cl_pure (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (he : ∀ z ∈ D, even n z ∈ D) (u : Fin n → ZMod 2) (huD : u ∈ D) (huB : u ∉ Bsp n)
    (hmin : ∀ z ∈ D, z ∉ Bsp n → wt n u ≤ wt n z) :
    ∃ p : ℕ, ∀ s, u s ≠ 0 → s.val % 2 = p := by
  by_contra h
  push_neg at h
  obtain ⟨s0, hs0, hs0p⟩ := h 0
  obtain ⟨s1, hs1, hs1p⟩ := h 1
  have hlt1 : wt n (even n u) < wt n u := by
    refine cl_wt_lt n u _ ?_ s0 hs0 ?_
    · intro i hi
      rw [even_apply] at hi
      split_ifs at hi
      · exact hi
      · exact absurd rfl hi
    · rw [even_apply, if_neg hs0p]
  have hlt2 : wt n (u + even n u) < wt n u := by
    refine cl_wt_lt n u _ ?_ s1 hs1 ?_
    · intro i hi
      rw [Pi.add_apply, even_apply] at hi
      split_ifs at hi
      · exact absurd (z2_add_self _) hi
      · simpa using hi
    · rw [Pi.add_apply, even_apply, if_pos (by omega), z2_add_self]
  have hD1 : even n u ∈ D := he u huD
  have hD2 : u + even n u ∈ D := D.add_mem huD hD1
  by_cases hB1 : even n u ∈ Bsp n
  · have hB2 : u + even n u ∉ Bsp n := by
      intro hB2
      apply huB
      have := (Bsp n).add_mem hB2 hB1
      rwa [add_assoc, fn_add_self, add_zero] at this
    exact absurd (hmin _ hD2 hB2) (by omega)
  · exact absurd (hmin _ hD1 hB1) (by omega)

lemma cl_wt1 (n : ℕ) (u : Fin n → ZMod 2) (hw : wt n u = 1) : ∃ s : Fin n, u = es n s.val := by
  obtain ⟨s, hs⟩ := Finset.card_eq_one.1 hw
  refine ⟨s, ?_⟩
  funext i
  have hi : u i ≠ 0 ↔ i = s := by
    rw [← Finset.mem_singleton, ← hs, Finset.mem_filter]
    simp
  unfold es
  by_cases h : i = s
  · rw [if_pos (congrArg Fin.val h)]
    rcases z2_cases (u i) with h' | h'
    · exact absurd h' (hi.2 h)
    · exact h'
  · rw [if_neg (fun h' => h (Fin.ext h'))]
    by_contra h'
    exact h (hi.1 h')

lemma classify (n t : ℕ) (hn : 0 < n) (hnt : n = 6 * t) (h240 : 240 ≤ t)
    (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hb : ∀ j, base n j ∈ D) (he : ∀ z ∈ D, even n z ∈ D)
    (hf : Module.finrank (ZMod 2) D ≤ 1 + 4) :
    Ssum n hn (markT n) D ≤ Ssum n hn (markT n) (D0 n) := by
  classical
  have h6 : 6 ∣ n := ⟨t, hnt⟩
  have hB : Bsp n ≤ D := by
    unfold Bsp
    rw [Submodule.span_le, Set.range_subset_iff]
    exact hb
  rw [cl_SD0 n hn h6]
  by_cases hall : ∀ z ∈ D, z ∈ Bsp n
  · have hD : D = Bsp n := le_antisymm (fun z hz => hall z hz) hB
    rw [hD, cl_SB n hn h6]
    linarith [cl_es0_nonneg n t hn hnt h240]
  · push_neg at hall
    obtain ⟨z, hzD, hzB⟩ := hall
    obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun z => z ∈ D ∧ z ∉ Bsp n)) (wt n)
      ⟨z, Finset.mem_filter.2 ⟨Finset.mem_univ _, hzD, hzB⟩⟩
    obtain ⟨huD, huB⟩ := (Finset.mem_filter.1 hu).2
    have hmin' : ∀ z ∈ D, z ∉ Bsp n → wt n u ≤ wt n z :=
      fun z h1 h2 => hmin z (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩)
    have hminc : ∀ c : C4, wt n u ≤ wt n (bc n c + u) := by
      intro c
      refine hmin' _ (D.add_mem (hB (bc_mem n c)) huD) (fun h => huB ?_)
      have := (Bsp n).add_mem (bc_mem n c) h
      rwa [← add_assoc, fn_add_self, zero_add] at this
    rw [← cl_D_eq n hn h6 D hB hf u huD huB, cl_SS n hn h6 u huB]
    obtain ⟨p, hp⟩ := cl_pure n D he u huD huB hmin'
    rcases Nat.lt_or_ge (wt n u) 2 with hw | hw
    · have hw1 : wt n u = 1 := by
        have : wt n u ≠ 0 := by
          intro h0
          apply huB
          have : u = 0 := by
            funext i
            by_contra hi
            have : 0 < wt n u := Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
            omega
          rw [this]
          exact (Bsp n).zero_mem
        omega
      obtain ⟨s, hs⟩ := cl_wt1 n u hw1
      rw [hs, ← cl_es_rot n hn s, cl_SigB_rot n hn h6]
    · linarith [cl_ineq n t hn hnt h240 u p hp hminc hw]

end PEqualNP.Outside.L_meta_33628_aux

namespace PEqualNP.Outside.L_meta_33628_aux

noncomputable def gl_phi (n : ℕ) (hn : 0 < n) : Fin 1 → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  fun _ => (dotL n (es n 0)).comp (mixL n hn)

lemma gl_ix0 (n : ℕ) (hn : 0 < n) : (ix n hn 0).val = 0 := by
  simp [ix]

lemma gl_dot_es0 (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) :
    dot n (es n 0) x = x (ix n hn 0) := by
  unfold dot es
  rw [Finset.sum_eq_single (ix n hn 0)]
  · simp [gl_ix0 n hn]
  · intro i _ hi
    have h : i.val ≠ 0 := by
      intro h
      apply hi
      ext
      rw [h, gl_ix0 n hn]
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma gl_phi_apply (n : ℕ) (hn : 0 < n) (j : Fin 1) (w : Fin n → ZMod 2) :
    gl_phi n hn j w = mix n hn w (ix n hn 0) := by
  show dot n (mix n hn w) (es n 0) = _
  rw [dot_comm, gl_dot_es0]

lemma gl_phi_dot (n : ℕ) (hn : 0 < n) (j : Fin 1) (w : Fin n → ZMod 2) :
    gl_phi n hn j w = dot n ((fun _ : Fin 1 => es n 0) j) (mix n hn w) := by
  show dot n (mix n hn w) (es n 0) = _
  rw [dot_comm]

lemma gl_memK (n : ℕ) (hn : 0 < n) (w : Fin n → ZMod 2) :
    w ∈ LinearMap.ker (LinearMap.pi (gl_phi n hn)) ↔ mix n hn w (ix n hn 0) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h1 := congrFun h 0
    rwa [LinearMap.pi_apply, gl_phi_apply] at h1
  · intro h
    funext j
    rw [LinearMap.pi_apply, gl_phi_apply]
    exact h

lemma gl_orth_mix (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    orth n ((mixL n hn).comp (LinearMap.ker (LinearMap.pi (gl_phi n hn))).subtype) = D0 n := by
  refine h6_orth_eq n hn h6 1 (D0 n) ?_ (fun _ => es n 0) ?_ ?_ (gl_phi n hn)
    (gl_phi_dot n hn)
  · intro j
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)
  · intro j
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  · unfold D0 Bsp
    refine sup_le_sup_left ?_ _
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Submodule.subset_span ⟨0, rfl⟩

lemma gl_orth_tau (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    orth n (h5_tau n hn (LinearMap.ker (LinearMap.pi (gl_phi n hn)))) = D0 n := by
  apply le_antisymm
  · rw [← gl_orth_mix n hn h6]
    intro z hz
    rw [mem_orth] at hz ⊢
    intro u
    show dot n z (mix n hn u.1) = 0
    have h1 := hz (u, 0)
    rw [h5_tau_apply] at h1
    simp only [ZeroMemClass.coe_zero, mix_zero, add_zero] at h1
    have hyb : ∀ j, dot n (base n j) (mix n hn u.1 + even n (mix n hn u.1)) = 0 := by
      intro j
      rw [dot_add_right, base_dot_mix n hn h6, ← dot_even]
      rcases even_base n j with h | h
      · rw [h, base_dot_mix n hn h6, add_zero]
      · rw [h, dot_zero_left, add_zero]
    obtain ⟨w, hw⟩ := mix_surj n hn h6 _ hyb
    have hwK : w ∈ LinearMap.ker (LinearMap.pi (gl_phi n hn)) := by
      rw [gl_memK, hw, Pi.add_apply, even_apply, gl_ix0 n hn, if_pos rfl]
      exact z2_add_self _
    have hwZ : w ∈ h5_KZ n hn (LinearMap.ker (LinearMap.pi (gl_phi n hn))) := by
      rw [h5_mem_KZ]
      refine ⟨hwK, ?_⟩
      rw [hw, even_add, even_even]
      exact fn_add_self n _
    have h2 := hz (0, ⟨w, hwZ⟩)
    rw [h5_tau_apply] at h2
    simp only [ZeroMemClass.coe_zero, mix_zero, even_zero, zero_add] at h2
    rw [hw] at h2
    have e : mix n hn u.1 = even n (mix n hn u.1) + (mix n hn u.1 + even n (mix n hn u.1)) := by
      rw [add_comm (mix n hn u.1), ← add_assoc, fn_add_self, zero_add]
    rw [e, dot_add_right, h1, h2, add_zero]
  · unfold D0 Bsp
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact h5_base_mem n hn h6 _ j
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, mem_orth]
      intro u
      have hu1 := (gl_memK n hn _).1 u.1.2
      have hu2 := (gl_memK n hn _).1 ((h5_mem_KZ n hn _ _).1 u.2.2).1
      rw [h5_tau_apply, dot_add_right, gl_dot_es0 n hn, gl_dot_es0 n hn, even_apply,
        gl_ix0 n hn, if_pos rfl, hu1, hu2, add_zero]

lemma gl_cell_count (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (mark : Fin n → Bool)
    (name c : Fin n → ZMod 2) (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (w0 : Fin n → ZMod 2) (A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : Fin n → ZMod 2) :
      (2:ℤ)^n * (Nat.card {k : K // ∀ i, mark i = true →
        out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
          (A (w0 + (k : Fin n → ZMod 2)) + b) i} : ℤ) ≤
      (Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K)) := by
  obtain ⟨L, c0, hL⟩ := out_affine n hn name c
  have h2 : 2 ∣ n := Dvd.dvd.trans (by norm_num) h6
  have hp := h5_pairs n hn h2 mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A)
  have hf := fourier_count n hn mark (h5_tau n hn K)
  rw [Nat.card_prod] at hf
  rw [h5_good n hn mark name c K w0 A L b c0 hL]
  have hpos : (0:ℤ) < (Nat.card (h5_KZ n hn K) : ℤ) := Nat.cast_pos.mpr Nat.card_pos
  have hp' : (Nat.card (h5_KZ n hn K) : ℤ) *
      (Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ)
      ≤ (Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} : ℤ) := by
    exact_mod_cast hp
  have h3 : (Nat.card (h5_KZ n hn K) : ℤ) * ((2:ℤ)^n *
      (Nat.card {k : ↥K // h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ))
      ≤ (Nat.card (h5_KZ n hn K) : ℤ) *
        ((Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K))) := by
    calc (Nat.card (h5_KZ n hn K) : ℤ) * ((2:ℤ)^n * (Nat.card {k : ↥K //
          h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ))
        = (2:ℤ)^n * ((Nat.card (h5_KZ n hn K) : ℤ) * (Nat.card {k : ↥K //
          h5_G n hn mark K (mix n hn w0) (L w0 + c0 + A w0 + b) (L + A) k} : ℤ)) := by ring
      _ ≤ (2:ℤ)^n *
          (Nat.card {u : ↥K × ↥(h5_KZ n hn K) // adm n hn mark (h5_tau n hn K u)} : ℤ) :=
        mul_le_mul_of_nonneg_left hp' (by positivity)
      _ = ((Nat.card K * Nat.card (h5_KZ n hn K) : ℕ) : ℤ) *
          Ssum n hn mark (orth n (h5_tau n hn K)) := hf
      _ = (Nat.card (h5_KZ n hn K) : ℤ) *
          ((Nat.card K : ℤ) * Ssum n hn mark (orth n (h5_tau n hn K))) := by
        push_cast
        ring
  exact le_of_mul_le_mul_left h3 hpos

lemma gl_cell (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (name c : Fin n → ZMod 2)
    (A : ZMod 2 → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ZMod 2 → Fin n → ZMod 2)
    (w0 : Fin n → ZMod 2) :
    (2:ℤ)^n * (Nat.card {w : Fin n → ZMod 2 // out n hn name c w =
        A (mix n hn w (ix n hn 0)) w + b (mix n hn w (ix n hn 0)) ∧
        (mix n hn w (ix n hn 0)).val = (mix n hn w0 (ix n hn 0)).val} : ℤ) ≤
      (Nat.card {w : Fin n → ZMod 2 //
        (mix n hn w (ix n hn 0)).val = (mix n hn w0 (ix n hn 0)).val} : ℤ) *
        Ssum n hn (markT n) (D0 n) := by
  have hcc := gl_cell_count n hn h6 (markT n) name c
    (LinearMap.ker (LinearMap.pi (gl_phi n hn))) w0
    (A (mix n hn w0 (ix n hn 0))) (b (mix n hn w0 (ix n hn 0)))
  rw [gl_orth_tau n hn h6] at hcc
  have hK : ∀ w : Fin n → ZMod 2, (mix n hn w (ix n hn 0)).val = (mix n hn w0 (ix n hn 0)).val
      ↔ w - w0 ∈ LinearMap.ker (LinearMap.pi (gl_phi n hn)) := by
    intro w
    rw [gl_memK, mix_sub, Pi.sub_apply, sub_eq_zero]
    exact ⟨fun h => ZMod.val_injective _ h, fun h => by rw [h]⟩
  have hrun : ∀ k : LinearMap.ker (LinearMap.pi (gl_phi n hn)),
      mix n hn (w0 + (k : Fin n → ZMod 2)) (ix n hn 0) = mix n hn w0 (ix n hn 0) := by
    intro k
    have h := (hK (w0 + (k : Fin n → ZMod 2))).2 (by rw [add_sub_cancel_left]; exact k.2)
    exact ZMod.val_injective _ h
  have e2 : Nat.card (LinearMap.ker (LinearMap.pi (gl_phi n hn))) =
      Nat.card {w : Fin n → ZMod 2 //
        (mix n hn w (ix n hn 0)).val = (mix n hn w0 (ix n hn 0)).val} :=
    Nat.card_congr
      { toFun := fun k => ⟨w0 + (k : Fin n → ZMod 2), by rw [hrun k]⟩
        invFun := fun w => ⟨w.1 - w0, (hK _).mp w.2⟩
        left_inv := fun k => Subtype.ext (add_sub_cancel_left _ _)
        right_inv := fun w => Subtype.ext (add_sub_cancel _ _) }
  have e1 : Nat.card {k : LinearMap.ker (LinearMap.pi (gl_phi n hn)) // ∀ i, markT n i = true →
      out n hn name c (w0 + (k : Fin n → ZMod 2)) i =
        (A (mix n hn w0 (ix n hn 0)) (w0 + (k : Fin n → ZMod 2)) +
          b (mix n hn w0 (ix n hn 0))) i} =
      Nat.card {w : Fin n → ZMod 2 // out n hn name c w =
        A (mix n hn w (ix n hn 0)) w + b (mix n hn w (ix n hn 0)) ∧
        (mix n hn w (ix n hn 0)).val = (mix n hn w0 (ix n hn 0)).val} :=
    Nat.card_congr
      { toFun := fun k => ⟨w0 + (k.1 : Fin n → ZMod 2), by
          refine ⟨?_, by rw [hrun k.1]⟩
          rw [hrun k.1]
          funext i
          exact k.2 i rfl⟩
        invFun := fun w => ⟨⟨w.1 - w0, (hK _).mp w.2.2⟩, by
          have hw := w.2.1
          have hq : mix n hn w.1 (ix n hn 0) = mix n hn w0 (ix n hn 0) :=
            ZMod.val_injective _ w.2.2
          rw [hq] at hw
          have hc : w0 + (w.1 - w0) = w.1 := add_sub_cancel _ _
          intro i _
          show out n hn name c (w0 + (w.1 - w0)) i =
            (A (mix n hn w0 (ix n hn 0)) (w0 + (w.1 - w0)) + b (mix n hn w0 (ix n hn 0))) i
          rw [hc]
          exact congrFun hw i⟩
        left_inv := fun k => Subtype.ext (Subtype.ext (add_sub_cancel_left _ _))
        right_inv := fun w => Subtype.ext (add_sub_cancel _ _) }
  rw [← e1, ← e2]
  exact hcc

lemma gl_upper_fixed (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (name c : Fin n → ZMod 2)
    (A : ZMod 2 → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ZMod 2 → Fin n → ZMod 2) :
    (Nat.card {w : Fin n → ZMod 2 // out n hn name c w =
        A (mix n hn w (ix n hn 0)) w + b (mix n hn w (ix n hn 0))} : ℤ) ≤
      Ssum n hn (markT n) (D0 n) := by
  by_contra hcon
  have hW : ((2:ℤ)^n) = (Nat.card (Fin n → ZMod 2) : ℤ) := by
    simp [Nat.card_eq_fintype_card]
  refine h6_fiber_sum (fun w => (mix n hn w (ix n hn 0)).val) (fun w => out n hn name c w =
    A (mix n hn w (ix n hn 0)) w + b (mix n hn w (ix n hn 0))) (fun w0 => ?_)
  have hc := gl_cell n hn h6 name c A b w0
  have hlt := lt_of_not_ge hcon
  rw [← hW]
  refine le_trans hc (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  linarith

lemma gl_bit_cast : ∀ v : ZMod 2, ((h4_bit v : ℕ) : ZMod 2) = v := by
  decide

lemma gl_run1 (n : ℕ) (ask : Fin 1 → ℕ → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (w : Fin n → ZMod 2) : run n 1 ask w = h4_bit (ask 0 0 w) := by
  rw [h4_run_succ]
  have h0 : run n 0 (fun j => ask j.castSucc) w = 0 := by
    unfold run
    simp
  rw [h0]
  simp only [mul_zero, zero_add]
  rfl

lemma gl_lower_fixed (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (name c : Fin n → ZMod 2) :
    ∃ (A : ZMod 2 → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ZMod 2 → Fin n → ZMod 2),
      Ssum n hn (markT n) (D0 n) ≤ (Nat.card {w : Fin n → ZMod 2 // out n hn name c w =
        A (mix n hn w (ix n hn 0)) w + b (mix n hn w (ix n hn 0))} : ℤ) := by
  obtain ⟨A, b, hAb⟩ := nonadaptive_count n hn 1 (markT n) name c (gl_phi n hn)
  refine ⟨fun v => A (h4_bit v), fun v => b (h4_bit v), ?_⟩
  have hF := fourier_count n hn (markT n) ((mixL n hn).comp
    (LinearMap.ker (LinearMap.pi (gl_phi n hn))).subtype)
  rw [gl_orth_mix n hn h6] at hF
  have e : Nat.card {w : Fin n → ZMod 2 // ∀ i, markT n i = true → out n hn name c w i =
        (A (run n 1 (fun j _ => gl_phi n hn j) w) w +
          b (run n 1 (fun j _ => gl_phi n hn j) w)) i} =
      Nat.card {w : Fin n → ZMod 2 // out n hn name c w =
        A (h4_bit (mix n hn w (ix n hn 0))) w + b (h4_bit (mix n hn w (ix n hn 0)))} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
    rw [gl_run1, gl_phi_apply]
    constructor
    · intro h
      funext i
      exact h i rfl
    · intro h i _
      exact congrFun h i
  rw [e] at hAb
  have hAbZ := congrArg (fun k : ℕ => (k : ℤ)) hAb
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hAbZ
  have hEq := hAbZ.trans hF
  have hNpos : (0:ℤ) < (Nat.card (LinearMap.ker (LinearMap.pi (gl_phi n hn))) : ℤ) := by
    exact_mod_cast Nat.card_pos
  exact le_of_eq (mul_left_cancel₀ hNpos.ne' hEq).symm

lemma gl_upper_any (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) (name c : Fin n → ZMod 2)
    (q : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (A : ZMod 2 → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (b : ZMod 2 → Fin n → ZMod 2) :
    ∃ D : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ j, base n j ∈ D) ∧ (∀ z ∈ D, even n z ∈ D) ∧
      Module.finrank (ZMod 2) D ≤ 1 + 4 ∧
      (Nat.card {w : Fin n → ZMod 2 // out n hn name c w = A (q w) w + b (q w)} : ℤ) ≤
        Ssum n hn (markT n) D := by
  obtain ⟨D, h1, h2, h3, h4⟩ := upper n hn h6 1 (markT n) name c (fun _ _ => q)
    (fun m => A (m : ZMod 2)) (fun m => b (m : ZMod 2))
  refine ⟨D, h1, h2, h3, le_trans (le_of_eq ?_) h4⟩
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
  rw [gl_run1]
  show out n hn name c w = A (q w) w + b (q w) ↔ ∀ i, markT n i = true →
    out n hn name c w i = (A ((h4_bit (q w) : ℕ) : ZMod 2) w + b ((h4_bit (q w) : ℕ) : ZMod 2)) i
  rw [gl_bit_cast]
  constructor
  · intro h i _
    exact congrFun h i
  · intro h
    funext i
    exact h i rfl

lemma gl_final0 (t : ℕ) (ht : 0 < t) (name c : Fin (6*t) → ZMod 2) (k : ℕ) (fixed : Bool)
    (hfx : fixed = true ∨ 240 ≤ t) :
    (∃ (q : (Fin (6*t) → ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (A : ZMod 2 → (Fin (6*t) → ZMod 2) →ₗ[ZMod 2] (Fin (6*t) → ZMod 2))
        (b : ZMod 2 → Fin (6*t) → ZMod 2),
      (fixed = true → ∀ w : Fin (6*t) → ZMod 2,
        q w = mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w
          (ix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) 0)) ∧
      k ≤ Nat.card {w : Fin (6*t) → ZMod 2 //
        out (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) name c w = A (q w) w + b (q w)}) ↔
    (k : ℤ) ≤ 2*((((!![0,1;-1,18] : Matrix (Fin 2) (Fin 2) ℤ)^t).mulVec ![1,13]) 0 +
         (((!![0,1;-1,6] : Matrix (Fin 2) (Fin 2) ℤ)^t).mulVec ![6,26]) 0 + 3 +
         (6+4*(t : ℤ))*(-1 : ℤ)^t) := by
  have h6 : 6 ∣ 6*t := Dvd.intro t rfl
  rw [← formula t ht]
  constructor
  · rintro ⟨q, A, b, hq, hk⟩
    rcases hfx with hf | h240
    · have hq' := hq hf
      have e : Nat.card {w : Fin (6*t) → ZMod 2 //
          out (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) name c w = A (q w) w + b (q w)} =
          Nat.card {w : Fin (6*t) → ZMod 2 //
          out (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) name c w =
            A (mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w
              (ix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) 0)) w +
            b (mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w
              (ix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) 0))} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
        rw [hq' w]
      rw [e] at hk
      exact le_trans (Nat.cast_le.mpr hk)
        (gl_upper_fixed (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) h6 name c A b)
    · obtain ⟨D, h1, h2, h3, h4⟩ :=
        gl_upper_any (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) h6 name c q A b
      exact le_trans (Nat.cast_le.mpr hk) (le_trans h4
        (classify (6*t) t (Nat.mul_pos (Nat.zero_lt_succ 5) ht) rfl h240 D h1 h2 h3))
  · intro hk
    obtain ⟨A, b, hAb⟩ :=
      gl_lower_fixed (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) h6 name c
    refine ⟨gl_phi (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) 0, A, b,
      fun _ w => gl_phi_apply _ _ 0 w, ?_⟩
    have e : Nat.card {w : Fin (6*t) → ZMod 2 //
        out (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) name c w =
          A (gl_phi (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) 0 w) w +
          b (gl_phi (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) 0 w)} =
        Nat.card {w : Fin (6*t) → ZMod 2 //
        out (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) name c w =
          A (mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w
            (ix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) 0)) w +
          b (mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w
            (ix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) 0))} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
      rw [gl_phi_apply]
    rw [e]
    exact Nat.cast_le.mp (le_trans hk hAb)

lemma gl_inst (x lo hi : ℤ) (t : ℕ) :
    (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
     (((!![0,1;-1,x] : Matrix (Fin 2) (Fin 2) ℤ)^t).mulVec ![lo,hi]) 0) =
    (((!![0,1;-1,x] : Matrix (Fin 2) (Fin 2) ℤ)^t).mulVec ![lo,hi]) 0 := by
  convert rfl

lemma gl_final (t : ℕ) (ht : 0 < t) (name c : Fin (6*t) → ZMod 2) (k : ℕ) (fixed : Bool)
    (hfx : fixed = true ∨ 240 ≤ t) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    (∃ (q : (Fin (6*t) → ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (A : ZMod 2 → (Fin (6*t) → ZMod 2) →ₗ[ZMod 2] (Fin (6*t) → ZMod 2))
        (b : ZMod 2 → Fin (6*t) → ZMod 2),
      (fixed = true → ∀ w : Fin (6*t) → ZMod 2,
        q w = mix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) w
          (ix (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) 0)) ∧
      k ≤ Nat.card {w : Fin (6*t) → ZMod 2 //
        out (6*t) (Nat.mul_pos (Nat.zero_lt_succ 5) ht) name c w = A (q w) w + b (q w)}) ↔
    (k : ℤ) ≤ 2*((((!![0,1;-1,18] : Matrix (Fin 2) (Fin 2) ℤ)^t).mulVec ![1,13]) 0 +
         (((!![0,1;-1,6] : Matrix (Fin 2) (Fin 2) ℤ)^t).mulVec ![6,26]) 0 + 3 +
         (6+4*(t : ℤ))*(-1 : ℤ)^t) := by
  rw [gl_inst 18 1 13 t, gl_inst 6 6 26 t]
  exact gl_final0 t ht name c k fixed hfx

end PEqualNP.Outside.L_meta_33628_aux

theorem PEqualNP.Outside.L_meta_33628 : (∀ (t : ℕ) (ht : 0 < t),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 5) ht)⟩ : Fin n)
  let rot := fun (s : ℕ) (w : W) (i : Fin n) => w (ix (i.val + n - s % n))
  let out := fun (name c raw : W) (i : Fin n) =>
    let old := rot 3 raw + name
    let y := fun j : Fin n => old j + old (ix (j.val+2)) + old (ix (j.val+n-2))
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2)) + rot 4 raw i + c i
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  ∀ name c : W,
    let hits := fun (q : W →ₗ[F] F) (A : F → W →ₗ[F] W) (b : F → W) =>
      Nat.card {w : W // out name c w = A (q w) w + b (q w)}
    let seq := fun (x lo hi : ℤ) =>
      (((!![0,1;-1,x] : Matrix (Fin 2) (Fin 2) ℤ)^t).mulVec ![lo,hi]) 0
    ∀ (k : ℕ) (fixed : Bool), (fixed = true ∨ 240 ≤ t) →
      ((∃ (q : W →ₗ[F] F) (A : F → W →ₗ[F] W) (b : F → W),
        (fixed = true → ∀ w : W, q w = mix w (ix 0)) ∧ k ≤ hits q A b) ↔
        (k : ℤ) ≤ 2*(seq 18 1 13 + seq 6 6 26 + 3 + (6+4*(t : ℤ))*(-1 : ℤ)^t))) := by
  intro t ht
  exact fun name c k fixed hfx =>
    PEqualNP.Outside.L_meta_33628_aux.gl_final t ht name c k fixed hfx
