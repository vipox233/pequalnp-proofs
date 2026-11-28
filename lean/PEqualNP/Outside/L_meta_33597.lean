import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33597

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

end PEqualNP.Outside.L_meta_33597

theorem PEqualNP.Outside.L_meta_33597 : (∀ (t : ℕ) (ht : 0 < t) (h : ℕ),
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
  let run := fun (ask : Fin h → ℕ → W →ₗ[F] F) (w : W) =>
    (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)
  let base := fun (j : Fin 4) (i : Fin n) =>
    if i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let even := fun (z : W) (i : Fin n) => if i.val % 2 = 0 then z i else 0
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  ∀ (mark : Fin n → Bool) (name c : W) (k : ℕ) (fixed : Bool),
    let traceWord := fun z : W =>
      (List.ofFn (fun i : Fin n =>
        let s : ℤ := if z i = 0 then 1 else -1
        let a : ℤ := if mark (ix (i.val+n-2)) then 0 else s
        (!![1,s;1,a] : Matrix (Fin 2) (Fin 2) ℤ))).prod.trace
    (∃ (ask : Fin h → ℕ → W →ₗ[F] F) (A : ℕ → W →ₗ[F] W) (b : ℕ → W),
      (fixed = true → ∃ v : Fin h → W,
        (∀ j, even (v j) = v j ∨ even (v j) = 0) ∧
        (∀ j p w, ask j p w = ∑ i, v j i * mix w i)) ∧
      k ≤ Nat.card {w : W // ∀ i, mark i = true →
        out name c w i = (A (run ask w) w + b (run ask w)) i}) ↔
    ∃ D : Submodule F W,
      (∀ j, base j ∈ D) ∧ (∀ z ∈ D, even z ∈ D) ∧ Module.finrank F D ≤ h+4 ∧
      (k : ℤ) ≤ ∑ z ∈ (Finset.univ : Finset W).filter (fun z => z ∈ D), traceWord z) := by
  intro t ht h
  exact fun mark name c k fixed =>
    PEqualNP.Outside.L_meta_33597.final t ht h mark name c k fixed
