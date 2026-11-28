import Mathlib
import PEqualNP.Defs

/-
Adapted in part from PEqualNP/Outside/L_meta_33597.lean (Stan Mazhara, PR 44592),
licensed under the Apache License, Version 2.0.
-/

namespace PEqualNP.Outside.L_meta_33638


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


namespace Test33638

-- Minimal interface matching L_meta_33597
def ix (n : ℕ) (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

noncomputable def base (n : ℕ) (j : Fin 4) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2) then (1 : ZMod 2) else 0

noncomputable def even (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = 0 then z i else 0

def sgn (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

def dot (n : ℕ) (z x : Fin n → ZMod 2) : ZMod 2 := ∑ i, z i * x i

def ind (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) : Prop :=
  ∀ i : Fin n, x i * x (ix n hn (i.val + 1)) = 0

noncomputable def tw0 (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∑ x : Fin n → ZMod 2, if ind n hn x then sgn (dot n z x) else 0

noncomputable def S0 (n : ℕ) (hn : 0 < n) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∑ z ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun z => z ∈ D), tw0 n hn z

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma sgn_zero : sgn 0 = 1 := rfl
lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> decide

lemma sgn_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

lemma sgn_abs (x : ZMod 2) : |sgn x| = 1 := by
  fin_cases x <;> decide

-- Basic Fibonacci identities
lemma fib_add_id (a b : ℕ) :
    Nat.fib (a + b + 1) = Nat.fib (a + 1) * Nat.fib (b + 1) + Nat.fib a * Nat.fib b := by
  induction a generalizing b with
  | zero => simp [Nat.fib_zero, Nat.fib_one]
  | succ a ih =>
    have h1 := ih (b + 1)
    rw [show a + (b + 1) + 1 = a + 1 + b + 1 by omega] at h1
    rw [h1, Nat.fib_add_two, Nat.fib_add_two]
    ring

lemma fib_merge_id (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 * Nat.fib (a + b + 1) =
      Nat.fib (a + 2) * Nat.fib (b + 2) + Nat.fib (a - 1) * Nat.fib (b - 1) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hadd := fib_add_id (a' + 1) (b' + 1)
  have ha2 : Nat.fib (a' + 1 + 2) = Nat.fib (a' + 1) + Nat.fib (a' + 2) := Nat.fib_add_two
  have hb2 : Nat.fib (b' + 1 + 2) = Nat.fib (b' + 1) + Nat.fib (b' + 2) := Nat.fib_add_two
  have ha1 : Nat.fib (a' + 2) = Nat.fib a' + Nat.fib (a' + 1) := Nat.fib_add_two
  have hb1 : Nat.fib (b' + 2) = Nat.fib b' + Nat.fib (b' + 1) := Nat.fib_add_two
  simp only [Nat.add_sub_cancel]
  nlinarith

lemma fib_merge_zero (b : ℕ) (hb : 1 ≤ b) :
    2 * Nat.fib (b + 1) = Nat.fib 2 * Nat.fib (b + 2) + Nat.fib (b - 1) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have h2 : Nat.fib 2 = 1 := by decide
  have hb2 : Nat.fib (b' + 1 + 2) = Nat.fib (b' + 1) + Nat.fib (b' + 2) := Nat.fib_add_two
  have hb1 : Nat.fib (b' + 2) = Nat.fib b' + Nat.fib (b' + 1) := Nat.fib_add_two
  have h11 : b' + 1 + 1 = b' + 2 := rfl
  simp only [Nat.add_sub_cancel, h2, h11]
  omega

lemma fib_merge_le (a b : ℕ) :
    Nat.fib (a + 2) * Nat.fib (b + 2) ≤ 2 * Nat.fib (a + b + 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · decide
    · have := fib_merge_zero b hb; simp at this ⊢; omega
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · have := fib_merge_zero a ha; simp at this ⊢; rw [mul_comm]; omega
    · have := fib_merge_id a b ha hb; omega

lemma fib_prod_ge_fib_sum (a b : ℕ) :
    Nat.fib (a + b + 2) ≤ Nat.fib (a + 2) * Nat.fib (b + 2) := by
  have hadd := fib_add_id a (b + 1)
  rw [show a + (b + 1) + 1 = a + b + 2 by omega] at hadd
  have hmono : Nat.fib (b + 1) ≤ Nat.fib (b + 2) := Nat.fib_mono (by omega)
  have ha2 : Nat.fib (a + 2) = Nat.fib a + Nat.fib (a + 1) := Nat.fib_add_two
  nlinarith

lemma fib_mul_ge (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    Nat.fib (u + v - 2) ≤ Nat.fib u * Nat.fib v := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    rcases eq_or_lt_of_le hu with rfl | hu2
    · simp only [Nat.fib_one, one_mul]
      exact Nat.fib_mono (by omega)
    · rcases eq_or_lt_of_le (show 2 ≤ u by omega) with rfl | hu3
      · have h2 : Nat.fib 2 = 1 := by decide
        rw [h2, one_mul, show 2 + v - 2 = v by omega]
      · obtain ⟨u', rfl⟩ : ∃ u', u = u' + 2 := ⟨u - 2, by omega⟩
        have h1 := ih (u' + 1) (by omega) (by omega)
        have h2 := ih u' (by omega) (by omega)
        have hsum : u' + 2 + v - 2 = (u' + v - 2) + 2 := by omega
        have hsum1 : u' + 1 + v - 2 = (u' + v - 2) + 1 := by omega
        rw [hsum, Nat.fib_add_two, ← hsum1, Nat.fib_add_two]
        nlinarith

lemma fib_four_step (k : ℕ) (hk : 1 ≤ k) : Nat.fib (k + 2) ≤ 4 * Nat.fib k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : Nat.fib (k' + 1 + 2) = Nat.fib (k' + 1) + Nat.fib (k' + 2) := Nat.fib_add_two
  have h2 : Nat.fib (k' + 2) = Nat.fib k' + Nat.fib (k' + 1) := Nat.fib_add_two
  have h3 : Nat.fib k' ≤ Nat.fib (k' + 1) := Nat.fib_mono (by omega)
  omega

lemma fib_four_pow (k j : ℕ) (hk : 1 ≤ k) : Nat.fib (k + 2 * j) ≤ 4 ^ j * Nat.fib k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep := fib_four_step (k + 2 * j) (by omega)
    rw [show k + 2 * (j + 1) = (k + 2 * j) + 2 by omega, pow_succ']
    calc Nat.fib (k + 2 * j + 2) ≤ 4 * Nat.fib (k + 2 * j) := hstep
      _ ≤ 4 * (4 ^ j * Nat.fib k) := Nat.mul_le_mul_left 4 ih
      _ = 4 * 4 ^ j * Nat.fib k := by ring

lemma lucas_le_18_fib (n : ℕ) (hn : 5 ≤ n) :
    Nat.fib (n - 1) + Nat.fib (n + 1) ≤ 18 * Nat.fib (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have h1 : k + 5 - 1 = k + 4 := by omega
  have h2 : k + 5 + 1 = k + 6 := by omega
  have h3 : k + 5 - 4 = k + 1 := by omega
  rw [h1, h2, h3]
  have f2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
  have f3 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
  have f4 : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.fib_add_two
  have f5 : Nat.fib (k + 5) = Nat.fib (k + 3) + Nat.fib (k + 4) := Nat.fib_add_two
  have f6 : Nat.fib (k + 6) = Nat.fib (k + 4) + Nat.fib (k + 5) := Nat.fib_add_two
  have hm : Nat.fib k ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  omega

-- List Fibonacci product bounds
lemma list_fib_prod_ge (L : List ℕ) (hL : 1 ≤ L.length) :
    Nat.fib (L.sum + 2) ≤ (L.map (fun a => Nat.fib (a + 2))).prod := by
  induction L with
  | nil => simp at hL
  | cons a rest ih =>
    cases rest with
    | nil => simp
    | cons b rest' =>
      have ih' := ih (by simp)
      simp only [List.sum_cons, List.map_cons, List.prod_cons] at ih' ⊢
      calc Nat.fib (a + (b + rest'.sum) + 2)
          ≤ Nat.fib (a + 2) * Nat.fib ((b + rest'.sum) + 2) := fib_prod_ge_fib_sum a (b + rest'.sum)
        _ ≤ Nat.fib (a + 2) * (Nat.fib (b + 2) * (rest'.map (fun x => Nat.fib (x + 2))).prod) :=
            Nat.mul_le_mul_left _ ih'

lemma list_fib_prod_le : ∀ (d : ℕ) (L : List ℕ),
    L.length = d → 1 ≤ d → d ≤ L.sum →
    (L.map (fun a => Nat.fib (a + 2))).prod ≤ 2 ^ (d - 1) * Nat.fib (L.sum - d + 3)
  | 0, _, _, hd, _ => by omega
  | 1, L, hlen, _, hsum => by
    cases L with
    | nil => simp at hlen
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [List.sum_cons, List.sum_nil, add_zero] at hsum ⊢
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          Nat.sub_self, pow_zero, one_mul]
        rw [show a - 1 + 3 = a + 2 by omega]
      | cons _ _ => simp at hlen
  | d + 2, L, hlen, _, hsum => by
    have hex : ∃ b ∈ L, 1 ≤ b := by
      by_contra h
      push Not at h
      have hz : L.sum = 0 := List.sum_eq_zero (fun x hx => by have := h x hx; omega)
      omega
    obtain ⟨b, hbmem, hb1⟩ := hex
    obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hbmem
    have hrest_ne : (L1 ++ L2).length = d + 1 := by simp at hlen ⊢; omega
    cases hL12 : L1 ++ L2 with
    | nil => simp [hL12] at hrest_ne
    | cons a L' =>
      have hperm : (L1 ++ b :: L2).Perm (a :: b :: L') := by
        have h1 : (L1 ++ b :: L2).Perm (b :: (L1 ++ L2)) := List.perm_middle
        rw [hL12] at h1
        exact h1.trans (List.Perm.swap a b L')
      have hprod : ((L1 ++ b :: L2).map (fun x => Nat.fib (x + 2))).prod =
          Nat.fib (a + 2) * Nat.fib (b + 2) * (L'.map (fun x => Nat.fib (x + 2))).prod := by
        rw [(hperm.map _).prod_eq]; simp [mul_assoc]
      have hsum_eq : (L1 ++ b :: L2).sum = a + b + L'.sum := by
        rw [hperm.sum_eq]; simp [add_assoc]
      let Lnext := (a + b - 1) :: L'
      have hlen_next : Lnext.length = d + 1 := by
        simp [Lnext]; simp [hL12] at hrest_ne; omega
      have hsum_next : Lnext.sum = (L1 ++ b :: L2).sum - 1 := by
        simp only [Lnext, List.sum_cons, hsum_eq]; omega
      have hih := list_fib_prod_le (d + 1) Lnext hlen_next (by omega) (by omega)
      simp only [Lnext, List.map_cons, List.prod_cons] at hih
      rw [hprod]
      have hm : Nat.fib (a + 2) * Nat.fib (b + 2) ≤ 2 * Nat.fib ((a + b - 1) + 2) := by
        rw [show a + b - 1 + 2 = a + b + 1 by omega]
        exact fib_merge_le a b
      calc Nat.fib (a + 2) * Nat.fib (b + 2) * (L'.map (fun x => Nat.fib (x + 2))).prod
          ≤ 2 * Nat.fib (a + b - 1 + 2) * (L'.map (fun x => Nat.fib (x + 2))).prod :=
            Nat.mul_le_mul_right _ hm
        _ = 2 * (Nat.fib (a + b - 1 + 2) * (L'.map (fun x => Nat.fib (x + 2))).prod) := by ring
        _ ≤ 2 * (2 ^ (d + 1 - 1) * Nat.fib (Lnext.sum - (d + 1) + 3)) :=
            Nat.mul_le_mul_left 2 hih
        _ = 2 ^ (d + 2 - 1) * Nat.fib ((L1 ++ b :: L2).sum - (d + 2) + 3) := by
            rw [hsum_next, show d + 2 - 1 = d + 1 by omega, show d + 1 - 1 = d by omega,
              pow_succ', mul_assoc,
              show (L1 ++ b :: L2).sum - 1 - (d + 1) + 3 = (L1 ++ b :: L2).sum - (d + 2) + 3 by omega]

lemma list_fib_prod_gap (L : List ℕ) (hd : 2 ≤ L.length) (hsum : 2 * L.length + 10 ≤ L.sum)
    (hnot : ¬ ∃ p, L.Perm (List.replicate (L.length - 1) 1 ++ [p])) :
    (L.map (fun a => Nat.fib (a + 2))).prod +
      2 ^ (L.length - 2) * Nat.fib (L.sum - L.length - 2) ≤
      2 ^ (L.length - 1) * Nat.fib (L.sum - L.length + 3) := by
  have hex : ∃ a rest, L.Perm (a :: rest) ∧ a ≠ 1 ∧ 2 * a ≤ L.sum := by
    by_cases h0 : 0 ∈ L
    · obtain ⟨L1, L2, rfl⟩ := List.append_of_mem h0
      exact ⟨0, L1 ++ L2, List.perm_middle, by omega, by omega⟩
    · have hge1 : ∀ x ∈ L, 1 ≤ x := fun x hx => by
        rcases Nat.eq_zero_or_pos x with rfl | hpos
        · exact absurd hx h0
        · exact hpos
      have hge2 : 2 ≤ (L.filter (fun x => decide (2 ≤ x))).length := by
        by_contra hlt
        push Not at hlt
        have hle1 : (L.filter (fun x => decide (2 ≤ x))).length ≤ 1 := by omega
        cases hf : L.filter (fun x => decide (2 ≤ x)) with
        | nil =>
          have hall1 : ∀ x ∈ L, x = 1 := fun x hx => by
            have h1 := hge1 x hx
            have hnot2 : ¬ 2 ≤ x := by
              intro h2
              have hmem : x ∈ L.filter (fun y => decide (2 ≤ y)) :=
                List.mem_filter.mpr ⟨hx, decide_eq_true h2⟩
              rw [hf] at hmem; simp at hmem
            omega
          have hsum1 : L.sum = L.length := by
            have : L = List.replicate L.length 1 := List.eq_replicate_iff.mpr ⟨rfl, hall1⟩
            rw [this, List.sum_replicate, smul_eq_mul, mul_one, List.length_replicate]
          omega
        | cons p r =>
          cases r with
          | cons q r' => simp [hf] at hle1
          | nil =>
            have hp_flt : p ∈ L.filter (fun x => decide (2 ≤ x)) := by rw [hf]; simp
            have hp : p ∈ L := (List.mem_filter.mp hp_flt).1
            have hp2 : decide (2 ≤ p) = true := (List.mem_filter.mp hp_flt).2
            obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hp
            have hall1 : ∀ x ∈ L1 ++ L2, x = 1 := by
              intro x hx
              have hmemL : x ∈ L1 ++ p :: L2 := by
                simp at hx ⊢; rcases hx with h | h <;> simp [h]
              have h1 := hge1 x hmemL
              by_contra hne
              have hx2 : 2 ≤ x := by omega
              have hcnt : (L1 ++ p :: L2).filter (fun y => decide (2 ≤ y)) =
                  L1.filter (fun y => decide (2 ≤ y)) ++ p :: L2.filter (fun y => decide (2 ≤ y)) := by
                simp [List.filter_append, hp2]
              rw [hcnt] at hf
              have hlen_f := congrArg List.length hf
              simp at hlen_f
              rcases List.mem_append.mp hx with hx1 | hx2'
              · have : x ∈ L1.filter (fun y => decide (2 ≤ y)) :=
                  List.mem_filter.mpr ⟨hx1, decide_eq_true hx2⟩
                have := List.length_pos_of_mem this; omega
              · have : x ∈ L2.filter (fun y => decide (2 ≤ y)) :=
                  List.mem_filter.mpr ⟨hx2', decide_eq_true hx2⟩
                have := List.length_pos_of_mem this; omega
            have hrep : L1 ++ L2 = List.replicate ((L1 ++ p :: L2).length - 1) 1 := by
              apply List.eq_replicate_iff.mpr
              exact ⟨by simp, hall1⟩
            apply hnot
            refine ⟨p, ?_⟩
            have h1 : (L1 ++ p :: L2).Perm (p :: (L1 ++ L2)) := List.perm_middle
            have h2 : (p :: (L1 ++ L2)).Perm ((L1 ++ L2) ++ [p]) :=
              (List.perm_append_singleton p (L1 ++ L2)).symm
            rw [← hrep]
            exact h1.trans h2
      cases hf : L.filter (fun x => decide (2 ≤ x)) with
      | nil => simp [hf] at hge2
      | cons x restf =>
        cases restf with
        | nil => simp [hf] at hge2
        | cons y restf' =>
          have hsub : [x, y].Sublist L := by
            have h1 : [x, y].Sublist (x :: y :: restf') := by simp
            rw [← hf] at h1
            exact h1.trans List.filter_sublist
          have hsub_sum : ∀ {A B : List ℕ}, A.Sublist B → A.sum ≤ B.sum := by
            intro A B hs
            induction hs with
            | slnil => simp
            | cons _ _ ih => simp; omega
            | cons_cons _ _ ih => simp; omega
          have hxy_sum : x + y ≤ L.sum := by
            have := hsub_sum hsub; simp at this; exact this
          have hx_flt : x ∈ L.filter (fun z => decide (2 ≤ z)) := by rw [hf]; simp
          have hy_flt : y ∈ L.filter (fun z => decide (2 ≤ z)) := by rw [hf]; simp
          have hx2 : 2 ≤ x := of_decide_eq_true (List.mem_filter.mp hx_flt).2
          have hy2 : 2 ≤ y := of_decide_eq_true (List.mem_filter.mp hy_flt).2
          by_cases hle : x ≤ y
          · have hxmem : x ∈ L := (List.mem_filter.mp hx_flt).1
            obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hxmem
            exact ⟨x, L1 ++ L2, List.perm_middle, by omega, by omega⟩
          · have hymem : y ∈ L := (List.mem_filter.mp hy_flt).1
            obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hymem
            exact ⟨y, L1 ++ L2, List.perm_middle, by omega, by omega⟩
  obtain ⟨a, rest, hperm, ha_ne, h2a⟩ := hex
  have hlen_rest : rest.length = L.length - 1 := by
    have := hperm.length_eq; simp at this; omega
  have hsum_rest : a + rest.sum = L.sum := by
    have := hperm.sum_eq; simp at this; omega
  have hprod : (L.map (fun x => Nat.fib (x + 2))).prod =
      Nat.fib (a + 2) * (rest.map (fun x => Nat.fib (x + 2))).prod := by
    rw [(hperm.map _).prod_eq]; simp
  have hrest_le := list_fib_prod_le (L.length - 1) rest hlen_rest (by omega) (by omega)
  let B := L.sum - a - L.length + 2
  have hB_ge : 4 ≤ B := by dsimp [B]; omega
  have hrest_idx : rest.sum - (L.length - 1) + 3 = B + 2 := by dsimp [B]; omega
  rw [hrest_idx] at hrest_le
  have hstep : (L.map (fun x => Nat.fib (x + 2))).prod ≤
      2 ^ (L.length - 2) * (Nat.fib (a + 2) * Nat.fib (B + 2)) := by
    rw [hprod]
    calc Nat.fib (a + 2) * (rest.map (fun x => Nat.fib (x + 2))).prod
        ≤ Nat.fib (a + 2) * (2 ^ (L.length - 1 - 1) * Nat.fib (B + 2)) :=
          Nat.mul_le_mul_left _ hrest_le
      _ = 2 ^ (L.length - 2) * (Nat.fib (a + 2) * Nat.fib (B + 2)) := by
          rw [show L.length - 1 - 1 = L.length - 2 by omega]; ring
  have hpow : 2 ^ (L.length - 1) = 2 ^ (L.length - 2) * 2 := by
    rw [← pow_succ, show L.length - 2 + 1 = L.length - 1 by omega]
  have hgap_pair : Nat.fib (a + 2) * Nat.fib (B + 2) + Nat.fib (L.sum - L.length - 2) ≤
      2 * Nat.fib (L.sum - L.length + 3) := by
    rcases Nat.eq_zero_or_pos a with rfl | ha1
    · have hm := fib_merge_zero B (by omega)
      have hB1 : B + 1 = L.sum - L.length + 3 := by omega
      have hmono : Nat.fib (L.sum - L.length - 2) ≤ Nat.fib (B - 1) :=
        Nat.fib_mono (by dsimp [B]; omega)
      rw [hB1] at hm
      simp only [zero_add]
      have hf2 : Nat.fib 2 = 1 := by decide
      rw [hf2, one_mul] at hm ⊢
      omega
    · have ha2 : 2 ≤ a := by omega
      have hm := fib_merge_id a B (by omega) (by omega)
      have haB : a + B + 1 = L.sum - L.length + 3 := by dsimp [B]; omega
      have hmul := fib_mul_ge (a - 1) (B - 1) (by omega) (by omega)
      have hidx : (a - 1) + (B - 1) - 2 = L.sum - L.length - 2 := by dsimp [B]; omega
      rw [haB] at hm
      rw [hidx] at hmul
      omega
  rw [hpow, mul_assoc]
  have hmul_gap := Nat.mul_le_mul_left (2 ^ (L.length - 2)) hgap_pair
  rw [mul_add] at hmul_gap
  omega

-- =========================================================================
-- Path and cycle independent set counting
-- =========================================================================

def isIndPath (len : ℕ) (x : Fin len → ZMod 2) : Prop :=
  ∀ i : Fin len, (hi : i.val + 1 < len) → x i * x ⟨i.val + 1, hi⟩ = 0

open Classical in
noncomputable def indPathCard (len : ℕ) : ℕ :=
  (Finset.univ.filter (isIndPath len)).card

open Classical in
lemma indPathCard_eq_fib : ∀ len : ℕ, indPathCard len = Nat.fib (len + 2)
  | 0 => by
    unfold indPathCard
    have h : (Finset.univ : Finset (Fin 0 → ZMod 2)).filter (isIndPath 0) = Finset.univ := by
      ext x; simp [isIndPath]
    rw [h, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    decide
  | 1 => by
    unfold indPathCard
    have h : (Finset.univ : Finset (Fin 1 → ZMod 2)).filter (isIndPath 1) = Finset.univ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro i hi; omega
    rw [h, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    decide
  | len + 2 => by
    unfold indPathCard
    let S := (Finset.univ : Finset (Fin (len + 2) → ZMod 2)).filter (isIndPath (len + 2))
    let S0 := S.filter (fun x => x (Fin.last (len + 1)) = 0)
    let S1 := S.filter (fun x => x (Fin.last (len + 1)) = 1)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_filter]; intro x _ h0 h1; rw [h0] at h1; exact absurd h1 (by decide)
    have hunion : S0 ∪ S1 = S := by
      ext x; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; rcases z2_cases (x (Fin.last (len + 1))) with h0 | h1
        · exact Or.inl ⟨h, h0⟩
        · exact Or.inr ⟨h, h1⟩
    have hcard0 : S0.card = indPathCard (len + 1) := by
      unfold indPathCard
      refine Finset.card_bij (fun x _ => fun i : Fin (len + 1) => x i.castSucc) ?_ ?_ ?_
      · intro x hx
        simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        intro i hi
        exact hx.1 i.castSucc (by simp; omega)
      · intro x1 hx1 x2 hx2 hEq
        simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
        funext i
        rcases Nat.lt_or_ge i.val (len + 1) with hi | hi
        · exact congrFun hEq ⟨i.val, hi⟩
        · have : i = Fin.last (len + 1) := Fin.ext (by simp; omega)
          rw [this, hx1.2, hx2.2]
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        let x : Fin (len + 2) → ZMod 2 := fun i =>
          if hlt : i.val < len + 1 then y ⟨i.val, hlt⟩ else 0
        refine ⟨x, ?_, ?_⟩
        · simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, by simp [x, Fin.last]⟩
          intro i hi
          rcases Nat.lt_or_ge (i.val + 1) (len + 1) with hlt | hge
          · have h0 : i.val < len + 1 := by omega
            simp only [x, h0, hlt, dite_true]
            exact hy ⟨i.val, h0⟩ hlt
          · have hnot : ¬ i.val + 1 < len + 1 := by omega
            simp only [x, hnot, dite_false, mul_zero]
        · funext i; dsimp [x]; exact ite_eq_left_iff.mpr (fun h => absurd i.isLt h)
    have hcard1 : S1.card = indPathCard len := by
      unfold indPathCard
      refine Finset.card_bij (fun x _ => fun i : Fin len => x ⟨i.val, by omega⟩) ?_ ?_ ?_
      · intro x hx
        simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        intro i hi
        exact hx.1 ⟨i.val, by omega⟩ (by dsimp; omega)
      · intro x1 hx1 x2 hx2 hEq
        simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
        have hpen1 : x1 ⟨len, by omega⟩ = 0 := by
          have h := hx1.1 ⟨len, by omega⟩ (by simp)
          have hlast : (⟨len + 1, by omega⟩ : Fin (len + 2)) = Fin.last (len + 1) := Fin.ext rfl
          rw [hlast, hx1.2, mul_one] at h; exact h
        have hpen2 : x2 ⟨len, by omega⟩ = 0 := by
          have h := hx2.1 ⟨len, by omega⟩ (by simp)
          have hlast : (⟨len + 1, by omega⟩ : Fin (len + 2)) = Fin.last (len + 1) := Fin.ext rfl
          rw [hlast, hx2.2, mul_one] at h; exact h
        funext i
        rcases Nat.lt_or_ge i.val len with hi | hi
        · exact congrFun hEq ⟨i.val, hi⟩
        · rcases eq_or_lt_of_le hi with heq | hgt
          · have : i = ⟨len, by omega⟩ := Fin.ext heq.symm
            rw [this, hpen1, hpen2]
          · have : i = Fin.last (len + 1) := Fin.ext (by simp; omega)
            rw [this, hx1.2, hx2.2]
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        let x : Fin (len + 2) → ZMod 2 := fun i =>
          if hlt : i.val < len then y ⟨i.val, hlt⟩
          else if i.val = len then 0 else 1
        refine ⟨x, ?_, ?_⟩
        · simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, by simp [x, Fin.last]⟩
          intro i hi
          by_cases h1 : i.val + 1 < len
          · have h0 : i.val < len := by omega
            simp only [x, h0, h1, dite_true]
            exact hy ⟨i.val, h0⟩ h1
          · by_cases h2 : i.val < len
            · have hnext : i.val + 1 = len := by omega
              have hx2 : x ⟨i.val + 1, hi⟩ = 0 := by
                dsimp [x]; simp [hnext]
              rw [hx2, mul_zero]
            · have h3 : i.val = len := by omega
              have hx1 : x i = 0 := by
                dsimp [x]; simp [h3]
              rw [hx1, zero_mul]
        · funext i; dsimp [x]; exact ite_eq_left_iff.mpr (fun h => absurd i.isLt h)
    have hS : S.card = S0.card + S1.card := by
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    have hgoal : S.card = Nat.fib (len + 2 + 2) := by
      rw [hS, hcard0, hcard1, indPathCard_eq_fib (len + 1), indPathCard_eq_fib len]
      have hfib : Nat.fib (len + 2 + 2) = Nat.fib (len + 2) + Nat.fib (len + 1 + 2) :=
        Nat.fib_add_two
      omega
    exact hgoal

-- Segment independent sets with interior zero-pins
def segGaps (lo hi : ℕ) : List ℕ → List ℕ
  | [] => [hi - lo]
  | c :: rest => (c - lo) :: segGaps (c + 1) hi rest

lemma segGaps_length (lo hi : ℕ) (cs : List ℕ) :
    (segGaps lo hi cs).length = cs.length + 1 := by
  induction cs generalizing lo with
  | nil => rfl
  | cons c rest ih => simp [segGaps, ih]

lemma segGaps_sum (lo hi : ℕ) (cs : List ℕ)
    (hlo : ∀ c ∈ cs, lo ≤ c) (hhi : ∀ c ∈ cs, c < hi) (hlt : cs.Pairwise (· < ·)) (hle : lo ≤ hi) :
    (segGaps lo hi cs).sum = hi - lo - cs.length := by
  induction cs generalizing lo with
  | nil => simp [segGaps]
  | cons c rest ih =>
    rw [List.pairwise_cons] at hlt
    have hc_lo : lo ≤ c := hlo c (by simp)
    have hc_hi : c < hi := hhi c (by simp)
    have hrest_lo : ∀ x ∈ rest, c + 1 ≤ x := fun x hx => by have := hlt.1 x hx; omega
    have hrest_hi : ∀ x ∈ rest, x < hi := fun x hx => hhi x (by simp [hx])
    have hih := ih (c + 1) hrest_lo hrest_hi hlt.2 (by omega)
    simp only [segGaps, List.sum_cons, hih, List.length_cons]
    have hlen_le : rest.length ≤ hi - (c + 1) := by
      -- Since rest is strictly increasing in [c+1, hi), rest.length ≤ hi - (c + 1)
      have hsub : rest.toFinset ⊆ Finset.Ico (c + 1) hi := by
        intro x hx
        rw [List.mem_toFinset] at hx
        exact Finset.mem_Ico.mpr ⟨hrest_lo x hx, hrest_hi x hx⟩
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Ico, List.toFinset_card_of_nodup (hlt.2.imp (fun h => ne_of_lt h))] at hcard
      exact hcard
    omega

open Classical in
lemma segCount_eq_prod (lo hi : ℕ) (cs : List ℕ)
    (hlo : ∀ c ∈ cs, lo ≤ c) (hhi : ∀ c ∈ cs, c < hi) (hlt : cs.Pairwise (· < ·)) (hle : lo ≤ hi) :
    (Finset.univ.filter (fun x : Fin (hi - lo) → ZMod 2 =>
      isIndPath (hi - lo) x ∧ ∀ c ∈ cs, (hc : c - lo < hi - lo) → x ⟨c - lo, hc⟩ = 0)).card =
    ((segGaps lo hi cs).map (fun a => Nat.fib (a + 2))).prod := by
  induction cs generalizing lo with
  | nil =>
    simp only [segGaps, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.not_mem_nil, false_implies, implies_true, and_true]
    exact indPathCard_eq_fib (hi - lo)
  | cons c rest ih =>
    rw [List.pairwise_cons] at hlt
    have hc_lo : lo ≤ c := hlo c (by simp)
    have hc_hi : c < hi := hhi c (by simp)
    have hrest_lo : ∀ x ∈ rest, c + 1 ≤ x := fun x hx => by have := hlt.1 x hx; omega
    have hrest_hi : ∀ x ∈ rest, x < hi := fun x hx => hhi x (by simp [hx])
    have hih := ih (c + 1) hrest_lo hrest_hi hlt.2 (by omega)
    simp only [segGaps, List.map_cons, List.prod_cons, ← hih, ← indPathCard_eq_fib (c - lo)]
    unfold indPathCard
    rw [← Finset.card_product]
    refine Finset.card_bij
      (fun x _ => (fun i : Fin (c - lo) => x ⟨i.val, by omega⟩,
                   fun j : Fin (hi - (c + 1)) => x ⟨(c - lo) + 1 + j.val, by omega⟩)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hx ⊢
      refine ⟨?_, ?_, ?_⟩
      · intro i hi'; exact hx.1 ⟨i.val, by omega⟩ (by dsimp; omega)
      · intro j hj'
        have h := hx.1 ⟨(c - lo) + 1 + j.val, by have := j.isLt; omega⟩ (by dsimp; omega)
        convert h using 2
      · intro r hr hlt'
        have hr1 : c + 1 ≤ r := hrest_lo r hr
        have hidx : (c - lo) + 1 + (r - (c + 1)) = r - lo := by omega
        have hxeq := hx.2 r (by simp [hr]) (by omega)
        convert hxeq using 2
        ext; exact hidx
    · intro x1 hx1 x2 hx2 hEq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      have hEq1 := congrArg Prod.fst hEq
      have hEq2 := congrArg Prod.snd hEq
      funext i
      rcases lt_trichotomy i.val (c - lo) with hlt' | heq' | hgt'
      · exact congrFun hEq1 ⟨i.val, hlt'⟩
      · have h1 := hx1.2 c (by simp) (by omega)
        have h2 := hx2.2 c (by simp) (by omega)
        have hi_eq : i = ⟨c - lo, by omega⟩ := Fin.ext heq'
        rw [hi_eq, h1, h2]
      · have hval := congrFun hEq2 ⟨i.val - (c - lo + 1), by have := i.isLt; omega⟩
        convert hval using 2 <;> (ext; simp; omega)
    · rintro ⟨yL, yR⟩ hLR
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hLR
      let x : Fin (hi - lo) → ZMod 2 := fun i =>
        if h1 : i.val < c - lo then yL ⟨i.val, h1⟩
        else if h2 : i.val = c - lo then 0
        else yR ⟨i.val - (c - lo + 1), by have := i.isLt; omega⟩
      refine ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · intro i hi'
          by_cases h1 : i.val + 1 < c - lo
          · have h0 : i.val < c - lo := by omega
            simp only [x, h0, h1, dite_true]
            exact hLR.1 ⟨i.val, h0⟩ h1
          · by_cases h2 : i.val < c - lo
            · have hnext : i.val + 1 = c - lo := by omega
              have hx2 : x ⟨i.val + 1, hi'⟩ = 0 := by simp [x, hnext]
              rw [hx2, mul_zero]
            · by_cases h3 : i.val = c - lo
              · have hx1 : x i = 0 := by simp [x, h3]
                rw [hx1, zero_mul]
              · have h1' : ¬ i.val + 1 < c - lo := by omega
                have h3' : i.val + 1 ≠ c - lo := by omega
                simp only [x, h2, h3, h1', h3', dite_false]
                have h := hLR.2.1 ⟨i.val - (c - lo + 1), by have := i.isLt; omega⟩ (by dsimp; omega)
                convert h using 2
                congr 1; ext; simp; omega
        · intro r hr hlt'
          rcases List.mem_cons.mp hr with rfl | hr'
          · simp [x]
          · have hr1 : c + 1 ≤ r := hrest_lo r hr'
            have h1 : ¬ r - lo < c - lo := by omega
            have h2 : r - lo ≠ c - lo := by omega
            simp only [x, h1, h2, dite_false]
            have := hLR.2.2 r hr' (by omega)
            convert this using 2
            ext; simp; omega
      · ext i
        · simp [x, i.isLt]
        · have h1 : ¬ (c - lo) + 1 + i.val < c - lo := by omega
          have h2 : (c - lo) + 1 + i.val ≠ c - lo := by omega
          simp only [x, h1, h2, dite_false]
          congr 1; ext; simp

open Classical in
lemma ind_cycle_pinned_zero (n : ℕ) (hn : 0 < n) (R : Finset (Fin n)) (h0 : (⟨0, hn⟩ : Fin n) ∈ R) :
    let cs : List ℕ := ((R.erase ⟨0, hn⟩).image Fin.val).sort (· ≤ ·)
    (segGaps 1 n cs).length = R.card ∧ (segGaps 1 n cs).sum = n - R.card ∧
    (∀ c ∈ cs, 1 ≤ c ∧ c < n) ∧ cs.Pairwise (· < ·) ∧
    (∀ x : Fin n, x ∈ R ↔ x.val = 0 ∨ x.val ∈ cs) ∧
    (Finset.univ.filter (fun x : Fin n → ZMod 2 => ind n hn x ∧ ∀ i ∈ R, x i = 0)).card =
      ((segGaps 1 n cs).map (fun a => Nat.fib (a + 2))).prod := by
  let cs : List ℕ := ((R.erase ⟨0, hn⟩).image Fin.val).sort (· ≤ ·)
  have hmem_cs : ∀ a : ℕ, a ∈ cs ↔ ∃ i ∈ R, i ≠ ⟨0, hn⟩ ∧ i.val = a := by
    intro a; simp only [cs, Finset.mem_sort, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨i, ⟨hne, hi⟩, rfl⟩; exact ⟨i, hi, hne, rfl⟩
    · rintro ⟨i, hi, hne, rfl⟩; exact ⟨i, ⟨hne, hi⟩, rfl⟩
  have hlen_cs : cs.length = R.card - 1 := by
    simp only [cs, Finset.length_sort]
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_erase_of_mem h0]
  have hnodup : cs.Nodup := Finset.sort_nodup _ _
  have hsorted : cs.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hstrict : cs.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem] at hsorted ⊢
    rw [List.nodup_iff_injective_getElem] at hnodup
    intro i j hi hj hij
    exact lt_of_le_of_ne (hsorted i j hi hj hij) (fun heq => by
      have := @hnodup ⟨i, hi⟩ ⟨j, hj⟩ heq; simp at this; omega)
  have hbnd : ∀ c ∈ cs, 1 ≤ c ∧ c < n := by
    intro c hc
    obtain ⟨i, _, hne, rfl⟩ := (hmem_cs c).mp hc
    have hpos : i.val ≠ 0 := fun h => hne (Fin.ext h)
    exact ⟨by omega, i.isLt⟩
  have hRiff : ∀ x : Fin n, x ∈ R ↔ x.val = 0 ∨ x.val ∈ cs := by
    intro x
    rw [hmem_cs]
    constructor
    · intro hx
      by_cases hz : x.val = 0
      · exact Or.inl hz
      · exact Or.inr ⟨x, hx, fun h => hz (congrArg Fin.val h), rfl⟩
    · rintro (hz | ⟨i, hi, _, hval⟩)
      · have : x = ⟨0, hn⟩ := Fin.ext hz; rw [this]; exact h0
      · have : x = i := Fin.ext hval.symm; rw [this]; exact hi
  have hcardR : 1 ≤ R.card := Finset.one_le_card.mpr ⟨⟨0, hn⟩, h0⟩
  have hglen : (segGaps 1 n cs).length = R.card := by
    rw [segGaps_length, hlen_cs]; omega
  have hgsum : (segGaps 1 n cs).sum = n - R.card := by
    rw [segGaps_sum 1 n cs (fun c hc => (hbnd c hc).1) (fun c hc => (hbnd c hc).2) hstrict hn, hlen_cs]
    omega
  refine ⟨hglen, hgsum, hbnd, hstrict, hRiff, ?_⟩
  rw [← segCount_eq_prod 1 n cs (fun c hc => (hbnd c hc).1) (fun c hc => (hbnd c hc).2) hstrict hn]
  refine Finset.card_bij (fun x _ => fun j : Fin (n - 1) => x ⟨j.val + 1, by omega⟩) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨?_, ?_⟩
    · intro j hj
      have hind := hx.1 ⟨j.val + 1, by omega⟩
      have hix : ix n hn (j.val + 1 + 1) = ⟨j.val + 1 + 1, by omega⟩ :=
        Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : j.val + 1 + 1 < n)])
      rw [hix] at hind; exact hind
    · intro c hc hlt'
      obtain ⟨i, hiR, _, rfl⟩ := (hmem_cs c).mp hc
      have hval := hx.2 i hiR
      convert hval using 2
      ext; simp; have := (hbnd i.val hc).1; omega
  · intro x1 hx1 x2 hx2 hEq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    funext i
    rcases Nat.eq_zero_or_pos i.val with hz | hpos
    · have : i = ⟨0, hn⟩ := Fin.ext hz
      rw [this, hx1.2 _ h0, hx2.2 _ h0]
    · have := congrFun hEq ⟨i.val - 1, by omega⟩
      convert this using 2 <;> (ext; simp; omega)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    let x : Fin n → ZMod 2 := fun i => if hz : i.val = 0 then 0 else y ⟨i.val - 1, by omega⟩
    refine ⟨x, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro i
        by_cases h0i : i.val = 0
        · have hx0 : x i = 0 := by simp [x, h0i]
          rw [hx0, zero_mul]
        · by_cases hlast : i.val + 1 = n
          · have hix : ix n hn (i.val + 1) = ⟨0, hn⟩ := Fin.ext (by simp [ix, hlast])
            rw [hix]; simp [x]
          · have hix : ix n hn (i.val + 1) = ⟨i.val + 1, by omega⟩ :=
              Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : i.val + 1 < n)])
            rw [hix]
            have h1 : i.val + 1 ≠ 0 := by omega
            simp only [x, h0i, h1, dite_false]
            have h := hy.1 ⟨i.val - 1, by have := i.isLt; omega⟩ (by dsimp; have := i.isLt; omega)
            convert h using 2
            congr 1; ext; simp; omega
      · intro i hiR
        rcases (hRiff i).mp hiR with hz | hcs
        · simp [x, hz]
        · have h1 := (hbnd i.val hcs).1
          have hz : i.val ≠ 0 := by omega
          simp only [x, hz, dite_false]
          exact hy.2 i.val hcs (by omega)
    · funext j; simp [x]

open Classical in
lemma indCard_eq_lucas (n : ℕ) (hn : 3 ≤ n) :
    (Finset.univ.filter (ind n (by omega))).card = Nat.fib (n - 1) + Nat.fib (n + 1) := by
  have hn0 : 0 < n := by omega
  let S := (Finset.univ : Finset (Fin n → ZMod 2)).filter (ind n hn0)
  let S0 := S.filter (fun x => x ⟨0, hn0⟩ = 0)
  let S1 := S.filter (fun x => x ⟨0, hn0⟩ = 1)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_filter]; intro x _ h0 h1; rw [h0] at h1; exact absurd h1 (by decide)
  have hunion : S0 ∪ S1 = S := by
    ext x; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h; rcases z2_cases (x ⟨0, hn0⟩) with h0 | h1
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h1⟩
  have hcard0 : S0.card = Nat.fib (n + 1) := by
    have hpin := (ind_cycle_pinned_zero n hn0 {⟨0, hn0⟩} (Finset.mem_singleton_self _)).2.2.2.2.2
    simp only [Finset.erase_singleton, Finset.image_empty, Finset.sort_empty, segGaps,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Finset.mem_singleton, forall_eq] at hpin
    rw [show n - 1 + 2 = n + 1 by omega] at hpin
    have hS0 : S0 = Finset.univ.filter (fun x : Fin n → ZMod 2 => ind n hn0 x ∧ x ⟨0, hn0⟩ = 0) := by
      ext x; simp [S0, S]
    rw [hS0, hpin]
  have hcard1 : S1.card = Nat.fib (n - 1) := by
    rw [show n - 1 = n - 3 + 2 by omega, ← indPathCard_eq_fib (n - 3)]
    unfold indPathCard
    refine Finset.card_bij (fun x _ => fun j : Fin (n - 3) => x ⟨j.val + 2, by omega⟩) ?_ ?_ ?_
    · intro x hx
      simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      intro j hj
      have hind := hx.1 ⟨j.val + 2, by omega⟩
      have hix : ix n hn0 (j.val + 2 + 1) = ⟨j.val + 2 + 1, by omega⟩ :=
        Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : j.val + 2 + 1 < n)])
      rw [hix] at hind; exact hind
    · intro x1 hx1 x2 hx2 hEq
      simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      have h1_1 : x1 ⟨1, by omega⟩ = 0 := by
        have h := hx1.1 ⟨0, hn0⟩
        have hix : ix n hn0 (0 + 1) = ⟨1, by omega⟩ := Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : 1 < n)])
        rw [hix, hx1.2, one_mul] at h; exact h
      have h1_2 : x2 ⟨1, by omega⟩ = 0 := by
        have h := hx2.1 ⟨0, hn0⟩
        have hix : ix n hn0 (0 + 1) = ⟨1, by omega⟩ := Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : 1 < n)])
        rw [hix, hx2.2, one_mul] at h; exact h
      have hl_1 : x1 ⟨n - 1, by omega⟩ = 0 := by
        have h := hx1.1 ⟨n - 1, by omega⟩
        have hix : ix n hn0 (n - 1 + 1) = ⟨0, hn0⟩ := Fin.ext (by simp [ix, show n - 1 + 1 = n by omega])
        rw [hix, hx1.2, mul_one] at h; exact h
      have hl_2 : x2 ⟨n - 1, by omega⟩ = 0 := by
        have h := hx2.1 ⟨n - 1, by omega⟩
        have hix : ix n hn0 (n - 1 + 1) = ⟨0, hn0⟩ := Fin.ext (by simp [ix, show n - 1 + 1 = n by omega])
        rw [hix, hx2.2, mul_one] at h; exact h
      funext i
      by_cases h0i : i.val = 0
      · have : i = ⟨0, hn0⟩ := Fin.ext h0i; rw [this, hx1.2, hx2.2]
      · by_cases h1i : i.val = 1
        · have : i = ⟨1, by omega⟩ := Fin.ext h1i; rw [this, h1_1, h1_2]
        · by_cases hli : i.val = n - 1
          · have : i = ⟨n - 1, by omega⟩ := Fin.ext hli; rw [this, hl_1, hl_2]
          · have := congrFun hEq ⟨i.val - 2, by omega⟩
            convert this using 2 <;> (ext; simp; omega)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      let x : Fin n → ZMod 2 := fun i =>
        if h0 : i.val = 0 then 1
        else if h1 : i.val = 1 ∨ i.val = n - 1 then 0
        else y ⟨i.val - 2, by have := i.isLt; omega⟩
      refine ⟨x, ?_, ?_⟩
      · simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, by simp [x]⟩
        intro i
        by_cases h0i : i.val = 0
        · have hix : ix n hn0 (i.val + 1) = ⟨1, by omega⟩ :=
            Fin.ext (by simp [ix, h0i, Nat.mod_eq_of_lt (by omega : 1 < n)])
          rw [hix]; simp [x]
        · by_cases h1i : i.val = 1
          · have : x i = 0 := by simp [x, h1i]
            rw [this, zero_mul]
          · by_cases hli : i.val = n - 1
            · have hne : n - 1 ≠ 0 := by omega
              have : x i = 0 := by simp [x, hli, hne]
              rw [this, zero_mul]
            · by_cases hll : i.val + 1 = n - 1
              · have hix : ix n hn0 (i.val + 1) = ⟨n - 1, by omega⟩ :=
                  Fin.ext (by simp [ix, hll, Nat.mod_eq_of_lt (by omega : n - 1 < n)])
                rw [hix]
                have hx2 : x ⟨n - 1, by omega⟩ = 0 := by simp [x, show n - 1 ≠ 0 by omega]
                rw [hx2, mul_zero]
              · have hix : ix n hn0 (i.val + 1) = ⟨i.val + 1, by omega⟩ :=
                  Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : i.val + 1 < n)])
                rw [hix]
                have hnext0 : i.val + 1 ≠ 0 := by omega
                have hnext1 : ¬ (i.val + 1 = 1 ∨ i.val + 1 = n - 1) := by omega
                have hcurr1 : ¬ (i.val = 1 ∨ i.val = n - 1) := by omega
                simp only [x, h0i, hcurr1, hnext0, hnext1, dite_false]
                have h := hy ⟨i.val - 2, by have := i.isLt; omega⟩ (by dsimp; have := i.isLt; omega)
                convert h using 2
                congr 1; ext; simp; omega
      · funext j
        have h0j : j.val + 2 ≠ 0 := by omega
        have h1j : ¬ (j.val + 2 = 1 ∨ j.val + 2 = n - 1) := by omega
        simp only [x, h0j, h1j, dite_false]
        congr 1
  have hS : S.card = S0.card + S1.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  change S.card = Nat.fib (n - 1) + Nat.fib (n + 1)
  rw [hS, hcard0, hcard1, add_comm]

-- Block characterization from gap permutation
lemma segGaps_perm_block (n : ℕ) (hn : 0 < n) (cs : List ℕ) (p : ℕ)
    (hbnd : ∀ c ∈ cs, 1 ≤ c ∧ c < n) (hstrict : cs.Pairwise (· < ·))
    (hbig : 2 * (cs.length + 1) < n)
    (hperm : (segGaps 1 n cs).Perm (List.replicate cs.length 1 ++ [p])) :
    ∃ s : ℕ, ∀ x : Fin n, (x.val = 0 ∨ x.val ∈ cs) ↔
      ∃ j : Fin (cs.length + 1), x = ix n hn (s + 2 * j.val) := by
  let d := cs.length + 1
  let r : ℕ → ℕ := fun i => if i = 0 then 0 else if h : i - 1 < cs.length then cs[i - 1]'h else n
  have hseg_get : ∀ (lo hi : ℕ) (L : List ℕ) (i : ℕ) (hi_i : i < (segGaps lo hi L).length),
      (segGaps lo hi L)[i]'hi_i =
        (if h1 : i < L.length then L[i]'h1 else hi) -
        (if h0 : i = 0 then lo else L[i - 1]'(by rw [segGaps_length] at hi_i; omega) + 1) := by
    intro lo hi L
    induction L generalizing lo with
    | nil =>
      intro i hi_i
      simp only [segGaps, List.length_singleton] at hi_i
      have : i = 0 := by omega
      subst this; simp [segGaps]
    | cons c rest ih =>
      intro i hi_i
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · simp [segGaps]
      · have hi' : i - 1 < (segGaps (c + 1) hi rest).length := by
          simp only [segGaps_length, List.length_cons] at hi_i ⊢; omega
        have h1 := ih (c + 1) (i - 1) hi'
        have hget : (segGaps lo hi (c :: rest))[i]'hi_i = (segGaps (c + 1) hi rest)[i - 1]'hi' := by
          obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          rfl
        rw [hget, h1]
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        simp only [Nat.add_sub_cancel, List.length_cons, Nat.add_lt_add_iff_right,
          Nat.succ_ne_zero, ↓reduceDIte, List.getElem_cons_succ]
        rcases Nat.eq_zero_or_pos i' with rfl | hi'pos
        · simp
        · simp only [Nat.ne_of_gt hi'pos, ↓reduceDIte]
          congr 2
          obtain ⟨i'', rfl⟩ : ∃ i'', i' = i'' + 1 := ⟨i' - 1, by omega⟩
          rfl
  have hp_val : p = n - 2 * d + 1 := by
    have hs1 := hperm.sum_eq
    rw [segGaps_sum 1 n cs (fun c hc => (hbnd c hc).1) (fun c hc => (hbnd c hc).2) hstrict hn] at hs1
    simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one, List.sum_singleton] at hs1
    dsimp [d] at ⊢; omega
  have hp_ne1 : p ≠ 1 := by omega
  have hmem_p : p ∈ segGaps 1 n cs := hperm.symm.subset (by simp)
  obtain ⟨k, hk_lt, hgk⟩ := List.mem_iff_getElem.mp hmem_p
  have hk_d : k < d := by rw [segGaps_length] at hk_lt; exact hk_lt
  have hother1 : ∀ j : ℕ, (hj : j < (segGaps 1 n cs).length) → j ≠ k →
      (segGaps 1 n cs)[j]'hj = 1 := by
    intro j hj hjk
    have hcount1 : (segGaps 1 n cs).count p = 1 := by
      rw [hperm.count_eq, List.count_append, List.count_replicate, List.count_singleton_self]
      simp [hp_ne1.symm]
    by_contra hne1
    have hmemj : (segGaps 1 n cs)[j]'hj ∈ List.replicate cs.length 1 ++ [p] :=
      hperm.subset (List.getElem_mem hj)
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hmemj
    have hjp : (segGaps 1 n cs)[j]'hj = p := by
      rcases hmemj with ⟨_, h1⟩ | hp'
      · exact absurd h1 hne1
      · exact hp'
    have h2 : 2 ≤ (segGaps 1 n cs).count p := by
      have hcnt_ge : ∀ (L : List ℕ) (i1 i2 : ℕ) (h1 : i1 < L.length) (h2 : i2 < L.length),
          i1 ≠ i2 → L[i1]'h1 = p → L[i2]'h2 = p → 2 ≤ L.count p := by
        intro L
        induction L with
        | nil => intro _ _ h1; simp at h1
        | cons a rest ih =>
          intro i1 i2 h1 h2 hne he1 he2
          cases i1 with
          | zero =>
            cases i2 with
            | zero => exact absurd rfl hne
            | succ i2' =>
              simp only [List.getElem_cons_zero] at he1
              simp only [List.getElem_cons_succ] at he2
              simp only [List.count_cons, he1, beq_self_eq_true, ↓reduceIte]
              have hpos : 1 ≤ rest.count p :=
                List.count_pos_iff.mpr (he2 ▸ List.getElem_mem (by simp at h2; omega))
              omega
          | succ i1' =>
            cases i2 with
            | zero =>
              simp only [List.getElem_cons_zero] at he2
              simp only [List.getElem_cons_succ] at he1
              simp only [List.count_cons, he2, beq_self_eq_true, ↓reduceIte]
              have hpos : 1 ≤ rest.count p :=
                List.count_pos_iff.mpr (he1 ▸ List.getElem_mem (by simp at h1; omega))
              omega
            | succ i2' =>
              simp only [List.getElem_cons_succ] at he1 he2
              have hih := ih i1' i2' (by simp at h1; omega) (by simp at h2; omega)
                (by omega) he1 he2
              rw [List.count_cons]; split_ifs <;> omega
      exact hcnt_ge (segGaps 1 n cs) j k hj hk_lt hjk hjp hgk
    omega
  -- Express r (i+1) - r i = (segGaps 1 n cs)[i] + 1 for all i < d
  have hr_step : ∀ i : ℕ, (hi : i < d) →
      r (i + 1) = r i + (segGaps 1 n cs)[i]'(by rw [segGaps_length]; exact hi) + 1 := by
    intro i hi
    have hhi : i < (segGaps 1 n cs).length := by rw [segGaps_length]; exact hi
    rw [hseg_get 1 n cs i hhi]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · by_cases h0 : 0 < cs.length
      · have h1 := (hbnd cs[0] (List.getElem_mem h0)).1
        simp only [r, ↓reduceIte, Nat.add_sub_cancel, h0, ↓reduceDIte, Nat.succ_ne_zero]; omega
      · simp only [r, ↓reduceIte, Nat.add_sub_cancel, h0, ↓reduceDIte, Nat.succ_ne_zero]; omega
    · have him1 : i - 1 < cs.length := by dsimp [d] at hi; omega
      have hne0 : i ≠ 0 := by omega
      have hne0' : i + 1 ≠ 0 := by omega
      by_cases hilt : i < cs.length
      · have hlt_cs : cs[i - 1] < cs[i] := by
          rw [List.pairwise_iff_getElem] at hstrict
          exact hstrict (i - 1) i him1 hilt (by omega)
        simp only [r, hne0, hne0', ↓reduceIte, him1, hilt, Nat.add_sub_cancel, ↓reduceDIte]
        omega
      · have hlt_n : cs[i - 1] < n := (hbnd cs[i - 1] (List.getElem_mem him1)).2
        simp only [r, hne0, hne0', ↓reduceIte, him1, hilt, Nat.add_sub_cancel, ↓reduceDIte]
        omega
  -- Now r i = 2 * i for i ≤ k, and r i = n - 2 * (d - i) for k < i ≤ d!
  have hr_lo : ∀ i : ℕ, i ≤ k → r i = 2 * i := by
    intro i hi
    induction i with
    | zero => simp [r]
    | succ i ih =>
      have h1 := hr_step i (by omega)
      have h2 := hother1 i (by rw [segGaps_length]; omega) (by omega)
      rw [h2, ih (by omega)] at h1; omega
  have hr_hi : ∀ m : ℕ, m < d - k → r (d - m) = n - 2 * m := by
    intro m hm
    induction m with
    | zero =>
      simp only [Nat.sub_zero, mul_zero, r]
      have hd0 : d ≠ 0 := by dsimp [d]; omega
      have hdl : ¬ d - 1 < cs.length := by dsimp [d]; omega
      simp [hd0, hdl]
    | succ m ih =>
      have h1 := hr_step (d - (m + 1)) (by omega)
      have h2 := hother1 (d - (m + 1)) (by rw [segGaps_length]; omega) (by omega)
      rw [show d - (m + 1) + 1 = d - m by omega, ih (by omega), h2] at h1
      omega
  -- Choose starting point s := r ((k + 1) % d) = if k + 1 < d then n - 2 * (d - (k + 1)) else 0
  let s := if k + 1 < d then n - 2 * (d - (k + 1)) else 0
  refine ⟨s, fun x => ?_⟩
  have hr_mem : ∀ x : Fin n, (x.val = 0 ∨ x.val ∈ cs) ↔ ∃ i : Fin d, x.val = r i.val := by
    intro x
    constructor
    · rintro (hz | hcs)
      · exact ⟨⟨0, by dsimp [d]; omega⟩, by simp [r, hz]⟩
      · obtain ⟨i, hilt, hi⟩ := List.mem_iff_getElem.mp hcs
        refine ⟨⟨i + 1, by dsimp [d]; omega⟩, ?_⟩
        simp [r, hilt, hi]
    · rintro ⟨i, hx⟩
      rcases Nat.eq_zero_or_pos i.val with hz | hpos
      · left; simp [r, hz] at hx; exact hx
      · right
        have him1 : i.val - 1 < cs.length := by dsimp [d] at i; omega
        simp only [r, Nat.ne_of_gt hpos, ↓reduceIte, him1, ↓reduceDIte] at hx
        rw [hx]; exact List.getElem_mem him1
  rw [hr_mem]
  constructor
  · rintro ⟨i, hx⟩
    by_cases hkd : k + 1 < d
    · by_cases hik : i.val ≤ k
      · refine ⟨⟨(d - (k + 1)) + i.val, by omega⟩, Fin.ext ?_⟩
        rw [hx, hr_lo i.val hik]
        simp only [ix, s, hkd, ↓reduceIte]
        have heq : n - 2 * (d - (k + 1)) + 2 * (d - (k + 1) + i.val) = n + 2 * i.val := by omega
        rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      · refine ⟨⟨i.val - (k + 1), by omega⟩, Fin.ext ?_⟩
        have hri : r i.val = n - 2 * (d - i.val) := by
          have := hr_hi (d - i.val) (by omega)
          rwa [show d - (d - i.val) = i.val by omega] at this
        rw [hx, hri]
        simp only [ix, s, hkd, ↓reduceIte]
        have heq : n - 2 * (d - (k + 1)) + 2 * (i.val - (k + 1)) = n - 2 * (d - i.val) := by omega
        rw [heq, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨i, Fin.ext ?_⟩
      rw [hx, hr_lo i.val (by omega)]
      simp only [ix, s, hkd, ↓reduceIte, zero_add]
      rw [Nat.mod_eq_of_lt (by omega)]
  · rintro ⟨j, rfl⟩
    by_cases hkd : k + 1 < d
    · by_cases hjd : j.val < d - (k + 1)
      · refine ⟨⟨k + 1 + j.val, by omega⟩, ?_⟩
        have hri : r (k + 1 + j.val) = n - 2 * (d - (k + 1 + j.val)) := by
          have := hr_hi (d - (k + 1 + j.val)) (by omega)
          rwa [show d - (d - (k + 1 + j.val)) = k + 1 + j.val by omega] at this
        rw [hri]
        simp only [ix, s, hkd, ↓reduceIte]
        have heq : n - 2 * (d - (k + 1)) + 2 * j.val = n - 2 * (d - (k + 1 + j.val)) := by omega
        rw [heq, Nat.mod_eq_of_lt (by omega)]
      · refine ⟨⟨j.val - (d - (k + 1)), by omega⟩, ?_⟩
        have hle_k : j.val - (d - (k + 1)) ≤ k := by omega
        simp only [hr_lo (j.val - (d - (k + 1))) hle_k]
        simp only [ix, s, hkd, ↓reduceIte]
        have heq : n - 2 * (d - (k + 1)) + 2 * j.val = n + 2 * (j.val - (d - (k + 1))) := by omega
        rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨j, ?_⟩
      rw [hr_lo j.val (by omega)]
      simp only [ix, s, hkd, ↓reduceIte, zero_add]
      rw [Nat.mod_eq_of_lt (by omega)]

end Test33638

namespace Decay33638

def ix (n : ℕ) (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

noncomputable def base (n : ℕ) (j : Fin 4) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2) then (1 : ZMod 2) else 0

noncomputable def even (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = 0 then z i else 0

def sgn (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

def dot (n : ℕ) (z x : Fin n → ZMod 2) : ZMod 2 := ∑ i, z i * x i

def ind (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) : Prop :=
  ∀ i : Fin n, x i * x (ix n hn (i.val + 1)) = 0

noncomputable def tw0 (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∑ x : Fin n → ZMod 2, if ind n hn x then sgn (dot n z x) else 0

noncomputable def S0 (n : ℕ) (hn : 0 < n) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∑ z ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun z => z ∈ D), tw0 n hn z

instance decInd (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) : Decidable (ind n hn x) :=
  Fintype.decidableForallFintype

/-! Section 1: Cyclic shift -/

private lemma ix_add (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    ix n hn ((ix n hn a).val + b) = ix n hn (a + b) := by
  apply Fin.ext
  simp [ix, Nat.mod_add_mod]

private lemma ix_val_self (n : ℕ) (hn : 0 < n) (i : Fin n) :
    ix n hn i.val = i := by
  apply Fin.ext
  simp [ix, Nat.mod_eq_of_lt i.isLt]

private lemma ix_add_inv (n : ℕ) (hn : 0 < n) (s : ℕ) (i : Fin n) :
    ix n hn ((ix n hn (i.val + s)).val + (n - s % n)) = i := by
  rw [ix_add]
  apply Fin.ext
  have hlt : s % n < n := Nat.mod_lt s hn
  have hdiv : s = n * (s / n) + s % n := (Nat.div_add_mod s n).symm
  have hsum : i.val + s + (n - s % n) = i.val + n * (s / n + 1) := by
    rw [Nat.mul_add, mul_one]; omega
  simp only [ix, hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

private lemma ix_inv_add (n : ℕ) (hn : 0 < n) (s : ℕ) (i : Fin n) :
    ix n hn ((ix n hn (i.val + (n - s % n))).val + s) = i := by
  rw [ix_add]
  apply Fin.ext
  have hlt : s % n < n := Nat.mod_lt s hn
  have hdiv : s = n * (s / n) + s % n := (Nat.div_add_mod s n).symm
  have hsum : i.val + (n - s % n) + s = i.val + n * (s / n + 1) := by
    rw [Nat.mul_add, mul_one]; omega
  simp only [ix, hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

def sh (n : ℕ) (hn : 0 < n) (s : ℕ) (z : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => z (ix n hn (i.val + s))

private def shIdx (n : ℕ) (hn : 0 < n) (s : ℕ) : Fin n ≃ Fin n where
  toFun i := ix n hn (i.val + s)
  invFun i := ix n hn (i.val + (n - s % n))
  left_inv i := ix_add_inv n hn s i
  right_inv i := ix_inv_add n hn s i

def shL (n : ℕ) (hn : 0 < n) (s : ℕ) :
    (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun := sh n hn s
  invFun := sh n hn (n - s % n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    funext i
    simp [sh, ix_inv_add]
  right_inv z := by
    funext i
    simp [sh, ix_add_inv]

private lemma sh_dot (n : ℕ) (hn : 0 < n) (s : ℕ) (z x : Fin n → ZMod 2) :
    dot n (sh n hn s z) (sh n hn s x) = dot n z x := by
  unfold dot sh
  exact Equiv.sum_comp (shIdx n hn s) (fun i => z i * x i)

private lemma sh_ind (n : ℕ) (hn : 0 < n) (s : ℕ) (x : Fin n → ZMod 2) :
    ind n hn (sh n hn s x) ↔ ind n hn x := by
  unfold ind sh
  constructor
  · intro h j
    have hj := h ((shIdx n hn s).symm j)
    have h1 : ix n hn (((shIdx n hn s).symm j).val + s) = j := (shIdx n hn s).apply_symm_apply j
    have h2 : ix n hn ((ix n hn (((shIdx n hn s).symm j).val + 1)).val + s) = ix n hn (j.val + 1) := by
      rw [ix_add, show (((shIdx n hn s).symm j).val + 1 + s) = (((shIdx n hn s).symm j).val + s + 1) by omega]
      rw [← ix_add, h1]
    rw [h1, h2] at hj
    exact hj
  · intro h i
    have h1 : ix n hn ((ix n hn (i.val + 1)).val + s) = ix n hn ((ix n hn (i.val + s)).val + 1) := by
      rw [ix_add, ix_add]
      congr 1
      omega
    rw [h1]
    exact h (ix n hn (i.val + s))

private lemma tw0_eq_sum (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) :
    tw0 n hn z = ∑ x : Fin n → ZMod 2, if ind n hn x then sgn (dot n z x) else 0 := by
  unfold tw0
  refine Finset.sum_congr (by ext; simp) fun x _ => ?_
  by_cases h : ind n hn x <;> simp [h]

lemma sh_tw0 (n : ℕ) (hn : 0 < n) (s : ℕ) (z : Fin n → ZMod 2) :
    tw0 n hn (sh n hn s z) = tw0 n hn z := by
  rw [tw0_eq_sum, tw0_eq_sum]
  symm
  refine Fintype.sum_equiv (shL n hn s).toEquiv _ _ fun x => ?_
  change (if ind n hn x then sgn (dot n z x) else 0) =
    if ind n hn (sh n hn s x) then sgn (dot n (sh n hn s z) (sh n hn s x)) else 0
  by_cases h : ind n hn x
  · have h' : ind n hn (sh n hn s x) := (sh_ind n hn s x).mpr h
    simp only [h, h', ↓reduceIte, sh_dot]
  · have h' : ¬ ind n hn (sh n hn s x) := fun hs => h ((sh_ind n hn s x).mp hs)
    simp only [h, h', ↓reduceIte]

lemma sh_S0 (n : ℕ) (hn : 0 < n) (s : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    S0 n hn (D.map (shL n hn s).toLinearMap) = S0 n hn D := by
  classical
  have hS0 : ∀ E : Submodule (ZMod 2) (Fin n → ZMod 2),
      S0 n hn E = ∑ z : Fin n → ZMod 2, if z ∈ E then tw0 n hn z else 0 := by
    intro E
    unfold S0
    rw [Finset.sum_filter]
    refine Finset.sum_congr (by ext; simp) fun z _ => ?_
    by_cases hz : z ∈ E <;> simp [hz]
  rw [hS0, hS0]
  symm
  refine Fintype.sum_equiv (shL n hn s).toEquiv _ _ fun z => ?_
  have hmem : (shL n hn s) z ∈ D.map (shL n hn s).toLinearMap ↔ z ∈ D := by
    constructor
    · rintro ⟨w, hw, hEq⟩
      have : w = z := (shL n hn s).injective hEq
      rwa [← this]
    · intro hz
      exact ⟨z, hz, rfl⟩
  simp only [LinearEquiv.coe_toEquiv]
  by_cases hz : z ∈ D
  · have hz' : (shL n hn s) z ∈ D.map (shL n hn s).toLinearMap := hmem.mpr hz
    simp only [hz, hz', ↓reduceIte]
    exact (sh_tw0 n hn s z).symm
  · have hz' : (shL n hn s) z ∉ D.map (shL n hn s).toLinearMap := fun h => hz (hmem.mp h)
    simp only [hz, hz', ↓reduceIte]

private lemma base_mod6 (t : ℕ) (j : Fin 4) (i : Fin (6*t)) :
    base (6*t) j i =
      if i.val % 6 % 2 = j.val / 2 ∧ (i.val % 6 / 2 = j.val % 2 ∨ i.val % 6 / 2 = 2)
      then (1 : ZMod 2) else 0 := by
  unfold base
  have hdiv6 : i.val = 6 * (i.val / 6) + i.val % 6 := (Nat.div_add_mod i.val 6).symm
  have h1 : i.val % 2 = i.val % 6 % 2 := by omega
  have h2 : i.val / 2 = 3 * (i.val / 6) + i.val % 6 / 2 := by omega
  have h3 : i.val / 2 % 3 = i.val % 6 / 2 := by rw [h2]; omega
  have hiff : (i.val % 2 = j.val / 2 ∧ (i.val / 2 % 3 = j.val % 2 ∨ i.val / 2 % 3 = 2)) ↔
      (i.val % 6 % 2 = j.val / 2 ∧ (i.val % 6 / 2 = j.val % 2 ∨ i.val % 6 / 2 = 2)) := by
    rw [h1, h3]
  by_cases h : i.val % 6 % 2 = j.val / 2 ∧ (i.val % 6 / 2 = j.val % 2 ∨ i.val % 6 / 2 = 2)
  · simp only [h, hiff.mpr h]
  · simp only [h, mt hiff.mp h, ↓reduceIte]

private lemma ix_succ_mod6 (t : ℕ) (ht : 0 < t) (i : Fin (6*t)) :
    (ix (6*t) (by omega) (i.val + 1)).val % 6 = (i.val % 6 + 1) % 6 := by
  simp only [ix]
  rw [Nat.mod_mod_of_dvd (i.val + 1) ⟨t, rfl⟩]
  omega

private lemma sh_one_base0 (t : ℕ) (ht : 0 < t) :
    sh (6*t) (by omega) 1 (base (6*t) 0) = base (6*t) 3 := by
  funext i
  simp only [sh, base_mod6, ix_succ_mod6 t ht]
  have hr : i.val % 6 < 6 := Nat.mod_lt _ (by omega)
  generalize i.val % 6 = r at hr
  interval_cases r <;> decide

private lemma sh_one_base1 (t : ℕ) (ht : 0 < t) :
    sh (6*t) (by omega) 1 (base (6*t) 1) = base (6*t) 2 + base (6*t) 3 := by
  funext i
  simp only [sh, Pi.add_apply, base_mod6, ix_succ_mod6 t ht]
  have hr : i.val % 6 < 6 := Nat.mod_lt _ (by omega)
  generalize i.val % 6 = r at hr
  interval_cases r <;> decide

private lemma sh_one_base2 (t : ℕ) (ht : 0 < t) :
    sh (6*t) (by omega) 1 (base (6*t) 2) = base (6*t) 0 := by
  funext i
  simp only [sh, base_mod6, ix_succ_mod6 t ht]
  have hr : i.val % 6 < 6 := Nat.mod_lt _ (by omega)
  generalize i.val % 6 = r at hr
  interval_cases r <;> decide

private lemma sh_one_base3 (t : ℕ) (ht : 0 < t) :
    sh (6*t) (by omega) 1 (base (6*t) 3) = base (6*t) 1 := by
  funext i
  simp only [sh, base_mod6, ix_succ_mod6 t ht]
  have hr : i.val % 6 < 6 := Nat.mod_lt _ (by omega)
  generalize i.val % 6 = r at hr
  interval_cases r <;> decide

private lemma sh_check_one (t : ℕ) (ht : 0 < t) :
    (Submodule.span (ZMod 2) (Set.range (base (6*t)))).map (shL (6*t) (by omega) 1).toLinearMap =
      Submodule.span (ZMod 2) (Set.range (base (6*t))) := by
  set C := Submodule.span (ZMod 2) (Set.range (base (6*t)))
  have hb : ∀ j : Fin 4, base (6*t) j ∈ C := fun j => Submodule.subset_span ⟨j, rfl⟩
  apply le_antisymm
  · rw [Submodule.map_span_le]
    rintro _ ⟨j, rfl⟩
    change sh (6*t) (by omega) 1 (base (6*t) j) ∈ C
    fin_cases j
    · change sh (6*t) (by omega) 1 (base (6*t) 0) ∈ C
      rw [sh_one_base0 t ht]; exact hb 3
    · change sh (6*t) (by omega) 1 (base (6*t) 1) ∈ C
      rw [sh_one_base1 t ht]; exact C.add_mem (hb 2) (hb 3)
    · change sh (6*t) (by omega) 1 (base (6*t) 2) ∈ C
      rw [sh_one_base2 t ht]; exact hb 0
    · change sh (6*t) (by omega) 1 (base (6*t) 3) ∈ C
      rw [sh_one_base3 t ht]; exact hb 1
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact ⟨base (6*t) 2, hb 2, sh_one_base2 t ht⟩
    · exact ⟨base (6*t) 3, hb 3, sh_one_base3 t ht⟩
    · refine ⟨base (6*t) 0 + base (6*t) 1, C.add_mem (hb 0) (hb 1), ?_⟩
      rw [map_add]
      change sh (6*t) (by omega) 1 (base (6*t) 0) + sh (6*t) (by omega) 1 (base (6*t) 1) = base (6*t) 2
      rw [sh_one_base0 t ht, sh_one_base1 t ht]
      funext i
      simp only [Pi.add_apply]
      have h2 : base (6*t) 3 i + base (6*t) 3 i = 0 := CharTwo.add_self_eq_zero _
      rw [add_left_comm, h2, add_zero]
    · exact ⟨base (6*t) 0, hb 0, sh_one_base0 t ht⟩

lemma sh_check (t : ℕ) (ht : 0 < t) (s : ℕ) :
    (Submodule.span (ZMod 2) (Set.range (base (6*t)))).map (shL (6*t) (by omega) s).toLinearMap =
      Submodule.span (ZMod 2) (Set.range (base (6*t))) := by
  induction s with
  | zero =>
    have h0 : (shL (6*t) (by omega) 0).toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun z => funext fun i => ?_
      change sh (6*t) (by omega) 0 z i = z i
      simp [sh, ix_val_self]
    rw [h0, Submodule.map_id]
  | succ s ih =>
    have hcomp : (shL (6*t) (by omega) (s + 1)).toLinearMap =
        (shL (6*t) (by omega) 1).toLinearMap.comp (shL (6*t) (by omega) s).toLinearMap := by
      refine LinearMap.ext fun z => funext fun i => ?_
      change sh (6*t) (by omega) (s + 1) z i = sh (6*t) (by omega) 1 (sh (6*t) (by omega) s z) i
      simp only [sh, ix_add]
      congr 2
      omega
    rw [hcomp, Submodule.map_comp, ih, sh_check_one t ht]

/-! Section 2: Hamming weight and light span -/

noncomputable def wt (n : ℕ) (z : Fin n → ZMod 2) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).card

private lemma wt_eq_card (n : ℕ) (z : Fin n → ZMod 2) :
    wt n z = (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).card := by
  unfold wt
  congr 1
  ext i
  simp

private lemma wt_zero (n : ℕ) : wt n 0 = 0 := by
  rw [wt_eq_card]
  simp

lemma wt_add_le (n : ℕ) (x y : Fin n → ZMod 2) : wt n (x + y) ≤ wt n x + wt n y := by
  rw [wt_eq_card, wt_eq_card, wt_eq_card]
  calc (Finset.univ.filter (fun i : Fin n => (x + y) i ≠ 0)).card
      ≤ (Finset.univ.filter (fun i : Fin n => x i ≠ 0) ∪
          Finset.univ.filter (fun i : Fin n => y i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Finset.mem_union] at hi ⊢
        by_contra h
        push Not at h
        exact hi (by rw [h.1, h.2, add_zero])
    _ ≤ _ := Finset.card_union_le _ _

lemma wt_sum_le {ι : Type*} (n : ℕ) (s : Finset ι) (f : ι → Fin n → ZMod 2) :
    wt n (∑ j ∈ s, f j) ≤ ∑ j ∈ s, wt n (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wt_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (wt_add_le n _ _) (Nat.add_le_add_left ih _)

lemma wt_even_le (n : ℕ) (z : Fin n → ZMod 2) : wt n (even n z) ≤ wt n z := by
  rw [wt_eq_card, wt_eq_card]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  unfold even at hi
  by_cases h : i.val % 2 = 0
  · simp only [h, ↓reduceIte] at hi
    exact hi
  · simp only [h, ↓reduceIte] at hi
    exact absurd rfl hi

lemma wt_sh (n : ℕ) (hn : 0 < n) (s : ℕ) (z : Fin n → ZMod 2) :
    wt n (sh n hn s z) = wt n z := by
  rw [wt_eq_card, wt_eq_card]
  unfold sh
  refine Finset.card_bij (fun i _ => shIdx n hn s i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  · intro i₁ _ i₂ _ h
    exact (shIdx n hn s).injective h
  · intro j hj
    refine ⟨(shIdx n hn s).symm j, ?_, (shIdx n hn s).apply_symm_apply j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    change z ((shIdx n hn s) ((shIdx n hn s).symm j)) ≠ 0
    rwa [(shIdx n hn s).apply_symm_apply]

private lemma base_eval_mod6 (t : ℕ) (j : Fin 4) (b : Fin t) (r : ℕ) (hr : r < 6) :
    base (6*t) j ⟨6 * b.val + r, by omega⟩ =
      if r % 2 = j.val / 2 ∧ (r / 2 = j.val % 2 ∨ r / 2 = 2) then (1 : ZMod 2) else 0 := by
  rw [base_mod6]
  have hmod : (6 * b.val + r) % 6 = r := by omega
  simp only [hmod]

lemma check_wt_ge (t : ℕ) (ht : 0 < t) (c : Fin (6*t) → ZMod 2)
    (hc : c ∈ Submodule.span (ZMod 2) (Set.range (base (6*t)))) (hne : c ≠ 0) :
    2 * t ≤ wt (6*t) c := by
  have _ : 0 < t := ht
  rw [Submodule.mem_span_range_iff_exists_fun] at hc
  rcases hc with ⟨a, rfl⟩
  have hblock : ∀ (b : Fin t) (r : ℕ) (hr : r < 6),
      (∑ j : Fin 4, a j • base (6*t) j) ⟨6 * b.val + r, by omega⟩ =
        if r = 0 then a 0
        else if r = 1 then a 2
        else if r = 2 then a 1
        else if r = 3 then a 3
        else if r = 4 then a 0 + a 1
        else a 2 + a 3 := by
    intro b r hr
    rw [Finset.sum_apply, Fin.sum_univ_four]
    simp only [Pi.smul_apply, smul_eq_mul, base_eval_mod6 t _ b r hr]
    interval_cases r <;> simp
  have hex : ∃ r₁ r₂ : Fin 6, r₁ ≠ r₂ ∧
      (∀ b : Fin t, (∑ j : Fin 4, a j • base (6*t) j) ⟨6 * b.val + r₁.val, by omega⟩ ≠ 0) ∧
      (∀ b : Fin t, (∑ j : Fin 4, a j • base (6*t) j) ⟨6 * b.val + r₂.val, by omega⟩ ≠ 0) := by
    have ha_ne : a 0 ≠ 0 ∨ a 1 ≠ 0 ∨ a 2 ≠ 0 ∨ a 3 ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hne
      rw [Fin.sum_univ_four, hall.1, hall.2.1, hall.2.2.1, hall.2.2.2]
      simp
    rcases ha_ne with h0 | h1 | h2 | h3
    · by_cases h1 : a 1 = 0
      · refine ⟨⟨0, by omega⟩, ⟨4, by omega⟩, by simp, ?_, ?_⟩
        · intro b; rw [hblock b 0 (by omega)]; simpa using h0
        · intro b; rw [hblock b 4 (by omega)]; simpa [h1] using h0
      · refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, by simp, ?_, ?_⟩
        · intro b; rw [hblock b 0 (by omega)]; simpa using h0
        · intro b; rw [hblock b 2 (by omega)]; simpa using h1
    · by_cases h0 : a 0 = 0
      · refine ⟨⟨2, by omega⟩, ⟨4, by omega⟩, by simp, ?_, ?_⟩
        · intro b; rw [hblock b 2 (by omega)]; simpa using h1
        · intro b; rw [hblock b 4 (by omega)]; simpa [h0] using h1
      · refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, by simp, ?_, ?_⟩
        · intro b; rw [hblock b 0 (by omega)]; simpa using h0
        · intro b; rw [hblock b 2 (by omega)]; simpa using h1
    · by_cases h3 : a 3 = 0
      · refine ⟨⟨1, by omega⟩, ⟨5, by omega⟩, by simp, ?_, ?_⟩
        · intro b; rw [hblock b 1 (by omega)]; simpa using h2
        · intro b; rw [hblock b 5 (by omega)]; simpa [h3] using h2
      · refine ⟨⟨1, by omega⟩, ⟨3, by omega⟩, by simp, ?_, ?_⟩
        · intro b; rw [hblock b 1 (by omega)]; simpa using h2
        · intro b; rw [hblock b 3 (by omega)]; simpa using h3
    · by_cases h2 : a 2 = 0
      · refine ⟨⟨3, by omega⟩, ⟨5, by omega⟩, by simp, ?_, ?_⟩
        · intro b; rw [hblock b 3 (by omega)]; simpa using h3
        · intro b; rw [hblock b 5 (by omega)]; simpa [h2] using h3
      · refine ⟨⟨1, by omega⟩, ⟨3, by omega⟩, by simp, ?_, ?_⟩
        · intro b; rw [hblock b 1 (by omega)]; simpa using h2
        · intro b; rw [hblock b 3 (by omega)]; simpa using h3
  rcases hex with ⟨r₁, r₂, hne_r, hnz₁, hnz₂⟩
  have hne_val : r₁.val ≠ r₂.val := fun h => hne_r (Fin.ext h)
  rw [wt_eq_card]
  let f : Fin t × Fin 2 → Fin (6*t) := fun p =>
    if p.2.val = 0 then ⟨6 * p.1.val + r₁.val, by omega⟩ else ⟨6 * p.1.val + r₂.val, by omega⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨b₁, ⟨c₁, hc₁⟩⟩ ⟨b₂, ⟨c₂, hc₂⟩⟩ hpq
    interval_cases c₁ <;> interval_cases c₂
    · simp only [f, ↓reduceIte, Fin.mk.injEq] at hpq
      refine Prod.ext (Fin.ext ?_) rfl
      dsimp only
      omega
    · simp only [f, ↓reduceIte, Nat.one_ne_zero, Fin.mk.injEq] at hpq
      omega
    · simp only [f, ↓reduceIte, Nat.one_ne_zero, Fin.mk.injEq] at hpq
      omega
    · simp only [f, ↓reduceIte, Nat.one_ne_zero, Fin.mk.injEq] at hpq
      refine Prod.ext (Fin.ext ?_) rfl
      dsimp only
      omega
  have hsub : (Finset.univ : Finset (Fin t × Fin 2)).image f ⊆
      Finset.univ.filter (fun i : Fin (6*t) => (∑ j : Fin 4, a j • base (6*t) j) i ≠ 0) := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨⟨b, ⟨c, hc⟩⟩, _, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    interval_cases c
    · simpa [f] using hnz₁ b
    · simpa [f] using hnz₂ b
  have hcard : 2 * t = ((Finset.univ : Finset (Fin t × Fin 2)).image f).card := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, mul_comm]
  rw [hcard]
  exact Finset.card_le_card hsub

noncomputable def lightSpan (t : ℕ) (h : ℕ)
    (D : Submodule (ZMod 2) (Fin (6*t) → ZMod 2)) : Submodule (ZMod 2) (Fin (6*t) → ZMod 2) :=
  Submodule.span (ZMod 2) {z | z ∈ D ∧ (h + 1) * wt (6*t) z < 2 * t}

lemma lightSpan_le (t h : ℕ) (D : Submodule (ZMod 2) (Fin (6*t) → ZMod 2)) :
    lightSpan t h D ≤ D :=
  Submodule.span_le.mpr (fun _ hz => hz.1)

private noncomputable def evenL (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun := even n
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    unfold even
    by_cases h : i.val % 2 = 0 <;> simp [h]
  map_smul' a x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    unfold even
    by_cases h : i.val % 2 = 0 <;> simp [h]

lemma lightSpan_split (t h : ℕ) (D : Submodule (ZMod 2) (Fin (6*t) → ZMod 2))
    (hsplit : ∀ z ∈ D, even (6*t) z ∈ D) :
    ∀ z ∈ lightSpan t h D, even (6*t) z ∈ lightSpan t h D := by
  have hmap : (lightSpan t h D).map (evenL (6*t)) ≤ lightSpan t h D := by
    unfold lightSpan
    rw [Submodule.map_span_le]
    rintro z ⟨hzD, hzwt⟩
    apply Submodule.subset_span
    refine ⟨hsplit z hzD, ?_⟩
    exact lt_of_le_of_lt (Nat.mul_le_mul_left (h + 1) (wt_even_le (6*t) z)) hzwt
  intro z hz
  exact hmap ⟨z, hz, rfl⟩

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  rcases a with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact absurd rfl ha
  · rfl

private lemma linIndep_insert_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]
    (B : Finset V) (v : V) (hvnotB : v ∉ B)
    (hBli : LinearIndependent (ZMod 2) (fun b : (B : Set V) => (b : V)))
    (hvnot : v ∉ Submodule.span (ZMod 2) (B : Set V)) :
    LinearIndependent (ZMod 2) (fun b : ((insert v B : Finset V) : Set V) => (b : V)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let v0 : ((insert v B : Finset V) : Set V) := ⟨v, by simp⟩
  have hsplit := Finset.add_sum_erase Finset.univ (fun b : ((insert v B : Finset V) : Set V) => g b • (b : V)) (Finset.mem_univ v0)
  rw [← hsplit] at hg
  have hgv : g v0 = 0 := by
    by_contra hgv_ne
    have hgv1 : g v0 = 1 := zmod2_eq_one_of_ne_zero _ hgv_ne
    rw [hgv1, one_smul] at hg
    have hv_eq : v = - ∑ x ∈ Finset.univ.erase v0, g x • (x : V) := eq_neg_of_add_eq_zero_left hg
    apply hvnot
    rw [hv_eq]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun x hx => ?_)
    have hxne : x ≠ v0 := (Finset.mem_erase.mp hx).1
    have hxB : (x : V) ∈ B := by
      have hxmem : (x : V) ∈ insert v B := Finset.mem_coe.mp x.2
      rcases Finset.mem_insert.mp hxmem with hEq | hmem
      · exact absurd (Subtype.ext hEq) hxne
      · exact hmem
    exact Submodule.smul_mem _ _ (Submodule.subset_span hxB)
  rw [hgv, zero_smul, zero_add] at hg
  let g' : ↥(B : Set V) → ZMod 2 := fun b => g ⟨b.1, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp b.2))⟩
  have hg'_sum : ∑ b : ↥(B : Set V), g' b • (b : V) = 0 := by
    rw [← hg]
    refine Finset.sum_bij (fun b _ => (⟨b.1, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp b.2))⟩ : ↥((insert v B : Finset V) : Set V))) ?_ ?_ ?_ ?_
    · intro b _
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hEq
      have : (b : V) = v := congrArg Subtype.val hEq
      exact hvnotB (this ▸ Finset.mem_coe.mp b.2)
    · intro b₁ _ b₂ _ hEq
      exact Subtype.ext (Subtype.mk.inj hEq)
    · intro x hx
      have hxne : x ≠ v0 := (Finset.mem_erase.mp hx).1
      have hxB : (x : V) ∈ B := by
        have hxmem : (x : V) ∈ insert v B := Finset.mem_coe.mp x.2
        rcases Finset.mem_insert.mp hxmem with hEq | hmem
        · exact absurd (Subtype.ext hEq) hxne
        · exact hmem
      exact ⟨⟨x.1, hxB⟩, Finset.mem_univ _, Subtype.ext rfl⟩
    · intro b _; rfl
  have hg'_zero : ∀ b : ↥(B : Set V), g' b = 0 :=
    (Fintype.linearIndependent_iff.mp hBli) g' hg'_sum
  intro x
  by_cases hx : x = v0
  · subst hx; exact hgv
  · have hxB : (x : V) ∈ B := by
      have hxmem : (x : V) ∈ insert v B := Finset.mem_coe.mp x.2
      rcases Finset.mem_insert.mp hxmem with hEq | hmem
      · exact absurd (Subtype.ext hEq) hx
      · exact hmem
    exact hg'_zero ⟨x.1, hxB⟩

lemma lightSpan_disj_and_finrank (t : ℕ) (ht : 0 < t) (h : ℕ)
    (D : Submodule (ZMod 2) (Fin (6*t) → ZMod 2))
    (hbase : ∀ j, base (6*t) j ∈ D)
    (hfin : Module.finrank (ZMod 2) D ≤ h + 4)
    (hcheck_rank : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (base (6*t)))) = 4) :
    lightSpan t h D ⊓ Submodule.span (ZMod 2) (Set.range (base (6*t))) = ⊥ ∧
      Module.finrank (ZMod 2) (lightSpan t h D) ≤ h := by
  classical
  set C : Submodule (ZMod 2) (Fin (6*t) → ZMod 2) :=
    Submodule.span (ZMod 2) (Set.range (base (6*t)))
  have hC_le_D : C ≤ D := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hbase j
  let S : Finset (Fin (6*t) → ZMod 2) :=
    Finset.univ.filter (fun z => z ∈ D ∧ (h + 1) * wt (6*t) z < 2 * t)
  have hS_set : (S : Set (Fin (6*t) → ZMod 2)) = {z | z ∈ D ∧ (h + 1) * wt (6*t) z < 2 * t} := by
    ext z
    simp [S]
  let good : Finset (Fin (6*t) → ZMod 2) → Prop := fun B =>
    LinearIndependent (ZMod 2) (fun b : (B : Set (Fin (6*t) → ZMod 2)) => (b : Fin (6*t) → ZMod 2)) ∧
      Submodule.span (ZMod 2) (B : Set (Fin (6*t) → ZMod 2)) ⊓ C = ⊥
  let ℱ := S.powerset.filter good
  have hempty : (∅ : Finset (Fin (6*t) → ZMod 2)) ∈ ℱ := by
    simp only [ℱ, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and, good]
    refine ⟨?_, by simp⟩
    rw [Finset.coe_empty]
    exact linearIndependent_empty (ZMod 2) (Fin (6*t) → ZMod 2)
  obtain ⟨B, hBmem, hBmax⟩ := Finset.exists_max_image ℱ Finset.card ⟨∅, hempty⟩
  simp only [ℱ, Finset.mem_filter, Finset.mem_powerset] at hBmem
  rcases hBmem with ⟨hBS, hBli, hBdisj⟩
  have hspanB_le_D : Submodule.span (ZMod 2) (B : Set (Fin (6*t) → ZMod 2)) ≤ D := by
    rw [Submodule.span_le]
    intro b hb
    have hbS : b ∈ S := hBS hb
    exact (Finset.mem_filter.mp hbS).2.1
  have hspanB_rank : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (B : Set (Fin (6*t) → ZMod 2))) = B.card := by
    rw [finrank_span_set_eq_card (R := ZMod 2) (s := (B : Set (Fin (6*t) → ZMod 2))) hBli]
    simp
  have hBcard : B.card ≤ h := by
    have hsup : Submodule.span (ZMod 2) (B : Set (Fin (6*t) → ZMod 2)) ⊔ C ≤ D :=
      sup_le hspanB_le_D hC_le_D
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span (ZMod 2) (B : Set (Fin (6*t) → ZMod 2))) C
    rw [hBdisj, finrank_bot, add_zero, hspanB_rank, hcheck_rank] at h1
    have h2 := Submodule.finrank_mono hsup
    omega
  have hS_sub : (S : Set (Fin (6*t) → ZMod 2)) ⊆ Submodule.span (ZMod 2) (B : Set (Fin (6*t) → ZMod 2)) := by
    intro v hv
    by_contra hvnot
    have hvS : v ∈ S := hv
    have hvnotB : v ∉ B := fun hmem => hvnot (Submodule.subset_span hmem)
    let B' := insert v B
    have hB'S : B' ⊆ S := Finset.insert_subset hvS hBS
    have hB'li : LinearIndependent (ZMod 2)
        (fun b : (B' : Set (Fin (6*t) → ZMod 2)) => (b : Fin (6*t) → ZMod 2)) :=
      linIndep_insert_zmod2 B v hvnotB hBli hvnot
    have hB'notdisj : Submodule.span (ZMod 2) (B' : Set (Fin (6*t) → ZMod 2)) ⊓ C ≠ ⊥ := by
      intro hdisj'
      have hB'mem : B' ∈ ℱ := by
        simp only [ℱ, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hB'S, hB'li, hdisj'⟩
      have hle := hBmax B' hB'mem
      have hcard' : B'.card = B.card + 1 := Finset.card_insert_of_notMem hvnotB
      omega
    obtain ⟨c, hcmem, hcne⟩ : ∃ c ∈ Submodule.span (ZMod 2) (B' : Set (Fin (6*t) → ZMod 2)) ⊓ C, c ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hB'notdisj
      rw [Submodule.eq_bot_iff]
      exact hall
    rcases hcmem with ⟨hcB', hcC⟩
    have hcB'2 : c ∈ Submodule.span (ZMod 2) (B' : Set (Fin (6*t) → ZMod 2)) := hcB'
    rw [Submodule.mem_span_finset] at hcB'2
    rcases hcB'2 with ⟨a, _, hc_eq⟩
    let T := B'.filter (fun b => a b ≠ 0)
    have hc_sum : c = ∑ b ∈ T, b := by
      rw [← hc_eq]
      calc ∑ b ∈ B', a b • b
          = ∑ b ∈ T, a b • b := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun b _ => ?_
            split_ifs with h
            · rfl
            · push Not at h; simp [h]
        _ = ∑ b ∈ T, b := by
            refine Finset.sum_congr rfl fun b hb => ?_
            have ha1 : a b = 1 := zmod2_eq_one_of_ne_zero _ (Finset.mem_filter.mp hb).2
            rw [ha1, one_smul]
    have hTne : T.Nonempty := by
      by_contra hTe
      rw [Finset.not_nonempty_iff_eq_empty] at hTe
      rw [hTe, Finset.sum_empty] at hc_sum
      exact hcne hc_sum
    have hTcard : T.card ≤ h + 1 := by
      have h1 : T.card ≤ B'.card := Finset.card_filter_le _ _
      have h2 : B'.card = B.card + 1 := Finset.card_insert_of_notMem hvnotB
      omega
    have hwt_lt : (h + 1) * wt (6*t) c < (h + 1) * (2 * t) := by
      calc (h + 1) * wt (6*t) c
          = (h + 1) * wt (6*t) (∑ b ∈ T, b) := by rw [hc_sum]
        _ ≤ (h + 1) * ∑ b ∈ T, wt (6*t) b := Nat.mul_le_mul_left _ (wt_sum_le (6*t) T id)
        _ = ∑ b ∈ T, (h + 1) * wt (6*t) b := by rw [Finset.mul_sum]
        _ < ∑ _b ∈ T, (2 * t) := by
            refine Finset.sum_lt_sum_of_nonempty hTne fun b hb => ?_
            have hbS : b ∈ S := hB'S (Finset.mem_filter.mp hb).1
            exact (Finset.mem_filter.mp hbS).2.2
        _ = T.card * (2 * t) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (h + 1) * (2 * t) := Nat.mul_le_mul_right _ hTcard
    have hwt_lt2 : wt (6*t) c < 2 * t := Nat.lt_of_mul_lt_mul_left hwt_lt
    have hwt_ge : 2 * t ≤ wt (6*t) c := check_wt_ge t ht c hcC hcne
    omega
  have hlight_le : lightSpan t h D ≤ Submodule.span (ZMod 2) (B : Set (Fin (6*t) → ZMod 2)) := by
    unfold lightSpan
    rw [← hS_set, Submodule.span_le]
    exact hS_sub
  refine ⟨?_, ?_⟩
  · apply le_antisymm _ bot_le
    calc lightSpan t h D ⊓ C
        ≤ Submodule.span (ZMod 2) (B : Set (Fin (6*t) → ZMod 2)) ⊓ C := inf_le_inf_right C hlight_le
      _ = ⊥ := hBdisj
  · calc Module.finrank (ZMod 2) (lightSpan t h D)
        ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (B : Set (Fin (6*t) → ZMod 2))) :=
          Submodule.finrank_mono hlight_le
      _ = B.card := hspanB_rank
      _ ≤ h := hBcard

lemma outside_lightSpan_wt (t h : ℕ) (D : Submodule (ZMod 2) (Fin (6*t) → ZMod 2))
    (z : Fin (6*t) → ZMod 2) (hzD : z ∈ D) (hzn : z ∉ lightSpan t h D) :
    2 * t ≤ (h + 1) * wt (6*t) z := by
  by_contra hlt
  push Not at hlt
  exact hzn (Submodule.subset_span ⟨hzD, hlt⟩)

/-! Section 3: Even/Odd Lane Decomposition & Exponential Decay -/

def ev (m : ℕ) (x : Fin (2*m) → ZMod 2) (k : Fin m) : ZMod 2 :=
  x ⟨2*k.val, by omega⟩

def od (m : ℕ) (x : Fin (2*m) → ZMod 2) (k : Fin m) : ZMod 2 :=
  x ⟨2*k.val + 1, by omega⟩

def mergeEO (m : ℕ) (u v : Fin m → ZMod 2) (i : Fin (2*m)) : ZMod 2 :=
  if i.val % 2 = 0 then u ⟨i.val / 2, by omega⟩ else v ⟨i.val / 2, by omega⟩

def covE (m : ℕ) (hm : 0 < m) (v : Fin m → ZMod 2) (k : Fin m) : Prop :=
  v (ix m hm (k.val + m - 1)) = 1 ∨ v k = 1

instance decCovE (m : ℕ) (hm : 0 < m) (v : Fin m → ZMod 2) (k : Fin m) :
    Decidable (covE m hm v k) :=
  instDecidableOr

private lemma mergeEO_even (m : ℕ) (u v : Fin m → ZMod 2) (k : Fin m) :
    mergeEO m u v ⟨2 * k.val, by omega⟩ = u k := by
  unfold mergeEO
  have hp : (2 * k.val) % 2 = 0 := by omega
  simp only [hp, ↓reduceIte]
  congr 1
  apply Fin.ext
  dsimp
  omega

private lemma mergeEO_odd (m : ℕ) (u v : Fin m → ZMod 2) (k : Fin m) :
    mergeEO m u v ⟨2 * k.val + 1, by omega⟩ = v k := by
  unfold mergeEO
  have hp : (2 * k.val + 1) % 2 ≠ 0 := by omega
  simp only [hp, ↓reduceIte]
  congr 1
  apply Fin.ext
  dsimp
  omega

private def eoIdx (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2*m) where
  toFun
    | Sum.inl k => ⟨2 * k.val, by omega⟩
    | Sum.inr k => ⟨2 * k.val + 1, by omega⟩
  invFun i :=
    if i.val % 2 = 0 then Sum.inl ⟨i.val / 2, by omega⟩ else Sum.inr ⟨i.val / 2, by omega⟩
  left_inv s := by
    cases s with
    | inl k =>
      have h : (2 * k.val) % 2 = 0 := by omega
      simp only [h, ↓reduceIte]
      congr 1; apply Fin.ext; dsimp; omega
    | inr k =>
      have h : (2 * k.val + 1) % 2 ≠ 0 := by omega
      simp only [h, ↓reduceIte]
      congr 1; apply Fin.ext; dsimp; omega
  right_inv i := by
    by_cases h : i.val % 2 = 0
    · simp only [h, ↓reduceIte]
      apply Fin.ext
      dsimp
      omega
    · simp only [h, ↓reduceIte]
      apply Fin.ext
      dsimp
      omega

private def eoEquiv (m : ℕ) :
    (Fin (2*m) → ZMod 2) ≃ (Fin m → ZMod 2) × (Fin m → ZMod 2) where
  toFun x := (ev m x, od m x)
  invFun p := mergeEO m p.1 p.2
  left_inv x := by
    funext i
    unfold mergeEO ev od
    by_cases h : i.val % 2 = 0
    · simp only [h, ↓reduceIte]
      congr 1; apply Fin.ext; dsimp; omega
    · simp only [h, ↓reduceIte]
      congr 1; apply Fin.ext; dsimp; omega
  right_inv p := by
    rcases p with ⟨u, v⟩
    ext k
    · exact mergeEO_even m u v k
    · exact mergeEO_odd m u v k

private lemma dot_mergeEO (m : ℕ) (z : Fin (2*m) → ZMod 2) (u v : Fin m → ZMod 2) :
    dot (2*m) z (mergeEO m u v) = dot m (ev m z) u + dot m (od m z) v := by
  unfold dot
  rw [← Equiv.sum_comp (eoIdx m) (fun i => z i * mergeEO m u v i), Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [eoIdx, Equiv.coe_fn_mk, ev, mergeEO_even]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [eoIdx, Equiv.coe_fn_mk, od, mergeEO_odd]

private lemma sgn_zero : sgn 0 = 1 := rfl

private lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private lemma sgn_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

private lemma zmod2_mul_eq_zero_iff (a b : ZMod 2) : a * b = 0 ↔ (b = 1 → a = 0) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private lemma ix_pred_succ (m : ℕ) (hm : 0 < m) (k : Fin m) :
    ix m hm ((ix m hm (k.val + m - 1)).val + 1) = k := by
  rw [ix_add]
  apply Fin.ext
  simp only [ix]
  have h : k.val + m - 1 + 1 = k.val + m := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]

private lemma ix_succ_pred (m : ℕ) (hm : 0 < m) (k : Fin m) :
    ix m hm ((ix m hm (k.val + 1)).val + m - 1) = k := by
  apply Fin.ext
  simp only [ix]
  have h1 : (k.val + 1) % m + m - 1 = (k.val + 1) % m + (m - 1) := by omega
  rw [h1, Nat.mod_add_mod]
  have h3 : k.val + 1 + (m - 1) = k.val + m := by omega
  rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]

private lemma ind_mergeEO (m : ℕ) (hm : 0 < m) (u v : Fin m → ZMod 2) :
    ind (2*m) (by omega) (mergeEO m u v) ↔ ∀ k : Fin m, covE m hm v k → u k = 0 := by
  unfold ind covE
  constructor
  · intro hind k hcov
    rcases hcov with hL | hR
    · let k' := ix m hm (k.val + m - 1)
      have h := hind ⟨2 * k'.val + 1, by omega⟩
      have hnext : ix (2*m) (by omega) (2 * k'.val + 1 + 1) = ⟨2 * k.val, by omega⟩ := by
        apply Fin.ext
        simp only [ix]
        have h2 : (2 * k'.val + 1 + 1) % (2 * m) = 2 * ((k'.val + 1) % m) := by
          have : 2 * k'.val + 1 + 1 = 2 * (k'.val + 1) := by omega
          rw [this, Nat.mul_mod_mul_left]
        rw [h2]
        have hk : (k'.val + 1) % m = k.val := congrArg Fin.val (ix_pred_succ m hm k)
        rw [hk]
      rw [mergeEO_odd, hnext, mergeEO_even, hL, one_mul] at h
      exact h
    · have h := hind ⟨2 * k.val, by omega⟩
      have hnext : ix (2*m) (by omega) (2 * k.val + 1) = ⟨2 * k.val + 1, by omega⟩ := by
        apply Fin.ext
        simp only [ix]
        exact Nat.mod_eq_of_lt (by omega)
      rw [mergeEO_even, hnext, mergeEO_odd, hR, mul_one] at h
      exact h
  · intro hcov i
    by_cases hp : i.val % 2 = 0
    · let k : Fin m := ⟨i.val / 2, by omega⟩
      have hi : i = ⟨2 * k.val, by omega⟩ := Fin.ext (by dsimp [k]; omega)
      rw [hi]
      have hnext : ix (2*m) (by omega) (2 * k.val + 1) = ⟨2 * k.val + 1, by omega⟩ := by
        apply Fin.ext; simp only [ix]; exact Nat.mod_eq_of_lt (by omega)
      rw [mergeEO_even, hnext, mergeEO_odd, zmod2_mul_eq_zero_iff]
      intro hv
      exact hcov k (Or.inr hv)
    · let k' : Fin m := ⟨i.val / 2, by omega⟩
      let k : Fin m := ix m hm (k'.val + 1)
      have hi : i = ⟨2 * k'.val + 1, by omega⟩ := Fin.ext (by dsimp [k']; omega)
      rw [hi]
      have hnext : ix (2*m) (by omega) (2 * k'.val + 1 + 1) = ⟨2 * k.val, by omega⟩ := by
        apply Fin.ext
        simp only [ix, k]
        have : 2 * k'.val + 1 + 1 = 2 * (k'.val + 1) := by omega
        rw [this, Nat.mul_mod_mul_left]
      rw [mergeEO_odd, hnext, mergeEO_even, mul_comm, zmod2_mul_eq_zero_iff]
      intro hv
      have hk' : ix m hm (k.val + m - 1) = k' := ix_succ_pred m hm k'
      exact hcov k (Or.inl (by rwa [hk']))

private lemma sum_zmod2 (f : ZMod 2 → ℤ) : (∑ a : ZMod 2, f a) = f 0 + f 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide)]

private lemma sum_u_lane (m : ℕ) (P : Fin m → Prop) [DecidablePred P] (w : Fin m → ZMod 2) :
    (∑ u : Fin m → ZMod 2, if (∀ k : Fin m, P k → u k = 0) then sgn (dot m w u) else 0) =
      if ∀ k : Fin m, w k = 1 → P k then
        (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ P k)).card
      else 0 := by
  have hfactor : ∀ u : Fin m → ZMod 2,
      (if (∀ k : Fin m, P k → u k = 0) then sgn (dot m w u) else 0) =
        ∏ k : Fin m, (if P k → u k = 0 then sgn (w k * u k) else 0) := by
    intro u
    split_ifs with h
    · unfold dot
      rw [sgn_sum]
      refine Finset.prod_congr rfl fun k _ => ?_
      split_ifs with hk
      · rfl
      · exact absurd (h k) hk
    · push Not at h
      rcases h with ⟨k₀, hPk₀, huk₀⟩
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ k₀) ?_
      have hnot : ¬ (P k₀ → u k₀ = 0) := fun hi => huk₀ (hi hPk₀)
      simp only [hnot, ↓reduceIte]
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun k a => if P k → a = 0 then sgn (w k * a) else 0)]
  have hterm : ∀ k : Fin m,
      (∑ a : ZMod 2, if P k → a = 0 then sgn (w k * a) else 0) =
        if P k then (1 : ℤ) else if w k = 1 then 0 else 2 := by
    intro k
    rw [sum_zmod2]
    by_cases hP : P k
    · simp [hP, sgn_zero]
    · simp only [hP, false_implies, ↓reduceIte, mul_zero, mul_one, sgn_zero]
      rcases zmod2_cases (w k) with hw0 | hw1
      · rw [hw0]; decide
      · rw [hw1]; decide
  simp_rw [hterm]
  split_ifs with hall
  · have hsimp : ∀ k : Fin m,
        (if P k then (1 : ℤ) else if w k = 1 then 0 else 2) =
          if ¬ P k then (2 : ℤ) else 1 := by
      intro k
      by_cases hP : P k
      · simp [hP]
      · have hw : w k ≠ 1 := fun hw1 => hP (hall k hw1)
        simp [hP, hw]
    simp_rw [hsimp]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  · push Not at hall
    rcases hall with ⟨k₀, hw1, hnotP⟩
    refine Finset.prod_eq_zero (Finset.mem_univ k₀) ?_
    simp [hnotP, hw1]

lemma tw0_lane_sum (m : ℕ) (hm : 0 < m) (z : Fin (2*m) → ZMod 2) :
    tw0 (2*m) (by omega) z =
      ∑ v : Fin m → ZMod 2, sgn (dot m (od m z) v) *
        (if ∀ k : Fin m, ev m z k = 1 → covE m hm v k then
          (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card
        else 0) := by
  rw [tw0_eq_sum]
  have h1 : (∑ x : Fin (2*m) → ZMod 2, if ind (2*m) (by omega) x then sgn (dot (2*m) z x) else 0) =
      ∑ p : (Fin m → ZMod 2) × (Fin m → ZMod 2),
        if ind (2*m) (by omega) (mergeEO m p.1 p.2) then
          sgn (dot (2*m) z (mergeEO m p.1 p.2))
        else 0 := by
    symm
    exact Fintype.sum_equiv (eoEquiv m).symm _ _ (fun _ => rfl)
  rw [h1, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hinner : (∑ u : Fin m → ZMod 2,
      if ind (2*m) (by omega) (mergeEO m u v) then
        sgn (dot (2*m) z (mergeEO m u v))
      else 0) =
      sgn (dot m (od m z) v) *
        ∑ u : Fin m → ZMod 2,
          if (∀ k : Fin m, covE m hm v k → u k = 0) then sgn (dot m (ev m z) u) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with h1 h2 h2
    · rw [dot_mergeEO, sgn_add]; ring
    · exact absurd ((ind_mergeEO m hm u v).mp h1) h2
    · exact absurd ((ind_mergeEO m hm u v).mpr h2) h1
    · ring
  rw [hinner]
  congr 1
  exact sum_u_lane m (covE m hm v) (ev m z)

lemma tw0_abs_le_covE (m : ℕ) (hm : 0 < m) (z : Fin (2*m) → ZMod 2)
    (P : Finset (Fin m)) (hP : ∀ k ∈ P, ev m z k = 1) :
    |tw0 (2*m) (by omega) z| ≤
      ((Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
        ind (2*m) (by omega) x ∧ ∀ k ∈ P, covE m hm (od m x) k)).card : ℤ) := by
  rw [tw0_lane_sum m hm z]
  have h1 : |∑ v : Fin m → ZMod 2, sgn (dot m (od m z) v) *
      (if ∀ k : Fin m, ev m z k = 1 → covE m hm v k then
        (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card
      else 0)| ≤
      ∑ v : Fin m → ZMod 2,
        if ∀ k ∈ P, covE m hm v k then
          (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card
        else 0 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun v _ => ?_
    rw [abs_mul]
    have hsgn : |sgn (dot m (od m z) v)| = 1 := by
      unfold sgn
      split_ifs <;> decide
    rw [hsgn, one_mul]
    split_ifs with ha hb
    · rw [abs_of_nonneg (by positivity)]
    · exact absurd (fun k hk => ha k (hP k hk)) hb
    · rw [abs_zero]; positivity
    · rw [abs_zero]
  refine le_trans h1 ?_
  have hrhs : ((Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
      ind (2*m) (by omega) x ∧ ∀ k ∈ P, covE m hm (od m x) k)).card : ℤ) =
      ∑ v : Fin m → ZMod 2,
        if ∀ k ∈ P, covE m hm v k then
          (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card
        else 0 := by
    rw [Finset.card_filter, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [← Equiv.sum_comp (eoEquiv m).symm]
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hod : ∀ u : Fin m → ZMod 2, od m ((eoEquiv m).symm (u, v)) = v := fun u => by
      change (eoEquiv m ((eoEquiv m).symm (u, v))).2 = v
      rw [(eoEquiv m).apply_symm_apply]
    split_ifs with hvP
    · have heq : (∑ u : Fin m → ZMod 2,
          if ind (2*m) (by omega) ((eoEquiv m).symm (u, v)) ∧
              ∀ k ∈ P, covE m hm (od m ((eoEquiv m).symm (u, v))) k then (1 : ℤ) else 0) =
          ∑ u : Fin m → ZMod 2,
            if ∀ k : Fin m, covE m hm v k → u k = 0 then sgn (dot m 0 u) else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hod u]
        have hdot0 : dot m 0 u = 0 := by simp [dot]
        rw [hdot0, sgn_zero]
        split_ifs with hu1 hu2 hu2
        · rfl
        · exact absurd ((ind_mergeEO m hm u v).mp hu1.1) hu2
        · exact absurd ⟨(ind_mergeEO m hm u v).mpr hu2, hvP⟩ hu1
        · rfl
      rw [heq, sum_u_lane]
      have h0 : ∀ k : Fin m, (0 : Fin m → ZMod 2) k = 1 → covE m hm v k := fun k hk => by simp at hk
      exact ite_eq_left_iff.mpr (fun h0' => absurd h0 h0')
    · refine Finset.sum_eq_zero fun u _ => ?_
      rw [hod u]
      have hnot : ¬ (ind (2*m) (by omega) ((eoEquiv m).symm (u, v)) ∧ ∀ k ∈ P, covE m hm v k) :=
        fun h => hvP h.2
      simp only [hnot, ↓reduceIte]
  rw [hrhs]

private lemma ind_covE_step (t : ℕ) (ht : 0 < t) (k₀ : Fin (3*t)) (P' : Finset (Fin (3*t)))
    (hk₀ : k₀ ∉ P') (hmod' : ∀ k ∈ P', k.val % 3 = k₀.val % 3) :
    5 * (Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
      ind (2*(3*t)) (by omega) x ∧
        ∀ k ∈ insert k₀ P', covE (3*t) (by omega) (od (3*t) x) k)).card ≤
    3 * (Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
      ind (2*(3*t)) (by omega) x ∧
        ∀ k ∈ P', covE (3*t) (by omega) (od (3*t) x) k)).card := by
  let n := 2 * (3 * t)
  have hn : 0 < n := by omega
  have hm : 0 < 3 * t := by omega
  let iL : Fin n := ix n hn (2 * k₀.val + n - 1)
  let iM : Fin n := ⟨2 * k₀.val, by omega⟩
  let iR : Fin n := ⟨2 * k₀.val + 1, by omega⟩
  have hiL_val : iL.val = if k₀.val = 0 then n - 1 else 2 * k₀.val - 1 := by
    simp only [iL, ix]
    split_ifs with hk0
    · rw [hk0]
      have h1 : 2 * 0 + n - 1 = n - 1 := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    · have h1 : 2 * k₀.val + n - 1 = (2 * k₀.val - 1) + n := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hiL_ne_iM : iL ≠ iM := by
    intro h; have := congrArg Fin.val h; simp only [iM, hiL_val] at this; split_ifs at this <;> omega
  have hiM_ne_iR : iM ≠ iR := by
    intro h; have := congrArg Fin.val h; simp only [iM, iR] at this; omega
  have hiL_ne_iR : iL ≠ iR := by
    intro h; have := congrArg Fin.val h; simp only [iR, hiL_val] at this; split_ifs at this <;> omega
  have hix_iL : ix n hn (iL.val + 1) = iM := by
    apply Fin.ext
    simp only [ix, iM, hiL_val]
    split_ifs with hk0
    · rw [hk0]
      have h1 : n - 1 + 1 = n := by omega
      rw [h1, Nat.mod_self]
    · have h1 : 2 * k₀.val - 1 + 1 = 2 * k₀.val := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
  have hix_iM : ix n hn (iM.val + 1) = iR := by
    apply Fin.ext
    simp only [ix, iM, iR]
    exact Nat.mod_eq_of_lt (by omega)
  have hix_eq_iM : ∀ i : Fin n, ix n hn (i.val + 1) = iM ↔ i = iL := by
    intro i
    rw [← hix_iL]
    exact (shIdx n hn 1).injective.eq_iff
  have hcov_k0 : ∀ x : Fin n → ZMod 2,
      covE (3*t) hm (od (3*t) x) k₀ ↔ x iL = 1 ∨ x iR = 1 := by
    intro x
    unfold covE od
    have hidx : (⟨2 * (ix (3*t) hm (k₀.val + 3 * t - 1)).val + 1, by omega⟩ : Fin n) = iL := by
      apply Fin.ext
      simp only [ix, hiL_val]
      split_ifs with hk0
      · rw [hk0]
        have h1 : 0 + 3 * t - 1 = 3 * t - 1 := by omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]
        omega
      · have h1 : k₀.val + 3 * t - 1 = (k₀.val - 1) + 3 * t := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    rw [hidx]
  have hcov_other : ∀ k ∈ P', ∀ x y : Fin n → ZMod 2,
      (∀ i : Fin n, i ≠ iL → i ≠ iM → i ≠ iR → x i = y i) →
      (covE (3*t) hm (od (3*t) x) k ↔ covE (3*t) hm (od (3*t) y) k) := by
    intro k hk x y hxy
    have hne : k ≠ k₀ := fun heq => hk₀ (heq ▸ hk)
    have hne_val : k.val ≠ k₀.val := fun h => hne (Fin.ext h)
    have hmodk : k.val % 3 = k₀.val % 3 := hmod' k hk
    let jL : Fin n := ⟨2 * (ix (3*t) hm (k.val + 3 * t - 1)).val + 1, by omega⟩
    let jR : Fin n := ⟨2 * k.val + 1, by omega⟩
    have hjL_val : jL.val = if k.val = 0 then n - 1 else 2 * k.val - 1 := by
      simp only [jL, ix]
      split_ifs with hk0
      · rw [hk0]
        have h1 : 0 + 3 * t - 1 = 3 * t - 1 := by omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]
        omega
      · have h1 : k.val + 3 * t - 1 = (k.val - 1) + 3 * t := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    have hjL_ne_iL : jL ≠ iL := by
      intro h; have := congrArg Fin.val h; rw [hjL_val, hiL_val] at this; split_ifs at this <;> omega
    have hjL_ne_iM : jL ≠ iM := by
      intro h; have := congrArg Fin.val h; simp only [iM] at this; rw [hjL_val] at this; split_ifs at this <;> omega
    have hjL_ne_iR : jL ≠ iR := by
      intro h; have := congrArg Fin.val h; simp only [iR] at this; rw [hjL_val] at this; split_ifs at this <;> omega
    have hjR_ne_iL : jR ≠ iL := by
      intro h; have := congrArg Fin.val h; simp only [jR] at this; rw [hiL_val] at this; split_ifs at this <;> omega
    have hjR_ne_iM : jR ≠ iM := by
      intro h; have := congrArg Fin.val h; simp only [jR, iM] at this; omega
    have hjR_ne_iR : jR ≠ iR := by
      intro h; have := congrArg Fin.val h; simp only [jR, iR] at this; omega
    unfold covE od
    rw [hxy jL hjL_ne_iL hjL_ne_iM hjL_ne_iR, hxy jR hjR_ne_iL hjR_ne_iM hjR_ne_iR]
  let AP := Finset.univ.filter (fun x : Fin n → ZMod 2 =>
    ind n hn x ∧ ∀ k ∈ P', covE (3*t) hm (od (3*t) x) k)
  let C := AP.filter (fun x => covE (3*t) hm (od (3*t) x) k₀)
  let U := AP.filter (fun x => ¬ covE (3*t) hm (od (3*t) x) k₀)
  have hC_eq : Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      ind n hn x ∧ ∀ k ∈ insert k₀ P', covE (3*t) hm (od (3*t) x) k) = C := by
    ext x
    simp only [C, AP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      forall_eq_or_imp]
    tauto
  change 5 * (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      ind n hn x ∧ ∀ k ∈ insert k₀ P', covE (3*t) hm (od (3*t) x) k)).card ≤ 3 * AP.card
  rw [hC_eq]
  have hsplit : C.card + U.card = AP.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not AP AP _),
      Finset.filter_union_filter_not_eq]
  let zeroW : (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun x i =>
    if i = iL ∨ i = iM ∨ i = iR then 0 else x i
  let F := AP.image zeroW
  have hC_fib : C.card = ∑ y ∈ F, (C.filter (fun x => zeroW x = y)).card := by
    refine Finset.card_eq_sum_card_fiberwise fun x hx => ?_
    exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩
  have hU_fib : U.card = ∑ y ∈ F, (U.filter (fun x => zeroW x = y)).card := by
    refine Finset.card_eq_sum_card_fiberwise fun x hx => ?_
    exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩
  have h2C_le_3U : 2 * C.card ≤ 3 * U.card := by
    rw [hC_fib, hU_fib, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    rcases Finset.mem_image.mp hy with ⟨x₀, hx₀, rfl⟩
    have hx₀_ind : ind n hn x₀ := (Finset.mem_filter.mp hx₀).2.1
    have hx₀_cov : ∀ k ∈ P', covE (3*t) hm (od (3*t) x₀) k := (Finset.mem_filter.mp hx₀).2.2
    have hCy_le : (C.filter (fun x => zeroW x = zeroW x₀)).card ≤ 3 := by
      let T3 : Finset (ZMod 2 × ZMod 2) := {(1, 0), (0, 1), (1, 1)}
      have hT3 : T3.card = 3 := by decide
      rw [← hT3]
      refine Finset.card_le_card_of_injOn (fun x => (x iL, x iR)) ?_ ?_
      · intro x hx
        have hxC : x ∈ C := (Finset.mem_filter.mp hx).1
        have hcov0 : x iL = 1 ∨ x iR = 1 := (hcov_k0 x).mp (Finset.mem_filter.mp hxC).2
        have hL : x iL = 0 ∨ x iL = 1 := zmod2_cases (x iL)
        have hR : x iR = 0 ∨ x iR = 1 := zmod2_cases (x iR)
        simp only [T3, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rcases hL with hL0 | hL1 <;> rcases hR with hR0 | hR1
        · rcases hcov0 with h | h <;> simp_all
        · exact Or.inr (Or.inl ⟨hL0, hR1⟩)
        · exact Or.inl ⟨hL1, hR0⟩
        · exact Or.inr (Or.inr ⟨hL1, hR1⟩)
      · intro x₁ hx₁ x₂ hx₂ hpair
        have hx₁C : x₁ ∈ C := (Finset.mem_filter.mp hx₁).1
        have hx₂C : x₂ ∈ C := (Finset.mem_filter.mp hx₂).1
        have hz₁ : zeroW x₁ = zeroW x₀ := (Finset.mem_filter.mp hx₁).2
        have hz₂ : zeroW x₂ = zeroW x₀ := (Finset.mem_filter.mp hx₂).2
        have hM0 : ∀ x ∈ C, x iM = 0 := by
          intro x hxC
          have hind : ind n hn x := (Finset.mem_filter.mp (Finset.mem_filter.mp hxC).1).2.1
          have hcov0 : x iL = 1 ∨ x iR = 1 := (hcov_k0 x).mp (Finset.mem_filter.mp hxC).2
          rcases hcov0 with hL | hR
          · have h := hind iL; rw [hix_iL, hL, one_mul] at h; exact h
          · have h := hind iM; rw [hix_iM, hR, mul_one] at h; exact h
        have hL_eq : x₁ iL = x₂ iL := congrArg Prod.fst hpair
        have hR_eq : x₁ iR = x₂ iR := congrArg Prod.snd hpair
        have hM_eq : x₁ iM = x₂ iM := by rw [hM0 x₁ hx₁C, hM0 x₂ hx₂C]
        funext i
        by_cases hiL : i = iL
        · subst hiL; exact hL_eq
        · by_cases hiM : i = iM
          · subst hiM; exact hM_eq
          · by_cases hiR : i = iR
            · subst hiR; exact hR_eq
            · have hz := congrFun (hz₁.trans hz₂.symm) i
              simpa [zeroW, hiL, hiM, hiR] using hz
    have hUy_ge : 2 ≤ (U.filter (fun x => zeroW x = zeroW x₀)).card := by
      let x₁ : Fin n → ZMod 2 := zeroW x₀
      let x₂ : Fin n → ZMod 2 := Function.update (zeroW x₀) iM 1
      have hx₁_zeroW : zeroW x₁ = zeroW x₀ := by
        funext i
        simp only [zeroW, x₁]
        split_ifs <;> rfl
      have hx₂_zeroW : zeroW x₂ = zeroW x₀ := by
        funext i
        simp only [zeroW, x₂]
        by_cases h : i = iL ∨ i = iM ∨ i = iR
        · simp [h]
        · have hiM : i ≠ iM := fun heq => h (Or.inr (Or.inl heq))
          simp [h, Function.update_of_ne hiM]
      have hx₁_ind : ind n hn x₁ := by
        intro i
        simp only [x₁, zeroW]
        split_ifs
        · simp
        · simp
        · simp
        · exact hx₀_ind i
      have hx₂_ind : ind n hn x₂ := by
        intro i
        by_cases hiM : i = iM
        · subst hiM
          rw [hix_iM]
          have hx₂R : x₂ iR = 0 := by
            simp [x₂, Function.update_of_ne hiM_ne_iR.symm, zeroW]
          rw [hx₂R, mul_zero]
        · by_cases hnext : ix n hn (i.val + 1) = iM
          · have hiL : i = iL := (hix_eq_iM i).mp hnext
            subst hiL
            have hx₂L : x₂ iL = 0 := by
              simp [x₂, Function.update_of_ne hiL_ne_iM, zeroW]
            rw [hx₂L, zero_mul]
          · simp only [x₂, Function.update_of_ne hiM, Function.update_of_ne hnext]
            exact hx₁_ind i
      have hx₁_covP : ∀ k ∈ P', covE (3*t) hm (od (3*t) x₁) k := by
        intro k hk
        rw [hcov_other k hk x₁ x₀ (fun i h1 h2 h3 => by simp [x₁, zeroW, h1, h2, h3])]
        exact hx₀_cov k hk
      have hx₂_covP : ∀ k ∈ P', covE (3*t) hm (od (3*t) x₂) k := by
        intro k hk
        rw [hcov_other k hk x₂ x₀ (fun i h1 h2 h3 => by simp [x₂, zeroW, h1, h2, h3])]
        exact hx₀_cov k hk
      have hx₁_ncov0 : ¬ covE (3*t) hm (od (3*t) x₁) k₀ := by
        rw [hcov_k0]
        simp [x₁, zeroW]
      have hx₂_ncov0 : ¬ covE (3*t) hm (od (3*t) x₂) k₀ := by
        rw [hcov_k0]
        simp [x₂, Function.update_of_ne hiL_ne_iM, Function.update_of_ne hiM_ne_iR.symm, zeroW]
      have hx₁_mem : x₁ ∈ U.filter (fun x => zeroW x = zeroW x₀) := by
        simp only [Finset.mem_filter, U, AP, Finset.mem_univ, true_and]
        exact ⟨⟨⟨hx₁_ind, hx₁_covP⟩, hx₁_ncov0⟩, hx₁_zeroW⟩
      have hx₂_mem : x₂ ∈ U.filter (fun x => zeroW x = zeroW x₀) := by
        simp only [Finset.mem_filter, U, AP, Finset.mem_univ, true_and]
        exact ⟨⟨⟨hx₂_ind, hx₂_covP⟩, hx₂_ncov0⟩, hx₂_zeroW⟩
      have hx₁_ne_x₂ : x₁ ≠ x₂ := by
        intro h
        have hM := congrFun h iM
        simp [x₁, x₂, zeroW] at hM
      have hpair_sub : ({x₁, x₂} : Finset (Fin n → ZMod 2)) ⊆ U.filter (fun x => zeroW x = zeroW x₀) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hx₁_mem
        · exact hx₂_mem
      have hpair_card : ({x₁, x₂} : Finset (Fin n → ZMod 2)).card = 2 := Finset.card_pair hx₁_ne_x₂
      calc 2 = ({x₁, x₂} : Finset (Fin n → ZMod 2)).card := hpair_card.symm
        _ ≤ (U.filter (fun x => zeroW x = zeroW x₀)).card := Finset.card_le_card hpair_sub
    omega
  omega

lemma ind_covE_35_bound (t : ℕ) (ht : 0 < t) (c : ℕ) (P : Finset (Fin (3*t)))
    (hmod : ∀ k ∈ P, k.val % 3 = c) :
    5 ^ P.card * (Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
      ind (2*(3*t)) (by omega) x ∧ ∀ k ∈ P, covE (3*t) (by omega) (od (3*t) x) k)).card ≤
    3 ^ P.card * (Finset.univ.filter (ind (2*(3*t)) (by omega))).card := by
  induction P using Finset.induction_on with
  | empty =>
    simp
  | insert k₀ P' hk₀ ih =>
    have hmodP' : ∀ k ∈ P', k.val % 3 = c := fun k hk => hmod k (Finset.mem_insert_of_mem hk)
    have hmodk0 : k₀.val % 3 = c := hmod k₀ (Finset.mem_insert_self k₀ P')
    have hmod_eq : ∀ k ∈ P', k.val % 3 = k₀.val % 3 := fun k hk => (hmodP' k hk).trans hmodk0.symm
    have hstep := ind_covE_step t ht k₀ P' hk₀ hmod_eq
    have hih := ih hmodP'
    rw [Finset.card_insert_of_notMem hk₀, pow_succ, pow_succ]
    calc 5 ^ P'.card * 5 * (Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
            ind (2*(3*t)) (by omega) x ∧
              ∀ k ∈ insert k₀ P', covE (3*t) (by omega) (od (3*t) x) k)).card
        = 5 ^ P'.card * (5 * (Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
            ind (2*(3*t)) (by omega) x ∧
              ∀ k ∈ insert k₀ P', covE (3*t) (by omega) (od (3*t) x) k)).card) := by ring
      _ ≤ 5 ^ P'.card * (3 * (Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
            ind (2*(3*t)) (by omega) x ∧
              ∀ k ∈ P', covE (3*t) (by omega) (od (3*t) x) k)).card) := Nat.mul_le_mul_left _ hstep
      _ = 3 * (5 ^ P'.card * (Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
            ind (2*(3*t)) (by omega) x ∧
              ∀ k ∈ P', covE (3*t) (by omega) (od (3*t) x) k)).card) := by ring
      _ ≤ 3 * (3 ^ P'.card * (Finset.univ.filter (ind (2*(3*t)) (by omega))).card) :=
            Nat.mul_le_mul_left _ hih
      _ = 3 ^ P'.card * 3 * (Finset.univ.filter (ind (2*(3*t)) (by omega))).card := by ring

private lemma wt_eq_ev_add_od (m : ℕ) (z : Fin (2*m) → ZMod 2) :
    wt (2*m) z =
      (Finset.univ.filter (fun k : Fin m => ev m z k = 1)).card +
      (Finset.univ.filter (fun k : Fin m => od m z k = 1)).card := by
  rw [wt_eq_card, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  rw [← Equiv.sum_comp (eoIdx m), Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hiff : z (eoIdx m (Sum.inl k)) ≠ 0 ↔ ev m z k = 1 := by
      change ev m z k ≠ 0 ↔ ev m z k = 1
      rcases zmod2_cases (ev m z k) with h0 | h1
      · simp [h0]
      · simp [h1]
    exact if_congr hiff rfl rfl
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hiff : z (eoIdx m (Sum.inr k)) ≠ 0 ↔ od m z k = 1 := by
      change od m z k ≠ 0 ↔ od m z k = 1
      rcases zmod2_cases (od m z k) with h0 | h1
      · simp [h0]
      · simp [h1]
    exact if_congr hiff rfl rfl

private lemma ev_sh_one_eq_od (m : ℕ) (hm : 0 < m) (z : Fin (2*m) → ZMod 2) :
    ev m (sh (2*m) (by omega) 1 z) = od m z := by
  funext k
  unfold ev od sh ix
  congr 1
  apply Fin.ext
  dsimp only
  have hk := k.isLt
  exact Nat.mod_eq_of_lt (by omega)

private lemma heavy_bound_aux (t : ℕ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h)
    (ht_big : 100 * (h + 4)^2 ≤ t) (z : Fin (2*(3*t)) → ZMod 2)
    (hwt : 2 * t ≤ (h + 1) * wt (2*(3*t)) z) :
    (15625 : ℤ) ^ (h + 4) * |tw0 (2*(3*t)) (by omega) z| ≤
      (729 : ℤ) ^ (h + 4) * ((Finset.univ.filter (ind (2*(3*t)) (by omega))).card : ℤ) := by
  have hm : 0 < 3 * t := by omega
  have hn : 0 < 2 * (3 * t) := by omega
  have hwt_split := wt_eq_ev_add_od (3*t) z
  obtain ⟨z', htw_eq, hcard_ge⟩ : ∃ z' : Fin (2*(3*t)) → ZMod 2,
      tw0 (2*(3*t)) hn z' = tw0 (2*(3*t)) hn z ∧
      wt (2*(3*t)) z ≤ 2 * (Finset.univ.filter (fun k : Fin (3*t) => ev (3*t) z' k = 1)).card := by
    by_cases hcmp :
        (Finset.univ.filter (fun k : Fin (3*t) => od (3*t) z k = 1)).card ≤
        (Finset.univ.filter (fun k : Fin (3*t) => ev (3*t) z k = 1)).card
    · exact ⟨z, rfl, by omega⟩
    · refine ⟨sh (2*(3*t)) hn 1 z, sh_tw0 (2*(3*t)) hn 1 z, ?_⟩
      rw [ev_sh_one_eq_od (3*t) hm z]
      omega
  set E := Finset.univ.filter (fun k : Fin (3*t) => ev (3*t) z' k = 1)
  have hE_mul : t ≤ (h + 1) * E.card := by
    have h1 : 2 * t ≤ (h + 1) * (2 * E.card) := le_trans hwt (Nat.mul_le_mul_left _ hcard_ge)
    have h2 : (h + 1) * (2 * E.card) = 2 * ((h + 1) * E.card) := by ring
    omega
  have hE_big : 18 * (h + 4) ≤ E.card := by
    have hmul : (h + 1) * (18 * (h + 4)) ≤ (h + 1) * E.card := by
      have h1 : (h + 1) * (18 * (h + 4)) ≤ 100 * (h + 4) ^ 2 := by nlinarith
      omega
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  let E0 := E.filter (fun k : Fin (3*t) => k.val % 3 = 0)
  let E1 := E.filter (fun k : Fin (3*t) => k.val % 3 = 1)
  let E2 := E.filter (fun k : Fin (3*t) => k.val % 3 = 2)
  have hE_cov : E ⊆ E0 ∪ (E1 ∪ E2) := by
    intro k hk
    simp only [Finset.mem_union, E0, E1, E2, Finset.mem_filter]
    have hmod : k.val % 3 = 0 ∨ k.val % 3 = 1 ∨ k.val % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · exact Or.inl ⟨hk, h0⟩
    · exact Or.inr (Or.inl ⟨hk, h1⟩)
    · exact Or.inr (Or.inr ⟨hk, h2⟩)
  have hE_sum : E.card ≤ E0.card + E1.card + E2.card := by
    calc E.card ≤ (E0 ∪ (E1 ∪ E2)).card := Finset.card_le_card hE_cov
      _ ≤ E0.card + (E1 ∪ E2).card := Finset.card_union_le _ _
      _ ≤ E0.card + (E1.card + E2.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = E0.card + E1.card + E2.card := by omega
  obtain ⟨c, Ec, hEc_sub, hEc_mod, hEc_card⟩ :
      ∃ (c : ℕ) (Ec : Finset (Fin (3*t))),
        Ec ⊆ E ∧ (∀ k ∈ Ec, k.val % 3 = c) ∧ 6 * (h + 4) ≤ Ec.card := by
    by_cases h0 : 6 * (h + 4) ≤ E0.card
    · exact ⟨0, E0, Finset.filter_subset _ _, fun k hk => (Finset.mem_filter.mp hk).2, h0⟩
    · by_cases h1 : 6 * (h + 4) ≤ E1.card
      · exact ⟨1, E1, Finset.filter_subset _ _, fun k hk => (Finset.mem_filter.mp hk).2, h1⟩
      · exact ⟨2, E2, Finset.filter_subset _ _, fun k hk => (Finset.mem_filter.mp hk).2, by omega⟩
  obtain ⟨P, hP_sub, hP_card⟩ := Finset.exists_subset_card_eq hEc_card
  have hP_ev : ∀ k ∈ P, ev (3*t) z' k = 1 := fun k hk =>
    (Finset.mem_filter.mp (hEc_sub (hP_sub hk))).2
  have hP_mod : ∀ k ∈ P, k.val % 3 = c := fun k hk => hEc_mod k (hP_sub hk)
  have habs : |tw0 (2*(3*t)) hn z'| ≤
      ((Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
        ind (2*(3*t)) hn x ∧ ∀ k ∈ P, covE (3*t) hm (od (3*t) x) k)).card : ℤ) :=
    tw0_abs_le_covE (3*t) hm z' P hP_ev
  have h35 := ind_covE_35_bound t ht c P hP_mod
  rw [hP_card] at h35
  have h35Z : (5 : ℤ) ^ (6 * (h + 4)) *
      ((Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
        ind (2*(3*t)) hn x ∧ ∀ k ∈ P, covE (3*t) hm (od (3*t) x) k)).card : ℤ) ≤
      (3 : ℤ) ^ (6 * (h + 4)) * ((Finset.univ.filter (ind (2*(3*t)) hn)).card : ℤ) := by
    exact_mod_cast h35
  have h5pow : (5 : ℤ) ^ (6 * (h + 4)) = (15625 : ℤ) ^ (h + 4) := by
    rw [pow_mul]
    norm_num
  have h3pow : (3 : ℤ) ^ (6 * (h + 4)) = (729 : ℤ) ^ (h + 4) := by
    rw [pow_mul]
    norm_num
  rw [h5pow, h3pow] at h35Z
  rw [← htw_eq]
  calc (15625 : ℤ) ^ (h + 4) * |tw0 (2*(3*t)) hn z'|
      ≤ (15625 : ℤ) ^ (h + 4) * ((Finset.univ.filter (fun x : Fin (2*(3*t)) → ZMod 2 =>
          ind (2*(3*t)) hn x ∧ ∀ k ∈ P, covE (3*t) hm (od (3*t) x) k)).card : ℤ) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ (729 : ℤ) ^ (h + 4) * ((Finset.univ.filter (ind (2*(3*t)) hn)).card : ℤ) := h35Z

lemma tw0_heavy_bound (t : ℕ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h)
    (ht_big : 100 * (h + 4)^2 ≤ t) (z : Fin (6*t) → ZMod 2)
    (hwt : 2 * t ≤ (h + 1) * wt (6*t) z) :
    (15625 : ℤ) ^ (h + 4) * |tw0 (6*t) (by omega) z| ≤
      (729 : ℤ) ^ (h + 4) * ((Finset.univ.filter (ind (6*t) (by omega))).card : ℤ) := by
  have haux : ∀ (n : ℕ) (hn : n = 2 * (3 * t)) (z : Fin n → ZMod 2),
      2 * t ≤ (h + 1) * wt n z →
      (15625 : ℤ) ^ (h + 4) * |tw0 n (by omega) z| ≤
        (729 : ℤ) ^ (h + 4) * ((Finset.univ.filter (ind n (by omega))).card : ℤ) := by
    rintro _ rfl z hwt'
    exact heavy_bound_aux t ht h hh ht_big z hwt'
  exact haux (6 * t) (by ring) z hwt

end Decay33638

namespace Pivot33638

def ix (n : ℕ) (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

noncomputable def even (n : ℕ) (z : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if i.val % 2 = 0 then z i else 0

def sgn (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

def dot (n : ℕ) (z x : Fin n → ZMod 2) : ZMod 2 := ∑ i, z i * x i

def ind (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) : Prop :=
  ∀ i : Fin n, x i * x (ix n hn (i.val + 1)) = 0

noncomputable def tw0 (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∑ x : Fin n → ZMod 2, if ind n hn x then sgn (dot n z x) else 0

noncomputable def S0 (n : ℕ) (hn : 0 < n) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) : ℤ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∑ z ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun z => z ∈ D), tw0 n hn z

def ev (m : ℕ) (x : Fin (2*m) → ZMod 2) (k : Fin m) : ZMod 2 := x ⟨2*k.val, by omega⟩
def od (m : ℕ) (x : Fin (2*m) → ZMod 2) (k : Fin m) : ZMod 2 := x ⟨2*k.val + 1, by omega⟩
def mergeEO (m : ℕ) (u v : Fin m → ZMod 2) (i : Fin (2*m)) : ZMod 2 :=
  if i.val % 2 = 0 then u ⟨i.val / 2, by omega⟩ else v ⟨i.val / 2, by omega⟩
def covE (m : ℕ) (hm : 0 < m) (v : Fin m → ZMod 2) (k : Fin m) : Prop :=
  v (ix m hm (k.val + m - 1)) = 1 ∨ v k = 1
def sh (n : ℕ) (hn : 0 < n) (s : ℕ) (z : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => z (ix n hn (i.val + s))

lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_ne_zero_iff (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · exact ⟨fun h => absurd rfl h, fun h => absurd h zero_ne_one⟩
  · exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩

lemma zmod2_eq_zero_iff_ne_one (a : ZMod 2) : a = 0 ↔ a ≠ 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · exact ⟨fun _ => zero_ne_one, fun _ => rfl⟩
  · exact ⟨fun h => absurd h one_ne_zero, fun h => absurd rfl h⟩

open scoped Classical

lemma tw0_eq (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) :
    tw0 n hn z = ∑ x : Fin n → ZMod 2, if ind n hn x then sgn (dot n z x) else 0 := by
  unfold tw0
  convert rfl

lemma S0_eq (n : ℕ) (hn : 0 < n) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    S0 n hn D = ∑ z ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun z => z ∈ D), tw0 n hn z := by
  unfold S0
  convert rfl

-- Section 1: Coordinate subspaces and pivot selection

def eVec (n : ℕ) (i : Fin n) : Fin n → ZMod 2 := fun j => if j = i then 1 else 0

def coordSub (m : ℕ) (P : Finset (Fin m)) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) (eVec m '' (P : Set (Fin m)))

lemma eVec_mem_coordSub (m : ℕ) (P : Finset (Fin m)) {i : Fin m} (hi : i ∈ P) :
    eVec m i ∈ coordSub m P :=
  Submodule.subset_span ⟨i, hi, rfl⟩

lemma mem_coordSub_iff (m : ℕ) (P : Finset (Fin m)) (u : Fin m → ZMod 2) :
    u ∈ coordSub m P ↔ ∀ i : Fin m, i ∉ P → u i = 0 := by
  constructor
  · intro hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨p, hp, rfl⟩ i hi
      simp [eVec, show i ≠ p from fun h => hi (h ▸ hp)]
    · intro i _; rfl
    · intro x y _ _ hx hy i hi
      simp [hx i hi, hy i hi]
    · intro a x _ hx i hi
      simp [hx i hi]
  · intro hu
    have hsum : u = ∑ p ∈ P, u p • eVec m p := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eVec]
      by_cases hj : j ∈ P
      · rw [Finset.sum_eq_single j]
        · simp
        · intro p _ hne
          simp [hne.symm]
        · intro h; exact absurd hj h
      · rw [hu j hj, Finset.sum_eq_zero]
        intro p hp
        have hne : j ≠ p := fun h => hj (h ▸ hp)
        simp [hne]
    rw [hsum]
    exact Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _ (eVec_mem_coordSub m P hp)

noncomputable def coordSubEquiv (m : ℕ) (P : Finset (Fin m)) :
    coordSub m P ≃ₗ[ZMod 2] (P → ZMod 2) where
  toFun x i := x.1 i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f :=
    ⟨fun j => if h : j ∈ P then f ⟨j, h⟩ else 0, by
      rw [mem_coordSub_iff]
      intro i hi
      simp [hi]⟩
  left_inv x := by
    ext j
    by_cases hj : j ∈ P
    · simp [hj]
    · simp [hj, (mem_coordSub_iff m P x.1).mp x.2 j hj]
  right_inv f := by
    ext ⟨j, hj⟩
    simp [hj]

lemma finrank_coordSub (m : ℕ) (P : Finset (Fin m)) :
    Module.finrank (ZMod 2) (coordSub m P) = P.card := by
  rw [(coordSubEquiv m P).finrank_eq, Module.finrank_pi, Fintype.card_coe]

lemma card_filter_mem_submodule (n : ℕ) (M : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (Finset.univ.filter (fun u => u ∈ M)).card = Fintype.card M := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun ⟨u, hu⟩ => ⟨u, (Finset.mem_filter.mp hu).2⟩
      invFun := fun ⟨u, hu⟩ => ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }

lemma card_submodule (n : ℕ) (M : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (Finset.univ.filter (fun u => u ∈ M)).card = 2 ^ Module.finrank (ZMod 2) M := by
  rw [card_filter_mem_submodule, Module.card_eq_pow_finrank (K := ZMod 2) (V := M), ZMod.card]

lemma card_coordSub (m : ℕ) (P : Finset (Fin m)) :
    (Finset.univ.filter (fun u => u ∈ coordSub m P)).card = 2 ^ P.card := by
  rw [card_submodule, finrank_coordSub]

lemma exists_pivot (m : ℕ) (M : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    ∃ P : Finset (Fin m),
      P.card = Module.finrank (ZMod 2) M ∧
      Function.Bijective (fun x : M => fun i : P => x.1 i.1) := by
  suffices h : ∀ k : ℕ, ∀ M : Submodule (ZMod 2) (Fin m → ZMod 2),
      Module.finrank (ZMod 2) M = k →
      ∃ P : Finset (Fin m), P.card = k ∧ Function.Bijective (fun x : M => fun i : P => x.1 i.1) from
    h (Module.finrank (ZMod 2) M) M rfl
  intro k
  induction k with
  | zero =>
    intro M hM
    refine ⟨∅, rfl, ?_⟩
    have hcardM : Fintype.card M = 1 := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := M), ZMod.card, hM, pow_zero]
    have hsubM : Subsingleton M := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    constructor
    · intro x y _; exact Subsingleton.elim x y
    · intro f; exact ⟨0, funext fun i => absurd i.2 (Finset.notMem_empty _)⟩
  | succ k' ih =>
    intro M hM
    have hne : M ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hM
      omega
    have hv_ex : ∃ v ∈ M, v ≠ 0 := by
      by_contra h
      push Not at h
      apply hne
      ext x
      simp only [Submodule.mem_bot]
      exact ⟨fun hx => h x hx, fun hx => hx ▸ M.zero_mem⟩
    rcases hv_ex with ⟨v, hvM, hv0⟩
    have hi0_ex : ∃ i0 : Fin m, v i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    rcases hi0_ex with ⟨i0, hvi0⟩
    have hvi0_one : v i0 = 1 := (zmod2_ne_zero_iff _).mp hvi0
    let ev0 : M →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => x.1 i0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hev0_surj : Function.Surjective ev0 := by
      intro c
      refine ⟨c • ⟨v, hvM⟩, ?_⟩
      change (c • v) i0 = c
      simp [hvi0_one]
    let K : Submodule (ZMod 2) M := LinearMap.ker ev0
    let M' : Submodule (ZMod 2) (Fin m → ZMod 2) := K.map M.subtype
    have hrank_K : Module.finrank (ZMod 2) K = k' := by
      have hrn : Module.finrank (ZMod 2) (LinearMap.range ev0) + Module.finrank (ZMod 2) K =
          Module.finrank (ZMod 2) M := LinearMap.finrank_range_add_finrank_ker ev0
      have hrange : LinearMap.range ev0 = ⊤ := LinearMap.range_eq_top.mpr hev0_surj
      rw [hrange, finrank_top, Module.finrank_self, hM] at hrn
      omega
    have hrank_M' : Module.finrank (ZMod 2) M' = k' := by
      have heq : LinearMap.range (M.subtype.comp K.subtype) = M' := by
        ext x
        simp [M', LinearMap.mem_range, Submodule.mem_map]
      rw [← heq, ← hrank_K]
      exact (LinearEquiv.ofInjective (M.subtype.comp K.subtype)
        (Subtype.val_injective.comp Subtype.val_injective)).finrank_eq.symm
    rcases ih M' hrank_M' with ⟨P', hP'card, hP'bij⟩
    have hi0_not : i0 ∉ P' := by
      intro hi0
      rcases hP'bij.2 (fun _ => 1) with ⟨⟨x, hxM'⟩, hx1⟩
      have hx_at : x i0 = 1 := congrFun hx1 ⟨i0, hi0⟩
      rcases Submodule.mem_map.mp hxM' with ⟨⟨y, hyM⟩, hyK, hyx⟩
      have hy0 : y i0 = 0 := hyK
      have hxy : y = x := hyx
      rw [hxy, hx_at] at hy0
      exact one_ne_zero hy0
    let P : Finset (Fin m) := insert i0 P'
    have hPcard : P.card = k' + 1 := by
      rw [Finset.card_insert_of_notMem hi0_not, hP'card]
    refine ⟨P, hPcard, ?_⟩
    have hinj : Function.Injective (fun x : M => fun i : P => x.1 i.1) := by
      intro x y hxy
      let d : M := x - y
      have hdP : ∀ i ∈ P, d.1 i = 0 := by
        intro i hi
        have h1 : x.1 i = y.1 i := congrFun hxy ⟨i, hi⟩
        change x.1 i - y.1 i = 0
        rw [h1, sub_self]
      have hd_i0 : d.1 i0 = 0 := hdP i0 (Finset.mem_insert_self i0 P')
      have hdM' : d.1 ∈ M' := Submodule.mem_map.mpr ⟨d, hd_i0, rfl⟩
      have hd0 : (⟨d.1, hdM'⟩ : M') = 0 := by
        apply hP'bij.1
        ext ⟨i, hi⟩
        exact hdP i (Finset.mem_insert_of_mem hi)
      have hdval : d.1 = 0 := congrArg Subtype.val hd0
      have hsub : x - y = 0 := Subtype.ext hdval
      exact sub_eq_zero.mp hsub
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := M), ZMod.card, hM,
      Fintype.card_fun, ZMod.card, Fintype.card_coe, hPcard]

-- Section 2: Orthogonality formula for S0 and lane formula

lemma dot_comm (n : ℕ) (z x : Fin n → ZMod 2) : dot n z x = dot n x z := by
  simp only [dot, mul_comm]

lemma dot_add_left (n : ℕ) (z1 z2 x : Fin n → ZMod 2) :
    dot n (z1 + z2) x = dot n z1 x + dot n z2 x := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma sgn_add_one (a : ZMod 2) : sgn (a + 1) = -sgn a := by
  fin_cases a <;> decide

lemma sum_sgn_dot_submodule (n : ℕ) (M : Submodule (ZMod 2) (Fin n → ZMod 2))
    (x : Fin n → ZMod 2) :
    ∑ z ∈ Finset.univ.filter (fun z => z ∈ M), sgn (dot n z x) =
      if ∀ z ∈ M, dot n z x = 0 then ((Finset.univ.filter (fun z => z ∈ M)).card : ℤ) else 0 := by
  split_ifs with h
  · have h1 : ∀ z ∈ Finset.univ.filter (fun z => z ∈ M), sgn (dot n z x) = 1 := by
      intro z hz
      rw [h z (Finset.mem_filter.mp hz).2]
      rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  · push Not at h
    rcases h with ⟨z0, hz0M, hz0ne⟩
    have hz0one : dot n z0 x = 1 := (zmod2_ne_zero_iff _).mp hz0ne
    set S : ℤ := ∑ z ∈ Finset.univ.filter (fun z => z ∈ M), sgn (dot n z x)
    have hneg : S = -S := by
      have hbij :
          ∑ z ∈ Finset.univ.filter (fun z => z ∈ M), sgn (dot n (z + z0) x) =
          ∑ z ∈ Finset.univ.filter (fun z => z ∈ M), sgn (dot n z x) := by
        refine Finset.sum_bij (fun z _ => z + z0) ?_ ?_ ?_ ?_
        · intro z hz
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, M.add_mem (Finset.mem_filter.mp hz).2 hz0M⟩
        · intro z1 _ z2 _ heq
          exact add_right_cancel heq
        · intro z hz
          refine ⟨z - z0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, M.sub_mem (Finset.mem_filter.mp hz).2 hz0M⟩, ?_⟩
          simp
        · intro _ _; rfl
      calc
        S = ∑ z ∈ Finset.univ.filter (fun z => z ∈ M), sgn (dot n (z + z0) x) := hbij.symm
        _ = ∑ z ∈ Finset.univ.filter (fun z => z ∈ M), -sgn (dot n z x) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [dot_add_left, hz0one, sgn_add_one]
        _ = -S := Finset.sum_neg_distrib (f := fun z => sgn (dot n z x))
    omega

lemma S0_eq_card_orth (n : ℕ) (hn : 0 < n) (L : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    S0 n hn L =
      ((Finset.univ.filter (fun z => z ∈ L)).card : ℤ) *
        ((Finset.univ.filter (fun x : Fin n → ZMod 2 => ind n hn x ∧ ∀ z ∈ L, dot n z x = 0)).card : ℤ) := by
  rw [S0_eq]
  simp_rw [tw0_eq]
  rw [Finset.sum_comm]
  have hterm : ∀ x : Fin n → ZMod 2,
      ∑ z ∈ Finset.univ.filter (fun z => z ∈ L), (if ind n hn x then sgn (dot n z x) else 0) =
        if ind n hn x ∧ ∀ z ∈ L, dot n z x = 0 then
          ((Finset.univ.filter (fun z => z ∈ L)).card : ℤ)
        else 0 := by
    intro x
    by_cases hind : ind n hn x
    · simp only [hind, ite_true, true_and]
      exact sum_sgn_dot_submodule n L x
    · simp [hind]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma dot_eVec (n : ℕ) (i : Fin n) (x : Fin n → ZMod 2) : dot n (eVec n i) x = x i := by
  unfold dot eVec
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma orth_coordSub_iff (n : ℕ) (R : Finset (Fin n)) (x : Fin n → ZMod 2) :
    (∀ z ∈ coordSub n R, dot n z x = 0) ↔ ∀ i ∈ R, x i = 0 := by
  constructor
  · intro h i hi
    have h1 := h (eVec n i) (eVec_mem_coordSub n R hi)
    rwa [dot_eVec] at h1
  · intro h z hz
    have hz0 := (mem_coordSub_iff n R z).mp hz
    unfold dot
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ R
    · simp [h i hi]
    · simp [hz0 i hi]

lemma S0_coord_eq (n : ℕ) (hn : 0 < n) (R : Finset (Fin n)) :
    S0 n hn (coordSub n R) =
      (2 : ℤ) ^ R.card *
        ((Finset.univ.filter (fun x : Fin n → ZMod 2 => ind n hn x ∧ ∀ i ∈ R, x i = 0)).card : ℤ) := by
  rw [S0_eq_card_orth, card_coordSub]
  push_cast
  congr 1
  congr 1
  congr 1
  ext x
  simp [orth_coordSub_iff]

-- Split submodules and even/odd lane decomposition

lemma ev_mergeEO (m : ℕ) (u v : Fin m → ZMod 2) : ev m (mergeEO m u v) = u := by
  ext k
  simp only [ev, mergeEO]
  have hmod : (2 * k.val) % 2 = 0 := by omega
  have hdiv : (2 * k.val) / 2 = k.val := by omega
  simp [hmod, hdiv]

lemma od_mergeEO (m : ℕ) (u v : Fin m → ZMod 2) : od m (mergeEO m u v) = v := by
  ext k
  simp only [od, mergeEO]
  have hdiv : (2 * k.val + 1) / 2 = k.val := by omega
  simp [hdiv]

lemma mergeEO_ev_od (m : ℕ) (z : Fin (2*m) → ZMod 2) : mergeEO m (ev m z) (od m z) = z := by
  ext i
  simp only [mergeEO, ev, od]
  by_cases h : i.val % 2 = 0
  · simp only [h, ite_true]
    congr 1
    ext
    dsimp
    omega
  · simp only [h, ite_false]
    congr 1
    ext
    dsimp
    omega

lemma ev_add (m : ℕ) (x y : Fin (2*m) → ZMod 2) : ev m (x + y) = ev m x + ev m y := rfl
lemma od_add (m : ℕ) (x y : Fin (2*m) → ZMod 2) : od m (x + y) = od m x + od m y := rfl
lemma ev_zero (m : ℕ) : ev m 0 = 0 := rfl
lemma od_zero (m : ℕ) : od m 0 = 0 := rfl
lemma ev_smul (m : ℕ) (c : ZMod 2) (x : Fin (2*m) → ZMod 2) : ev m (c • x) = c • ev m x := rfl
lemma od_smul (m : ℕ) (c : ZMod 2) (x : Fin (2*m) → ZMod 2) : od m (c • x) = c • od m x := rfl

lemma mergeEO_add (m : ℕ) (u1 v1 u2 v2 : Fin m → ZMod 2) :
    mergeEO m (u1 + u2) (v1 + v2) = mergeEO m u1 v1 + mergeEO m u2 v2 := by
  ext i
  simp only [mergeEO, Pi.add_apply]
  split_ifs <;> rfl

lemma mergeEO_smul (m : ℕ) (c : ZMod 2) (u v : Fin m → ZMod 2) :
    mergeEO m (c • u) (c • v) = c • mergeEO m u v := by
  ext i
  simp only [mergeEO, Pi.smul_apply]
  split_ifs <;> rfl

lemma mergeEO_zero (m : ℕ) : mergeEO m 0 0 = 0 := by
  ext i
  simp [mergeEO]

lemma even_eq_mergeEO (m : ℕ) (z : Fin (2*m) → ZMod 2) :
    even (2*m) z = mergeEO m (ev m z) 0 := by
  ext i
  simp only [even, mergeEO, ev, Pi.zero_apply]
  by_cases h : i.val % 2 = 0
  · simp only [h, ite_true]
    congr 1
    ext
    dsimp
    omega
  · simp [h]

lemma sub_even_eq_mergeEO (m : ℕ) (z : Fin (2*m) → ZMod 2) :
    z - even (2*m) z = mergeEO m 0 (od m z) := by
  ext i
  simp only [Pi.sub_apply, even, mergeEO, od, Pi.zero_apply]
  by_cases h : i.val % 2 = 0
  · simp [h]
  · simp only [h, ite_false, sub_zero]
    congr 1
    ext
    dsimp
    omega

def splitSub (m : ℕ) (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    Submodule (ZMod 2) (Fin (2*m) → ZMod 2) :=
  { carrier := {z | ev m z ∈ Le ∧ od m z ∈ Lo}, add_mem' := fun ha hb => ⟨Le.add_mem ha.1 hb.1, Lo.add_mem ha.2 hb.2⟩,
    zero_mem' := ⟨Le.zero_mem, Lo.zero_mem⟩,
    smul_mem' := fun c _ hx => ⟨Le.smul_mem c hx.1, Lo.smul_mem c hx.2⟩ }

lemma mem_splitSub_iff (m : ℕ) (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2))
    (z : Fin (2*m) → ZMod 2) :
    z ∈ splitSub m Le Lo ↔ ev m z ∈ Le ∧ od m z ∈ Lo := Iff.rfl

def splitSubEquiv (m : ℕ) (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    splitSub m Le Lo ≃ₗ[ZMod 2] Le × Lo where
  toFun z := (⟨ev m z.1, z.2.1⟩, ⟨od m z.1, z.2.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ⟨mergeEO m p.1.1 p.2.1, by
    rw [mem_splitSub_iff, ev_mergeEO, od_mergeEO]
    exact ⟨p.1.2, p.2.2⟩⟩
  left_inv z := Subtype.ext (mergeEO_ev_od m z.1)
  right_inv p := Prod.ext (Subtype.ext (ev_mergeEO m p.1.1 p.2.1))
    (Subtype.ext (od_mergeEO m p.1.1 p.2.1))

lemma finrank_splitSub (m : ℕ) (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    Module.finrank (ZMod 2) (splitSub m Le Lo) =
      Module.finrank (ZMod 2) Le + Module.finrank (ZMod 2) Lo := by
  rw [(splitSubEquiv m Le Lo).finrank_eq, Module.finrank_prod]

lemma card_splitSub (m : ℕ) (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    (Finset.univ.filter (fun z => z ∈ splitSub m Le Lo)).card =
      (Finset.univ.filter (fun u => u ∈ Le)).card *
        (Finset.univ.filter (fun v => v ∈ Lo)).card := by
  rw [card_submodule, card_submodule, card_submodule, finrank_splitSub, pow_add]

def evenLane (m : ℕ) (L : Submodule (ZMod 2) (Fin (2*m) → ZMod 2)) :
    Submodule (ZMod 2) (Fin m → ZMod 2) :=
  { carrier := {u | mergeEO m u 0 ∈ L}, add_mem' := fun ha hb => (by
      change mergeEO m (_ + _) 0 ∈ L
      have h0 : (0 : Fin m → ZMod 2) = 0 + 0 := (add_zero 0).symm
      rw [h0, mergeEO_add]
      exact L.add_mem ha hb),
    zero_mem' := (by
      change mergeEO m 0 0 ∈ L
      rw [mergeEO_zero]
      exact L.zero_mem),
    smul_mem' := fun c u hu => (by
      change mergeEO m (c • u) 0 ∈ L
      have h0 : (0 : Fin m → ZMod 2) = c • 0 := (smul_zero c).symm
      rw [h0, mergeEO_smul]
      exact L.smul_mem c hu) }

def oddLane (m : ℕ) (L : Submodule (ZMod 2) (Fin (2*m) → ZMod 2)) :
    Submodule (ZMod 2) (Fin m → ZMod 2) :=
  { carrier := {v | mergeEO m 0 v ∈ L}, add_mem' := fun ha hb => (by
      change mergeEO m 0 (_ + _) ∈ L
      have h0 : (0 : Fin m → ZMod 2) = 0 + 0 := (add_zero 0).symm
      rw [h0, mergeEO_add]
      exact L.add_mem ha hb),
    zero_mem' := (by
      change mergeEO m 0 0 ∈ L
      rw [mergeEO_zero]
      exact L.zero_mem),
    smul_mem' := fun c v hv => (by
      change mergeEO m 0 (c • v) ∈ L
      have h0 : (0 : Fin m → ZMod 2) = c • 0 := (smul_zero c).symm
      rw [h0, mergeEO_smul]
      exact L.smul_mem c hv) }

lemma eq_splitSub_of_split (m : ℕ) (L : Submodule (ZMod 2) (Fin (2*m) → ZMod 2))
    (hsplit : ∀ z ∈ L, even (2*m) z ∈ L) :
    L = splitSub m (evenLane m L) (oddLane m L) := by
  ext z
  rw [mem_splitSub_iff]
  constructor
  · intro hz
    have hev : even (2*m) z ∈ L := hsplit z hz
    have hod : z - even (2*m) z ∈ L := L.sub_mem hz hev
    rw [even_eq_mergeEO] at hev
    rw [sub_even_eq_mergeEO] at hod
    exact ⟨hev, hod⟩
  · rintro ⟨hev, hod⟩
    have hsum : mergeEO m (ev m z) 0 + mergeEO m 0 (od m z) = z := by
      rw [← mergeEO_add, add_zero, zero_add, mergeEO_ev_od]
    rw [← hsum]
    exact L.add_mem hev hod

lemma finrank_eq_evenLane_add_oddLane (m : ℕ) (L : Submodule (ZMod 2) (Fin (2*m) → ZMod 2))
    (hsplit : ∀ z ∈ L, even (2*m) z ∈ L) :
    Module.finrank (ZMod 2) L =
      Module.finrank (ZMod 2) (evenLane m L) + Module.finrank (ZMod 2) (oddLane m L) := by
  conv_lhs => rw [eq_splitSub_of_split m L hsplit]
  exact finrank_splitSub m (evenLane m L) (oddLane m L)

lemma dot_mergeEO (m : ℕ) (u v a b : Fin m → ZMod 2) :
    dot (2*m) (mergeEO m u v) (mergeEO m a b) = dot m u a + dot m v b := by
  unfold dot
  have hpart :
      ∑ i : Fin (2*m), mergeEO m u v i * mergeEO m a b i =
        (∑ i ∈ Finset.univ.filter (fun i : Fin (2*m) => i.val % 2 = 0),
            mergeEO m u v i * mergeEO m a b i) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin (2*m) => ¬ i.val % 2 = 0),
            mergeEO m u v i * mergeEO m a b i) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin (2*m) => i.val % 2 = 0) _).symm
  rw [hpart]
  congr 1
  · refine Finset.sum_bij (fun i _ => (⟨i.val / 2, by omega⟩ : Fin m)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro i1 hi1 i2 hi2 heq
      have h1 := (Finset.mem_filter.mp hi1).2
      have h2 := (Finset.mem_filter.mp hi2).2
      have hval : i1.val / 2 = i2.val / 2 := congrArg Fin.val heq
      ext; omega
    · intro k _
      refine ⟨⟨2*k.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, ?_⟩
      ext; change (2 * k.val) / 2 = k.val; omega
    · intro i hi
      have h1 := (Finset.mem_filter.mp hi).2
      simp [mergeEO, h1]
  · refine Finset.sum_bij (fun i _ => (⟨i.val / 2, by omega⟩ : Fin m)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro i1 hi1 i2 hi2 heq
      have h1 := (Finset.mem_filter.mp hi1).2
      have h2 := (Finset.mem_filter.mp hi2).2
      have hval : i1.val / 2 = i2.val / 2 := congrArg Fin.val heq
      ext; omega
    · intro k _
      refine ⟨⟨2*k.val + 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, ?_⟩
      ext; change (2 * k.val + 1) / 2 = k.val; omega
    · intro i hi
      have h1 := (Finset.mem_filter.mp hi).2
      simp [mergeEO, h1]

lemma orth_splitSub_iff (m : ℕ) (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2))
    (x : Fin (2*m) → ZMod 2) :
    (∀ z ∈ splitSub m Le Lo, dot (2*m) z x = 0) ↔
      (∀ u ∈ Le, dot m u (ev m x) = 0) ∧ (∀ w ∈ Lo, dot m w (od m x) = 0) := by
  constructor
  · intro h
    constructor
    · intro u hu
      have hz : mergeEO m u 0 ∈ splitSub m Le Lo := by
        rw [mem_splitSub_iff, ev_mergeEO, od_mergeEO]
        exact ⟨hu, Lo.zero_mem⟩
      have hdot := h (mergeEO m u 0) hz
      rw [← mergeEO_ev_od m x, dot_mergeEO] at hdot
      simpa [dot] using hdot
    · intro w hw
      have hz : mergeEO m 0 w ∈ splitSub m Le Lo := by
        rw [mem_splitSub_iff, ev_mergeEO, od_mergeEO]
        exact ⟨Le.zero_mem, hw⟩
      have hdot := h (mergeEO m 0 w) hz
      rw [← mergeEO_ev_od m x, dot_mergeEO] at hdot
      simpa [dot] using hdot
  · rintro ⟨he, ho⟩ z hz
    rw [← mergeEO_ev_od m z, ← mergeEO_ev_od m x, dot_mergeEO, he _ hz.1, ho _ hz.2, add_zero]

lemma ix_pred_succ (m : ℕ) (hm : 0 < m) (k : Fin m) :
    ix m hm ((ix m hm (k.val + m - 1)).val + 1) = k := by
  ext
  simp only [ix]
  have hk := k.isLt
  by_cases h0 : k.val = 0
  · rw [h0, zero_add]
    have h1 : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1, show m - 1 + 1 = m by omega, Nat.mod_self]
  · have h1 : (k.val + m - 1) % m = k.val - 1 := by
      have : k.val + m - 1 = (k.val - 1) + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, show k.val - 1 + 1 = k.val by omega, Nat.mod_eq_of_lt hk]

lemma ix_succ_pred (m : ℕ) (hm : 0 < m) (k : Fin m) :
    ix m hm ((ix m hm (k.val + 1)).val + m - 1) = k := by
  ext
  simp only [ix]
  have hk := k.isLt
  by_cases hlast : k.val + 1 = m
  · rw [hlast, Nat.mod_self, zero_add]
    have h1 : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]; omega
  · have h1 : (k.val + 1) % m = k.val + 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1, show k.val + 1 + m - 1 = k.val + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hk]

lemma ind_two_mul_iff (m : ℕ) (hm : 0 < m) (x : Fin (2*m) → ZMod 2) :
    ind (2*m) (by omega) x ↔ ∀ k : Fin m, covE m hm (od m x) k → ev m x k = 0 := by
  constructor
  · intro hind k hcov
    rcases hcov with h1 | h2
    · let j : Fin m := ix m hm (k.val + m - 1)
      have hj := hind ⟨2 * j.val + 1, by omega⟩
      have hnext : ix (2*m) (by omega) (2 * j.val + 1 + 1) = ⟨2 * k.val, by omega⟩ := by
        ext
        have hjk : (j.val + 1) % m = k.val := congrArg Fin.val (ix_pred_succ m hm k)
        dsimp [ix]
        have hmod : (2 * j.val + 1 + 1) % (2 * m) = 2 * ((j.val + 1) % m) := by
          have : 2 * j.val + 1 + 1 = 2 * (j.val + 1) := by omega
          rw [this, Nat.mul_mod_mul_left]
        rw [hmod, hjk]
      rw [hnext] at hj
      have hxj : x ⟨2 * j.val + 1, by omega⟩ = 1 := h1
      rw [hxj, one_mul] at hj
      exact hj
    · have hk := hind ⟨2 * k.val, by omega⟩
      have hnext : ix (2*m) (by omega) (2 * k.val + 1) = ⟨2 * k.val + 1, by omega⟩ := by
        ext; dsimp [ix]; exact Nat.mod_eq_of_lt (by omega)
      rw [hnext] at hk
      have hxk : x ⟨2 * k.val + 1, by omega⟩ = 1 := h2
      rw [hxk, mul_one] at hk
      exact hk
  · intro h i
    by_cases heven : i.val % 2 = 0
    · let k : Fin m := ⟨i.val / 2, by omega⟩
      have hi : i = ⟨2 * k.val, by omega⟩ := by ext; dsimp [k]; omega
      have hxi : x i = ev m x k := by rw [hi]; rfl
      have hnext : ix (2*m) (by omega) (i.val + 1) = ⟨2 * k.val + 1, by omega⟩ := by
        ext; dsimp [ix, k]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [hnext, hxi]
      rcases zmod2_eq_zero_or_one (od m x k) with hv0 | hv1
      · change ev m x k * od m x k = 0; rw [hv0, mul_zero]
      · change ev m x k * od m x k = 0; rw [h k (Or.inr hv1), zero_mul]
    · let j : Fin m := ⟨i.val / 2, by omega⟩
      let k : Fin m := ix m hm (j.val + 1)
      have hi : i = ⟨2 * j.val + 1, by omega⟩ := by ext; dsimp [j]; omega
      have hxi : x i = od m x j := by rw [hi]; rfl
      have hnext : ix (2*m) (by omega) (i.val + 1) = ⟨2 * k.val, by omega⟩ := by
        ext; dsimp [ix, k, j]
        have h1 : i.val + 1 = 2 * (i.val / 2 + 1) := by omega
        rw [h1, Nat.mul_mod_mul_left]
      rw [hnext, hxi]
      rcases zmod2_eq_zero_or_one (od m x j) with hv0 | hv1
      · change od m x j * ev m x k = 0; rw [hv0, zero_mul]
      · have hj : ix m hm (k.val + m - 1) = j := ix_succ_pred m hm j
        have hcov : covE m hm (od m x) k := Or.inl (by rw [hj]; exact hv1)
        change od m x j * ev m x k = 0
        rw [h k hcov, mul_zero]

lemma inner_lane_duality (m : ℕ) (hm : 0 < m) (Le : Submodule (ZMod 2) (Fin m → ZMod 2))
    (v : Fin m → ZMod 2) :
    ((Finset.univ.filter (fun u => u ∈ Le)).card : ℤ) *
      ((Finset.univ.filter (fun a : Fin m → ZMod 2 =>
          (∀ k : Fin m, covE m hm v k → a k = 0) ∧ ∀ u ∈ Le, dot m u a = 0)).card : ℤ) =
    ((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
        u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) *
      (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card := by
  let U : Finset (Fin m) := Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)
  have hmemU : ∀ a : Fin m → ZMod 2,
      a ∈ coordSub m U ↔ ∀ k : Fin m, covE m hm v k → a k = 0 := by
    intro a
    rw [mem_coordSub_iff]
    simp [U]
  have h1 :
      ∑ a ∈ Finset.univ.filter (fun a => a ∈ coordSub m U),
        ∑ u ∈ Finset.univ.filter (fun u => u ∈ Le), sgn (dot m u a) =
      ((Finset.univ.filter (fun u => u ∈ Le)).card : ℤ) *
        ((Finset.univ.filter (fun a : Fin m → ZMod 2 =>
            (∀ k : Fin m, covE m hm v k → a k = 0) ∧ ∀ u ∈ Le, dot m u a = 0)).card : ℤ) := by
    have hinner : ∀ a : Fin m → ZMod 2,
        ∑ u ∈ Finset.univ.filter (fun u => u ∈ Le), sgn (dot m u a) =
          if ∀ u ∈ Le, dot m u a = 0 then ((Finset.univ.filter (fun u => u ∈ Le)).card : ℤ) else 0 :=
      fun a => sum_sgn_dot_submodule m Le a
    rw [Finset.sum_congr rfl fun a _ => hinner a, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_comm]
    congr 1
    congr 1
    congr 1
    ext a
    simp [hmemU]
  have h2 :
      ∑ u ∈ Finset.univ.filter (fun u => u ∈ Le),
        ∑ a ∈ Finset.univ.filter (fun a => a ∈ coordSub m U), sgn (dot m u a) =
      ((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
          u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) *
        (2 : ℤ) ^ U.card := by
    have hinner : ∀ u : Fin m → ZMod 2,
        ∑ a ∈ Finset.univ.filter (fun a => a ∈ coordSub m U), sgn (dot m u a) =
          if ∀ k : Fin m, u k = 1 → covE m hm v k then (2 : ℤ) ^ U.card else 0 := by
      intro u
      have hcomm :
          ∑ a ∈ Finset.univ.filter (fun a => a ∈ coordSub m U), sgn (dot m u a) =
          ∑ a ∈ Finset.univ.filter (fun a => a ∈ coordSub m U), sgn (dot m a u) :=
        Finset.sum_congr rfl fun a _ => by rw [dot_comm]
      rw [hcomm, sum_sgn_dot_submodule, card_coordSub]
      push_cast
      refine if_congr ?_ rfl rfl
      rw [orth_coordSub_iff]
      constructor
      · intro hu k huk
        by_contra hnc
        have h0 := hu k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hnc⟩)
        rw [huk] at h0
        exact one_ne_zero h0
      · intro hu k hk
        have hnc := (Finset.mem_filter.mp hk).2
        rcases zmod2_eq_zero_or_one (u k) with h0 | h1
        · exact h0
        · exact absurd (hu k h1) hnc
    rw [Finset.sum_congr rfl fun u _ => hinner u, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    congr 1
    congr 1
    congr 1
    ext u
    simp
  rw [← h1, Finset.sum_comm, h2]

lemma S0_split_formula (m : ℕ) (hm : 0 < m) (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    S0 (2*m) (by omega) (splitSub m Le Lo) =
      ((Finset.univ.filter (fun w => w ∈ Lo)).card : ℤ) *
        ∑ v ∈ Finset.univ.filter (fun v : Fin m → ZMod 2 => ∀ w ∈ Lo, dot m w v = 0),
          ((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
              u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) *
            (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card := by
  rw [S0_eq_card_orth, card_splitSub]
  push_cast
  have hcount :
      ((Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
          ind (2*m) (by omega) x ∧ ∀ z ∈ splitSub m Le Lo, dot (2*m) z x = 0)).card : ℤ) =
        ∑ v ∈ Finset.univ.filter (fun v : Fin m → ZMod 2 => ∀ w ∈ Lo, dot m w v = 0),
          ((Finset.univ.filter (fun a : Fin m → ZMod 2 =>
              (∀ k : Fin m, covE m hm v k → a k = 0) ∧ ∀ u ∈ Le, dot m u a = 0)).card : ℤ) := by
    norm_cast
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun x _ => ⟨od m x, ev m x⟩) ?_ ?_ ?_
    · intro x hx
      rcases (Finset.mem_filter.mp hx).2 with ⟨hind, horth⟩
      rw [ind_two_mul_iff m hm] at hind
      rw [orth_splitSub_iff] at horth
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, horth.2⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hind, horth.1⟩⟩⟩
    · intro x1 _ x2 _ heq
      have hod : od m x1 = od m x2 := congrArg Sigma.fst heq
      have hev : ev m x1 = ev m x2 := by
        have h := congrArg Sigma.snd heq
        simpa using h
      rw [← mergeEO_ev_od m x1, ← mergeEO_ev_od m x2, hev, hod]
    · intro ⟨v, a⟩ hp
      rcases Finset.mem_sigma.mp hp with ⟨hv, ha⟩
      refine ⟨mergeEO m a v, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · rw [ind_two_mul_iff m hm, ev_mergeEO, od_mergeEO]
          exact (Finset.mem_filter.mp ha).2.1
        · rw [orth_splitSub_iff, ev_mergeEO, od_mergeEO]
          exact ⟨(Finset.mem_filter.mp ha).2.2, (Finset.mem_filter.mp hv).2⟩
      · simp [ev_mergeEO, od_mergeEO]
  rw [hcount]
  have hrearr : ∀ a b c : ℤ, a * b * c = b * (a * c) := fun a b c => by ring
  rw [hrearr, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  exact inner_lane_duality m hm Le v

-- Section 3: Pivot projection monotonicity, lane swap, and strict gap

lemma card_le_coordSub_proj (m : ℕ) (hm : 0 < m)
    (Le : Submodule (ZMod 2) (Fin m → ZMod 2))
    (P : Finset (Fin m))
    (hP : Function.Bijective (fun x : Le => fun i : P => x.1 i.1))
    (v : Fin m → ZMod 2) :
    (Finset.univ.filter (fun u : Fin m → ZMod 2 =>
        u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card ≤
    (Finset.univ.filter (fun u : Fin m → ZMod 2 =>
        u ∈ coordSub m P ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card := by
  let proj : (Fin m → ZMod 2) → (Fin m → ZMod 2) := fun u k => if k ∈ P then u k else 0
  refine Finset.card_le_card_of_injOn proj ?_ ?_
  · intro u hu
    rcases (Finset.mem_filter.mp hu).2 with ⟨huLe, hcov⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [mem_coordSub_iff]
      intro i hi
      simp [proj, hi]
    · intro k hk
      by_cases hkP : k ∈ P
      · simp only [proj, hkP, ite_true] at hk
        exact hcov k hk
      · simp only [proj, hkP, ite_false] at hk
        exact absurd hk zero_ne_one
  · intro u1 hu1 u2 hu2 heq
    have h1 := (Finset.mem_filter.mp hu1).2.1
    have h2 := (Finset.mem_filter.mp hu2).2.1
    have hsub : (⟨u1, h1⟩ : Le) = ⟨u2, h2⟩ := by
      apply hP.1
      ext ⟨i, hi⟩
      have hi_eq := congrFun heq i
      simpa [proj, hi] using hi_eq
    exact congrArg Subtype.val hsub

lemma S0_proj_left_le (m : ℕ) (hm : 0 < m)
    (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2))
    (P : Finset (Fin m))
    (hP : Function.Bijective (fun x : Le => fun i : P => x.1 i.1)) :
    S0 (2*m) (by omega) (splitSub m Le Lo) ≤
      S0 (2*m) (by omega) (splitSub m (coordSub m P) Lo) := by
  rw [S0_split_formula m hm Le Lo, S0_split_formula m hm (coordSub m P) Lo]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine Finset.sum_le_sum fun v _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact_mod_cast card_le_coordSub_proj m hm Le P hP v

-- Shift invariance and swapping lanes

lemma ix_add_assoc (n : ℕ) (hn : 0 < n) (a b : ℕ) :
    ix n hn ((ix n hn a).val + b) = ix n hn (a + b) := by
  ext
  simp [ix, Nat.add_mod]

lemma ix_shift_bijective (n : ℕ) (hn : 0 < n) (s : ℕ) :
    Function.Bijective (fun i : Fin n => ix n hn (i.val + s)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, rfl⟩
  intro i j hij
  have hmod : (i.val + s) % n = (j.val + s) % n := congrArg Fin.val hij
  have h1 : ((i.val + s) + (n - s % n)) % n = ((j.val + s) + (n - s % n)) % n := by
    rw [Nat.add_mod, hmod, ← Nat.add_mod]
  have hsimp : ∀ a : Fin n, ((a.val + s) + (n - s % n)) % n = a.val := by
    intro a
    have hs : s % n < n := Nat.mod_lt s hn
    have hdiv : s = n * (s / n) + s % n := (Nat.div_add_mod s n).symm
    have hsum : a.val + s + (n - s % n) = a.val + n * (s / n + 1) := by
      rw [mul_add, mul_one]; omega
    rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
  rw [hsimp i, hsimp j] at h1
  exact Fin.ext h1

noncomputable def shEquiv (n : ℕ) (hn : 0 < n) (s : ℕ) :
    (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Equiv.ofBijective _ (ix_shift_bijective n hn s))

lemma shEquiv_apply (n : ℕ) (hn : 0 < n) (s : ℕ) (z : Fin n → ZMod 2) :
    shEquiv n hn s z = sh n hn s z := rfl

lemma dot_sh (n : ℕ) (hn : 0 < n) (s : ℕ) (z x : Fin n → ZMod 2) :
    dot n (sh n hn s z) (sh n hn s x) = dot n z x := by
  unfold dot sh
  exact Equiv.sum_comp (Equiv.ofBijective _ (ix_shift_bijective n hn s)) (fun i => z i * x i)

lemma ind_sh_iff (n : ℕ) (hn : 0 < n) (s : ℕ) (x : Fin n → ZMod 2) :
    ind n hn (sh n hn s x) ↔ ind n hn x := by
  unfold ind sh
  have hstep : ∀ i : Fin n,
      ix n hn ((ix n hn (i.val + 1)).val + s) = ix n hn ((ix n hn (i.val + s)).val + 1) := by
    intro i
    rw [ix_add_assoc, ix_add_assoc]
    congr 1
    omega
  constructor
  · intro h i
    rcases (ix_shift_bijective n hn s).2 i with ⟨j, hj⟩
    dsimp at hj
    have hj' := h j
    rw [hstep j, hj] at hj'
    exact hj'
  · intro h i
    rw [hstep i]
    exact h (ix n hn (i.val + s))

lemma tw0_sh (n : ℕ) (hn : 0 < n) (s : ℕ) (z : Fin n → ZMod 2) :
    tw0 n hn (sh n hn s z) = tw0 n hn z := by
  rw [tw0_eq, tw0_eq]
  refine (Equiv.sum_comp (shEquiv n hn s).toEquiv (fun x =>
    if ind n hn x then sgn (dot n (sh n hn s z) x) else 0)).symm.trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  change (if ind n hn (sh n hn s x) then sgn (dot n (sh n hn s z) (sh n hn s x)) else 0) = _
  rw [ind_sh_iff, dot_sh]

lemma S0_map_sh (n : ℕ) (hn : 0 < n) (s : ℕ) (L : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    S0 n hn (L.map (shEquiv n hn s).toLinearMap) = S0 n hn L := by
  rw [S0_eq, S0_eq]
  refine Finset.sum_bij (fun z _ => (shEquiv n hn s).symm z) ?_ ?_ ?_ ?_
  · intro z hz
    rcases Submodule.mem_map.mp (Finset.mem_filter.mp hz).2 with ⟨y, hyL, hyz⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have : (shEquiv n hn s).symm z = y := by
      rw [← hyz]; exact (shEquiv n hn s).symm_apply_apply y
    rwa [this]
  · intro z1 _ z2 _ heq
    exact (shEquiv n hn s).symm.injective heq
  · intro y hy
    refine ⟨shEquiv n hn s y,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Submodule.mem_map_of_mem (Finset.mem_filter.mp hy).2⟩,
      (shEquiv n hn s).symm_apply_apply y⟩
  · intro z _
    have h1 := tw0_sh n hn s ((shEquiv n hn s).symm z)
    rw [← shEquiv_apply, (shEquiv n hn s).apply_symm_apply] at h1
    exact h1

lemma ev_sh1 (m : ℕ) (hm : 0 < m) (z : Fin (2*m) → ZMod 2) :
    ev m (sh (2*m) (by omega) 1 z) = od m z := by
  ext k
  simp only [ev, od, sh, ix]
  congr 1
  ext
  dsimp
  exact Nat.mod_eq_of_lt (by omega)

lemma od_sh1 (m : ℕ) (hm : 0 < m) (z : Fin (2*m) → ZMod 2) :
    od m (sh (2*m) (by omega) 1 z) = sh m hm 1 (ev m z) := by
  ext k
  simp only [ev, od, sh, ix]
  congr 1
  ext
  dsimp
  have h1 : 2 * k.val + 1 + 1 = 2 * (k.val + 1) := by omega
  rw [h1, Nat.mul_mod_mul_left]

lemma splitSub_map_sh1 (m : ℕ) (hm : 0 < m)
    (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    (splitSub m Le Lo).map (shEquiv (2*m) (by omega) 1).toLinearMap =
      splitSub m Lo (Le.map (shEquiv m hm 1).toLinearMap) := by
  ext y
  rw [Submodule.mem_map, mem_splitSub_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ev m (sh (2*m) (by omega) 1 z) ∈ Lo ∧
      od m (sh (2*m) (by omega) 1 z) ∈ Le.map (shEquiv m hm 1).toLinearMap
    rw [ev_sh1 m hm, od_sh1 m hm]
    exact ⟨hz.2, Submodule.mem_map.mpr ⟨ev m z, hz.1, rfl⟩⟩
  · rintro ⟨hyLo, hyLe⟩
    rcases Submodule.mem_map.mp hyLe with ⟨u, huLe, huy⟩
    refine ⟨mergeEO m u (ev m y), ?_, ?_⟩
    · rw [mem_splitSub_iff, ev_mergeEO, od_mergeEO]
      exact ⟨huLe, hyLo⟩
    · change sh (2*m) (by omega) 1 (mergeEO m u (ev m y)) = y
      rw [← mergeEO_ev_od m (sh (2*m) (by omega) 1 (mergeEO m u (ev m y))),
        ev_sh1 m hm, od_sh1 m hm, ev_mergeEO, od_mergeEO]
      conv_rhs => rw [← mergeEO_ev_od m y]
      exact congrArg (mergeEO m (ev m y)) huy

lemma S0_swap_lanes (m : ℕ) (hm : 0 < m)
    (Le Lo : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    S0 (2*m) (by omega) (splitSub m Le Lo) =
      S0 (2*m) (by omega) (splitSub m Lo (Le.map (shEquiv m hm 1).toLinearMap)) := by
  rw [← splitSub_map_sh1 m hm Le Lo, S0_map_sh]

def mergeFinset (m : ℕ) (P Q : Finset (Fin m)) : Finset (Fin (2*m)) :=
  P.image (fun k => ⟨2*k.val, by omega⟩) ∪ Q.image (fun k => ⟨2*k.val + 1, by omega⟩)

lemma card_mergeFinset (m : ℕ) (P Q : Finset (Fin m)) :
    (mergeFinset m P Q).card = P.card + Q.card := by
  unfold mergeFinset
  have hdisj : Disjoint (P.image (fun k : Fin m => (⟨2*k.val, by omega⟩ : Fin (2*m))))
      (Q.image (fun k : Fin m => (⟨2*k.val + 1, by omega⟩ : Fin (2*m)))) := by
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    rcases Finset.mem_image.mp hxP with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hxQ with ⟨b, _, hab⟩
    have hv : 2 * b.val + 1 = 2 * a.val := congrArg Fin.val hab
    omega
  rw [Finset.card_union_of_disjoint hdisj]
  congr 1
  · refine Finset.card_image_of_injective P fun a b hab => ?_
    ext; have := congrArg Fin.val hab; dsimp at this; omega
  · refine Finset.card_image_of_injective Q fun a b hab => ?_
    ext; have := congrArg Fin.val hab; dsimp at this; omega

lemma coordSub_mergeFinset (m : ℕ) (P Q : Finset (Fin m)) :
    coordSub (2*m) (mergeFinset m P Q) = splitSub m (coordSub m P) (coordSub m Q) := by
  ext z
  rw [mem_coordSub_iff, mem_splitSub_iff, mem_coordSub_iff, mem_coordSub_iff]
  constructor
  · intro hz
    constructor
    · intro k hk
      apply hz ⟨2*k.val, by omega⟩
      intro hmem
      rcases Finset.mem_union.mp hmem with hP | hQ
      · rcases Finset.mem_image.mp hP with ⟨a, ha, heq⟩
        have hv : 2 * a.val = 2 * k.val := congrArg Fin.val heq
        have : a = k := Fin.ext (by omega)
        exact hk (this ▸ ha)
      · rcases Finset.mem_image.mp hQ with ⟨b, _, heq⟩
        have hv : 2 * b.val + 1 = 2 * k.val := congrArg Fin.val heq
        omega
    · intro k hk
      apply hz ⟨2*k.val + 1, by omega⟩
      intro hmem
      rcases Finset.mem_union.mp hmem with hP | hQ
      · rcases Finset.mem_image.mp hP with ⟨a, _, heq⟩
        have hv : 2 * a.val = 2 * k.val + 1 := congrArg Fin.val heq
        omega
      · rcases Finset.mem_image.mp hQ with ⟨b, hb, heq⟩
        have hv : 2 * b.val + 1 = 2 * k.val + 1 := congrArg Fin.val heq
        have : b = k := Fin.ext (by omega)
        exact hk (this ▸ hb)
  · rintro ⟨he, ho⟩ i hi
    by_cases hmod : i.val % 2 = 0
    · let k : Fin m := ⟨i.val / 2, by omega⟩
      have hik : i = ⟨2*k.val, by omega⟩ := by ext; dsimp [k]; omega
      rw [hik]
      refine he k fun hkP => hi ?_
      rw [hik]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hkP, rfl⟩)
    · let k : Fin m := ⟨i.val / 2, by omega⟩
      have hik : i = ⟨2*k.val + 1, by omega⟩ := by ext; dsimp [k]; omega
      rw [hik]
      refine ho k fun hkQ => hi ?_
      rw [hik]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hkQ, rfl⟩)

lemma exists_noncoord_witness (m : ℕ)
    (Le : Submodule (ZMod 2) (Fin m → ZMod 2))
    (P : Finset (Fin m))
    (hP : Function.Bijective (fun x : Le => fun i : P => x.1 i.1))
    (hne : Le ≠ coordSub m P) :
    ∃ j ∈ P, ∃ r : Fin m, r ∉ P ∧ ∃ u0 ∈ Le,
      (∀ i ∈ P, u0 i = if i = j then 1 else 0) ∧ u0 r = 1 := by
  by_contra h
  push Not at h
  have hle : coordSub m P ≤ Le := by
    rw [coordSub, Submodule.span_le]
    rintro _ ⟨j, hjP, rfl⟩
    rcases hP.2 (fun i : P => if i.1 = j then 1 else 0) with ⟨⟨u0, hu0Le⟩, hu0P⟩
    have hu0_on : ∀ i ∈ P, u0 i = if i = j then 1 else 0 := fun i hi => congrFun hu0P ⟨i, hi⟩
    have hu0_eq : u0 = eVec m j := by
      ext r
      by_cases hrP : r ∈ P
      · exact hu0_on r hrP
      · have hne1 := h j hjP r hrP u0 hu0Le hu0_on
        have h0 : u0 r = 0 := (zmod2_eq_zero_iff_ne_one _).mpr hne1
        have hrj : r ≠ j := fun heq => hrP (heq ▸ hjP)
        simp [eVec, h0, hrj]
    exact hu0_eq ▸ hu0Le
  have hcard : Fintype.card Le = Fintype.card (coordSub m P) := by
    rw [Fintype.card_of_bijective hP, Fintype.card_fun, ZMod.card, Fintype.card_coe,
      ← card_filter_mem_submodule, card_coordSub]
  have hfin_eq : Finset.univ.filter (fun u => u ∈ coordSub m P) =
      Finset.univ.filter (fun u => u ∈ Le) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle (Finset.mem_filter.mp hu).2⟩
    · rw [card_filter_mem_submodule, card_filter_mem_submodule, hcard]
  apply hne
  ext u
  have := Finset.ext_iff.mp hfin_eq u
  simpa using this.symm

lemma card_sub_coordSub_ge_one (m : ℕ) (hm : 0 < m)
    (Le : Submodule (ZMod 2) (Fin m → ZMod 2))
    (P : Finset (Fin m))
    (hP : Function.Bijective (fun x : Le => fun i : P => x.1 i.1))
    (j : Fin m) (hjP : j ∈ P) (r : Fin m) (u0 : Fin m → ZMod 2)
    (hu0Le : u0 ∈ Le) (hu0P : ∀ i ∈ P, u0 i = if i = j then 1 else 0) (hu0r : u0 r = 1)
    (v : Fin m → ZMod 2) (hcj : covE m hm v j) (hcr : ¬ covE m hm v r) :
    (Finset.univ.filter (fun u : Fin m → ZMod 2 =>
        u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card + 1 ≤
    (Finset.univ.filter (fun u : Fin m → ZMod 2 =>
        u ∈ coordSub m P ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card := by
  let A := Finset.univ.filter (fun u : Fin m → ZMod 2 =>
    u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)
  let B := Finset.univ.filter (fun u : Fin m → ZMod 2 =>
    u ∈ coordSub m P ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)
  have hejB : eVec m j ∈ B := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, eVec_mem_coordSub m P hjP, ?_⟩
    intro k hk
    by_cases hkj : k = j
    · exact hkj ▸ hcj
    · simp [eVec, hkj] at hk
  let proj : (Fin m → ZMod 2) → (Fin m → ZMod 2) := fun u k => if k ∈ P then u k else 0
  have hle : A.card ≤ (B.erase (eVec m j)).card := by
    refine Finset.card_le_card_of_injOn proj ?_ ?_
    · intro u hu
      rcases (Finset.mem_filter.mp hu).2 with ⟨huLe, hcov⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩⟩
      · intro hproj_eq
        have heq_u : u = u0 := by
          have hsub : (⟨u, huLe⟩ : Le) = ⟨u0, hu0Le⟩ := by
            apply hP.1
            ext ⟨i, hi⟩
            change u i = u0 i
            have hi_eq := congrFun hproj_eq i
            simp only [proj, hi, ite_true, eVec] at hi_eq
            rw [hi_eq, hu0P i hi]
          exact congrArg Subtype.val hsub
        rw [heq_u] at hcov
        exact hcr (hcov r hu0r)
      · rw [mem_coordSub_iff]
        intro i hi
        simp [proj, hi]
      · intro k hk
        by_cases hkP : k ∈ P
        · simp only [proj, hkP, ite_true] at hk
          exact hcov k hk
        · simp only [proj, hkP, ite_false] at hk
          exact absurd hk zero_ne_one
    · intro u1 hu1 u2 hu2 heq
      have h1 := (Finset.mem_filter.mp hu1).2.1
      have h2 := (Finset.mem_filter.mp hu2).2.1
      have hsub : (⟨u1, h1⟩ : Le) = ⟨u2, h2⟩ := by
        apply hP.1
        ext ⟨i, hi⟩
        have hi_eq := congrFun heq i
        simpa [proj, hi] using hi_eq
      exact congrArg Subtype.val hsub
  have herase : (B.erase (eVec m j)).card + 1 = B.card := Finset.card_erase_add_one hejB
  change A.card + 1 ≤ B.card
  omega

lemma card_ind_covE_eq_sum (m : ℕ) (hm : 0 < m) (j r : Fin m) :
    ((Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
        ind (2*m) (by omega) x ∧ covE m hm (od m x) j ∧ ¬ covE m hm (od m x) r)).card : ℤ) =
    ∑ v ∈ Finset.univ.filter (fun v : Fin m → ZMod 2 => covE m hm v j ∧ ¬ covE m hm v r),
      (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card := by
  norm_cast
  have hterm : ∀ v : Fin m → ZMod 2,
      2 ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card =
        (Finset.univ.filter (fun a : Fin m → ZMod 2 =>
          ∀ k : Fin m, covE m hm v k → a k = 0)).card := by
    intro v
    rw [← card_coordSub]
    congr 1
    ext a
    simp [mem_coordSub_iff]
  rw [Finset.sum_congr rfl fun v _ => hterm v, ← Finset.card_sigma]
  refine Finset.card_bij (fun x _ => ⟨od m x, ev m x⟩) ?_ ?_ ?_
  · intro x hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨hind, hcj, hcr⟩
    rw [ind_two_mul_iff m hm] at hind
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj, hcr⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, hind⟩⟩
  · intro x1 _ x2 _ heq
    have hod : od m x1 = od m x2 := congrArg Sigma.fst heq
    have hev : ev m x1 = ev m x2 := by
      have h := congrArg Sigma.snd heq
      simpa using h
    rw [← mergeEO_ev_od m x1, ← mergeEO_ev_od m x2, hev, hod]
  · intro ⟨v, a⟩ hp
    rcases Finset.mem_sigma.mp hp with ⟨hv, ha⟩
    refine ⟨mergeEO m a v, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [ind_two_mul_iff m hm, ev_mergeEO, od_mergeEO]
        exact (Finset.mem_filter.mp ha).2
      · rw [od_mergeEO]
        exact (Finset.mem_filter.mp hv).2
    · simp [ev_mergeEO, od_mergeEO]

lemma S0_gap_single_lane (m : ℕ) (hm : 0 < m)
    (Le : Submodule (ZMod 2) (Fin m → ZMod 2))
    (P : Finset (Fin m))
    (hP : Function.Bijective (fun x : Le => fun i : P => x.1 i.1))
    (hne : Le ≠ coordSub m P) :
    ∃ j ∈ P, ∃ r : Fin m, r ∉ P ∧
      ((Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
          ind (2*m) (by omega) x ∧ covE m hm (od m x) j ∧ ¬ covE m hm (od m x) r)).card : ℤ) ≤
      S0 (2*m) (by omega) (splitSub m (coordSub m P) ⊥) -
        S0 (2*m) (by omega) (splitSub m Le ⊥) := by
  rcases exists_noncoord_witness m Le P hP hne with ⟨j, hjP, r, hrP, u0, hu0Le, hu0P, hu0r⟩
  refine ⟨j, hjP, r, hrP, ?_⟩
  rw [S0_split_formula m hm (coordSub m P) ⊥, S0_split_formula m hm Le ⊥]
  have hbot_card :
      (Finset.univ.filter (fun w : Fin m → ZMod 2 =>
        w ∈ (⊥ : Submodule (ZMod 2) (Fin m → ZMod 2)))).card = 1 := by
    rw [card_submodule, finrank_bot, pow_zero]
  have hbot_orth :
      Finset.univ.filter (fun v : Fin m → ZMod 2 =>
        ∀ w ∈ (⊥ : Submodule (ZMod 2) (Fin m → ZMod 2)), dot m w v = 0) = Finset.univ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, Submodule.mem_bot]
    rintro w rfl
    simp [dot]
  rw [hbot_card, hbot_orth]
  simp only [Nat.cast_one, one_mul, ← Finset.sum_sub_distrib]
  rw [card_ind_covE_eq_sum m hm j r]
  let S_sub := Finset.univ.filter (fun v : Fin m → ZMod 2 => covE m hm v j ∧ ¬ covE m hm v r)
  have hnonneg : ∀ v : Fin m → ZMod 2,
      0 ≤ ((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
              u ∈ coordSub m P ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) *
            (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card -
          ((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
              u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) *
            (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card := by
    intro v
    rw [← sub_mul]
    refine mul_nonneg ?_ (by positivity)
    have hle := card_le_coordSub_proj m hm Le P hP v
    omega
  calc
    ∑ v ∈ S_sub, (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card
        ≤ ∑ v ∈ S_sub,
            (((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
                u ∈ coordSub m P ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) *
              (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card -
            ((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
                u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) *
              (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rcases (Finset.mem_filter.mp hv).2 with ⟨hcj, hcr⟩
          rw [← sub_mul]
          have h1 := card_sub_coordSub_ge_one m hm Le P hP j hjP r u0 hu0Le hu0P hu0r v hcj hcr
          have hdiff : (1 : ℤ) ≤
              ((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
                  u ∈ coordSub m P ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) -
              ((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
                  u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) := by omega
          calc
            (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card
                = 1 * (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card := (one_mul _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ ≤ ∑ v : Fin m → ZMod 2,
          (((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
              u ∈ coordSub m P ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) *
            (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card -
          ((Finset.univ.filter (fun u : Fin m → ZMod 2 =>
              u ∈ Le ∧ ∀ k : Fin m, u k = 1 → covE m hm v k)).card : ℤ) *
            (2 : ℤ) ^ (Finset.univ.filter (fun k : Fin m => ¬ covE m hm v k)).card) := by
          exact Finset.sum_le_univ_sum_of_nonneg hnonneg

lemma S0_le_coord_with_gap (m : ℕ) (hm : 0 < m)
    (L : Submodule (ZMod 2) (Fin (2*m) → ZMod 2))
    (hsplit : ∀ z ∈ L, even (2*m) z ∈ L) :
    ∃ P Q : Finset (Fin m),
      P.card + Q.card = Module.finrank (ZMod 2) L ∧
      let R : Finset (Fin (2*m)) :=
        P.image (fun k => ⟨2*k.val, by omega⟩) ∪ Q.image (fun k => ⟨2*k.val + 1, by omega⟩)
      R.card = Module.finrank (ZMod 2) L ∧
      S0 (2*m) (by omega) L ≤ S0 (2*m) (by omega) (coordSub (2*m) R) ∧
      (Q = ∅ → L ≠ coordSub (2*m) R →
        ∃ j ∈ P, ∃ r : Fin m, r ∉ P ∧
          ((Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
              ind (2*m) (by omega) x ∧ covE m hm (od m x) j ∧ ¬ covE m hm (od m x) r)).card : ℤ) ≤
          S0 (2*m) (by omega) (coordSub (2*m) R) - S0 (2*m) (by omega) L) ∧
      (P = ∅ → L ≠ coordSub (2*m) R →
        ∃ j ∈ Q, ∃ r : Fin m, r ∉ Q ∧
          ((Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
              ind (2*m) (by omega) x ∧ covE m hm (od m x) j ∧ ¬ covE m hm (od m x) r)).card : ℤ) ≤
          S0 (2*m) (by omega) (coordSub (2*m) R) - S0 (2*m) (by omega) L) := by
  let Le := evenLane m L
  let Lo := oddLane m L
  have hL_eq : L = splitSub m Le Lo := eq_splitSub_of_split m L hsplit
  have hrank : Module.finrank (ZMod 2) L =
      Module.finrank (ZMod 2) Le + Module.finrank (ZMod 2) Lo :=
    finrank_eq_evenLane_add_oddLane m L hsplit
  rcases exists_pivot m Le with ⟨P, hPcard, hPbij⟩
  rcases exists_pivot m Lo with ⟨Q, hQcard, hQbij⟩
  refine ⟨P, Q, by omega, ?_, ?_, ?_, ?_⟩
  · change (mergeFinset m P Q).card = Module.finrank (ZMod 2) L
    rw [card_mergeFinset]; omega
  · change S0 (2*m) (by omega) L ≤ S0 (2*m) (by omega) (coordSub (2*m) (mergeFinset m P Q))
    rw [hL_eq, coordSub_mergeFinset]
    calc
      S0 (2*m) (by omega) (splitSub m Le Lo)
          ≤ S0 (2*m) (by omega) (splitSub m (coordSub m P) Lo) :=
            S0_proj_left_le m hm Le Lo P hPbij
      _ = S0 (2*m) (by omega) (splitSub m Lo ((coordSub m P).map (shEquiv m hm 1).toLinearMap)) :=
            S0_swap_lanes m hm (coordSub m P) Lo
      _ ≤ S0 (2*m) (by omega) (splitSub m (coordSub m Q) ((coordSub m P).map (shEquiv m hm 1).toLinearMap)) :=
            S0_proj_left_le m hm Lo _ Q hQbij
      _ = S0 (2*m) (by omega) (splitSub m (coordSub m P) (coordSub m Q)) :=
            (S0_swap_lanes m hm (coordSub m P) (coordSub m Q)).symm
  · intro hQempty hne
    have hLo_bot : Lo = ⊥ := by
      have hcard : (Finset.univ.filter (fun v => v ∈ Lo)).card = 1 := by
        rw [card_submodule, ← hQcard, hQempty, Finset.card_empty, pow_zero]
      have hsub : Subsingleton Lo :=
        Fintype.card_le_one_iff_subsingleton.mp (by rw [← card_filter_mem_submodule]; omega)
      ext v
      simp only [Submodule.mem_bot]
      exact ⟨fun hv => congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : Lo) 0),
        fun hv => hv ▸ Lo.zero_mem⟩
    have hcoordQ : coordSub m Q = ⊥ := by
      rw [hQempty, coordSub, Finset.coe_empty, Set.image_empty, Submodule.span_empty]
    have hR : coordSub (2*m) (mergeFinset m P Q) = splitSub m (coordSub m P) ⊥ := by
      rw [coordSub_mergeFinset, hcoordQ]
    have hL_bot : L = splitSub m Le ⊥ := by rw [hL_eq, hLo_bot]
    have hLe_ne : Le ≠ coordSub m P := by
      intro heq
      apply hne
      change L = coordSub (2*m) (mergeFinset m P Q)
      rw [hL_bot, hR, heq]
    change ∃ j ∈ P, ∃ r : Fin m, r ∉ P ∧
      ((Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
          ind (2*m) (by omega) x ∧ covE m hm (od m x) j ∧ ¬ covE m hm (od m x) r)).card : ℤ) ≤
      S0 (2*m) (by omega) (coordSub (2*m) (mergeFinset m P Q)) - S0 (2*m) (by omega) L
    rw [hR, hL_bot]
    exact S0_gap_single_lane m hm Le P hPbij hLe_ne
  · intro hPempty hne
    have hLe_bot : Le = ⊥ := by
      have hcard : (Finset.univ.filter (fun u => u ∈ Le)).card = 1 := by
        rw [card_submodule, ← hPcard, hPempty, Finset.card_empty, pow_zero]
      have hsub : Subsingleton Le :=
        Fintype.card_le_one_iff_subsingleton.mp (by rw [← card_filter_mem_submodule]; omega)
      ext u
      simp only [Submodule.mem_bot]
      exact ⟨fun hu => congrArg Subtype.val (Subsingleton.elim (⟨u, hu⟩ : Le) 0),
        fun hu => hu ▸ Le.zero_mem⟩
    have hcoordP : coordSub m P = ⊥ := by
      rw [hPempty, coordSub, Finset.coe_empty, Set.image_empty, Submodule.span_empty]
    have hR : coordSub (2*m) (mergeFinset m P Q) = splitSub m ⊥ (coordSub m Q) := by
      rw [coordSub_mergeFinset, hcoordP]
    have hL_bot : L = splitSub m ⊥ Lo := by rw [hL_eq, hLe_bot]
    have hLo_ne : Lo ≠ coordSub m Q := by
      intro heq
      apply hne
      change L = coordSub (2*m) (mergeFinset m P Q)
      rw [hL_bot, hR, heq]
    change ∃ j ∈ Q, ∃ r : Fin m, r ∉ Q ∧
      ((Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
          ind (2*m) (by omega) x ∧ covE m hm (od m x) j ∧ ¬ covE m hm (od m x) r)).card : ℤ) ≤
      S0 (2*m) (by omega) (coordSub (2*m) (mergeFinset m P Q)) - S0 (2*m) (by omega) L
    rw [hR, hL_bot, S0_swap_lanes m hm ⊥ (coordSub m Q), S0_swap_lanes m hm ⊥ Lo, Submodule.map_bot]
    exact S0_gap_single_lane m hm Lo Q hQbij hLo_ne

lemma S0_le_coord (m : ℕ) (hm : 0 < m)
    (L : Submodule (ZMod 2) (Fin (2*m) → ZMod 2))
    (hsplit : ∀ z ∈ L, even (2*m) z ∈ L) :
    ∃ R : Finset (Fin (2*m)),
      R.card = Module.finrank (ZMod 2) L ∧
      S0 (2*m) (by omega) L ≤ S0 (2*m) (by omega) (coordSub (2*m) R) := by
  rcases S0_le_coord_with_gap m hm L hsplit with ⟨P, Q, _, hcard, hle, _, _⟩
  exact ⟨_, hcard, hle⟩

-- Section 4: Lower bound on the non-coordinate gap

lemma ix_pred_val (m : ℕ) (hm : 0 < m) (k : Fin m) :
    (ix m hm (k.val + m - 1)).val = if k.val = 0 then m - 1 else k.val - 1 := by
  dsimp [ix]
  have hk := k.isLt
  split_ifs with h0
  · rw [h0, zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · have : k.val + m - 1 = (k.val - 1) + m := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma noncoord_gap_pinned (m : ℕ) (hm : 5 ≤ m) (j r : Fin m) (hjr : j ≠ r) :
    ∃ Z : Finset (Fin (2*m)), Z.card ≤ 6 ∧ ∃ z0 ∈ Z,
      (Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
          ind (2*m) (by omega) x ∧ ∀ i ∈ Z, x i = 0)).card ≤
      (Finset.univ.filter (fun x : Fin (2*m) → ZMod 2 =>
          ind (2*m) (by omega) x ∧ covE m (by omega) (od m x) j ∧ ¬ covE m (by omega) (od m x) r)).card := by
  have hm0 : 0 < m := by omega
  let jm : Fin m := ix m hm0 (j.val + m - 1)
  let rm : Fin m := ix m hm0 (r.val + m - 1)
  have hku : ∃ k : Fin m, (k = jm ∨ k = j) ∧ k ≠ rm ∧ k ≠ r := by
    by_cases h1 : j ≠ rm
    · exact ⟨j, Or.inr rfl, h1, hjr⟩
    · push Not at h1
      refine ⟨jm, Or.inl rfl, ?_, ?_⟩
      · intro hjm_rm
        apply hjr
        have hjm_v := ix_pred_val m hm0 j
        have hrm_v := ix_pred_val m hm0 r
        have hv : jm.val = rm.val := congrArg Fin.val hjm_rm
        ext
        have := j.isLt; have := r.isLt
        dsimp [jm, rm] at hv
        rw [hjm_v, hrm_v] at hv
        split_ifs at hv <;> omega
      · intro hjm_r
        have hjm_v := ix_pred_val m hm0 j
        have hrm_v := ix_pred_val m hm0 r
        have hv1 : j.val = rm.val := congrArg Fin.val h1
        have hv2 : jm.val = r.val := congrArg Fin.val hjm_r
        dsimp [jm, rm] at hv1 hv2
        rw [hrm_v] at hv1
        rw [hjm_v] at hv2
        have := j.isLt; have := r.isLt
        split_ifs at hv1 hv2 <;> omega
  rcases hku with ⟨ku, hku_j, hku_rm, hku_r⟩
  let u : Fin (2*m) := ⟨2 * ku.val + 1, by omega⟩
  let u_prev : Fin (2*m) := ix (2*m) (by omega) (u.val + 2*m - 1)
  let u_next : Fin (2*m) := ix (2*m) (by omega) (u.val + 1)
  let r1 : Fin (2*m) := ⟨2 * rm.val + 1, by omega⟩
  let r2 : Fin (2*m) := ⟨2 * r.val + 1, by omega⟩
  let Z : Finset (Fin (2*m)) := {u_prev, u, u_next, r1, r2}
  have hZcard : Z.card ≤ 6 := by
    have h5 : Z.card ≤ 5 := by
      calc
        Z.card ≤ ({u, u_next, r1, r2} : Finset (Fin (2*m))).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({u_next, r1, r2} : Finset (Fin (2*m))).card + 1 + 1 := by
          have := Finset.card_insert_le u ({u_next, r1, r2} : Finset (Fin (2*m))); omega
        _ ≤ ({r1, r2} : Finset (Fin (2*m))).card + 1 + 1 + 1 := by
          have := Finset.card_insert_le u_next ({r1, r2} : Finset (Fin (2*m))); omega
        _ ≤ ({r2} : Finset (Fin (2*m))).card + 1 + 1 + 1 + 1 := by
          have := Finset.card_insert_le r1 ({r2} : Finset (Fin (2*m))); omega
        _ = 5 := by simp
    omega
  have huZ : u ∈ Z := by simp [Z]
  have hu_prev_Z : u_prev ∈ Z := by simp [Z]
  have hu_next_Z : u_next ∈ Z := by simp [Z]
  have hr1Z : r1 ∈ Z := by simp [Z]
  have hr2Z : r2 ∈ Z := by simp [Z]
  have hu_ne_r1 : r1 ≠ u := by
    intro h; apply hku_rm; ext; have := congrArg Fin.val h; dsimp [r1, u] at this; omega
  have hu_ne_r2 : r2 ≠ u := by
    intro h; apply hku_r; ext; have := congrArg Fin.val h; dsimp [r2, u] at this; omega
  have hu_ne_next : u_next ≠ u := by
    intro h
    have hv : (u.val + 1) % (2*m) = u.val := congrArg Fin.val h
    have hu_lt := u.isLt
    by_cases hlast : u.val + 1 = 2*m
    · rw [hlast, Nat.mod_self] at hv; dsimp [u] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
  have hu_ne_prev : u_prev ≠ u := by
    intro h
    have hv : u_prev.val = u.val := congrArg Fin.val h
    have hp := ix_pred_val (2*m) (by omega) u
    dsimp [u_prev] at hv
    rw [hp] at hv
    dsimp [u] at hv
    omega
  refine ⟨Z, hZcard, u, huZ, ?_⟩
  let f : (Fin (2*m) → ZMod 2) → (Fin (2*m) → ZMod 2) := fun x => Function.update x u 1
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro x hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨hind, hxZ⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro i
      by_cases hiu : i = u
      · rw [hiu]
        change Function.update x u 1 u * Function.update x u 1 u_next = 0
        rw [Function.update_of_ne hu_ne_next, hxZ u_next hu_next_Z, mul_zero]
      · by_cases hnu : ix (2*m) (by omega) (i.val + 1) = u
        · have hi_prev : i = u_prev := by
            have h1 := ix_succ_pred (2*m) (by omega) i
            rw [hnu] at h1
            exact h1.symm
          rw [hi_prev]
          dsimp only [f]
          rw [Function.update_of_ne hu_ne_prev, hxZ u_prev hu_prev_Z, zero_mul]
        · dsimp only [f]
          rw [Function.update_of_ne hiu, Function.update_of_ne hnu]
          exact hind i
    · have hku1 : od m (f x) ku = 1 := by
        change Function.update x u 1 u = 1
        exact Function.update_self u 1 x
      rcases hku_j with rfl | rfl
      · exact Or.inl hku1
      · exact Or.inr hku1
    · intro hcov
      rcases hcov with h1 | h2
      · change Function.update x u 1 r1 = 1 at h1
        rw [Function.update_of_ne hu_ne_r1, hxZ r1 hr1Z] at h1
        exact zero_ne_one h1
      · change Function.update x u 1 r2 = 1 at h2
        rw [Function.update_of_ne hu_ne_r2, hxZ r2 hr2Z] at h2
        exact zero_ne_one h2
  · intro x1 hx1 x2 hx2 heq
    have h1u := (Finset.mem_filter.mp hx1).2.2 u huZ
    have h2u := (Finset.mem_filter.mp hx2).2.2 u huZ
    ext i
    by_cases hiu : i = u
    · rw [hiu, h1u, h2u]
    · have hi_eq := congrFun heq i
      simpa [f, Function.update_of_ne hiu] using hi_eq

end Pivot33638

-- =========================================================================
-- Final assembly for L_meta_33638
-- =========================================================================

namespace Assembly33638

open scoped Classical

lemma adm_true_iff_ind (n : ℕ) (hn : 0 < n) (x : Fin n → ZMod 2) :
    adm n hn (fun _ => true) x ↔ Test33638.ind n hn x := by
  constructor
  · intro H i
    have h1 := H (ix n hn (i.val + n - 1)) rfl
    have he1 : ix n hn ((ix n hn (i.val + n - 1)).val + 1) = i := by
      rw [ix_val_add]
      have : i.val + n - 1 + 1 = i.val + n := by omega
      rw [this, ix_add_n, ix_self]
    have he2 : ix n hn ((ix n hn (i.val + n - 1)).val + 2) = ix n hn (i.val + 1) := by
      rw [ix_val_add]
      have : i.val + n - 1 + 2 = (i.val + 1) + n := by omega
      rw [this, ix_add_n]
    rw [he1, he2] at h1
    exact h1
  · intro H i _
    have h1 : x (ix n hn (i.val + 1)) * x (ix n hn ((ix n hn (i.val + 1)).val + 1)) = 0 :=
      H (ix n hn (i.val + 1))
    have he : ix n hn ((ix n hn (i.val + 1)).val + 1) = ix n hn (i.val + 2) := by
      rw [ix_val_add]
    rw [he] at h1
    exact h1

lemma tw_true_eq_tw0 (n : ℕ) (hn : 0 < n) (z : Fin n → ZMod 2) :
    tw n hn (fun _ => true) z = Test33638.tw0 n hn z := by
  rw [tw_eq_sum]
  unfold Test33638.tw0
  refine Finset.sum_congr (by ext x; simp) (fun x _ => ?_)
  by_cases h : adm n hn (fun _ => true) x
  · have h' : Test33638.ind n hn x := (adm_true_iff_ind n hn x).mp h
    simp only [h, h', ↓reduceIte]; rfl
  · have h' : ¬ Test33638.ind n hn x := fun hi => h ((adm_true_iff_ind n hn x).mpr hi)
    simp only [h, h', ↓reduceIte]

lemma Ssum_true_eq_S0 (n : ℕ) (hn : 0 < n) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Ssum n hn (fun _ => true) D = Test33638.S0 n hn D := by
  unfold Ssum Test33638.S0
  refine Finset.sum_congr rfl (fun z _ => tw_true_eq_tw0 n hn z)

def R_block (n : ℕ) (hn : 0 < n) (h : ℕ) : Finset (Fin n) :=
  Finset.univ.image (fun j : Fin h => ix n hn (2 * j.val))

def L_block (n : ℕ) (hn : 0 < n) (h : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Pivot33638.coordSub n (R_block n hn h)

noncomputable def checkSub (n : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (base n))

noncomputable def D_block (n : ℕ) (hn : 0 < n) (h : ℕ) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  checkSub n ⊔ L_block n hn h

lemma checkSub_finrank_eq_four (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Module.finrank (ZMod 2) (checkSub n) = 4 := by
  have hge := base_span_finrank n hn h6
  have hle : Module.finrank (ZMod 2) (checkSub n) ≤ 4 := by
    unfold checkSub
    have h1 := finrank_span_le_card (R := ZMod 2) (Set.range (base n))
    have hset : (Set.range (base n)).toFinset = Finset.univ.image (base n) := by
      ext x; simp
    have h2 : (Set.range (base n)).toFinset.card ≤ 4 := by
      rw [hset]
      calc (Finset.univ.image (base n)).card
          ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
        _ = 4 := by simp
    exact le_trans h1 h2
  exact le_antisymm hle hge

lemma R_block_card (n : ℕ) (hn : 0 < n) (h : ℕ) (h2h : 2 * h ≤ n) :
    (R_block n hn h).card = h := by
  unfold R_block
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    have hmod := congrArg Fin.val hab
    simp only [ix, Nat.mod_eq_of_lt (by omega : 2 * a.val < n),
      Nat.mod_eq_of_lt (by omega : 2 * b.val < n)] at hmod
    exact Fin.ext (by omega)

lemma mem_R_block_zero (n : ℕ) (hn : 0 < n) (h : ℕ) (hh : 1 ≤ h) :
    (⟨0, hn⟩ : Fin n) ∈ R_block n hn h := by
  unfold R_block
  refine Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
  ext; simp [ix]

lemma fib_add_le_pow_two_mul (k r : ℕ) (hk : 1 ≤ k) :
    Nat.fib (k + r) ≤ 2 ^ r * Nat.fib k := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hstep : Nat.fib (k + (r + 1)) ≤ 2 * Nat.fib (k + r) := by
      obtain ⟨m, hm⟩ : ∃ m, k + r = m + 1 := ⟨k + r - 1, by omega⟩
      rw [show k + (r + 1) = m + 2 by omega, hm, Nat.fib_add_two]
      have hmono : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_mono (by omega)
      omega
    calc Nat.fib (k + (r + 1))
        ≤ 2 * Nat.fib (k + r) := hstep
      _ ≤ 2 * (2 ^ r * Nat.fib k) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (r + 1) * Nat.fib k := by ring

lemma fib_step_four (k : ℕ) (hk : 1 ≤ k) :
    Nat.fib (k + 2) + Nat.fib k ≤ 4 * Nat.fib k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h1 : Nat.fib (m + 1 + 2) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have h2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have hm : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_mono (by omega)
  omega

lemma block_val_mono_pos (n : ℕ) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : 2 * b < n) :
    2 ^ (2 * a - 1) * Nat.fib (n - 2 * a + 3) ≤ 2 ^ (2 * b - 1) * Nat.fib (n - 2 * b + 3) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · have hb1 : 1 ≤ b := by omega
      calc 2 ^ (2 * a - 1) * Nat.fib (n - 2 * a + 3)
          ≤ 2 ^ (2 * b - 1) * Nat.fib (n - 2 * b + 3) := ih (by omega) (by omega)
        _ ≤ 2 ^ (2 * (b + 1) - 1) * Nat.fib (n - 2 * (b + 1) + 3) := by
            have hpow : 2 ^ (2 * (b + 1) - 1) = 2 ^ (2 * b - 1) * 4 := by
              rw [show 2 * (b + 1) - 1 = (2 * b - 1) + 2 by omega, pow_add]; norm_num
            rw [hpow, mul_assoc]
            refine Nat.mul_le_mul_left _ ?_
            have h4 := fib_step_four (n - 2 * (b + 1) + 3) (by omega)
            rw [show n - 2 * (b + 1) + 3 + 2 = n - 2 * b + 3 by omega] at h4
            omega

lemma segGaps_evens (k lo hi : ℕ) (hle : lo + 2 * k ≤ hi) :
    Test33638.segGaps lo hi (List.ofFn (fun j : Fin k => lo + 1 + 2 * j.val)) =
      List.replicate k 1 ++ [hi - lo - 2 * k] := by
  induction k generalizing lo with
  | zero =>
    simp [Test33638.segGaps]
  | succ k ih =>
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, mul_zero, add_zero, Fin.val_succ, Test33638.segGaps]
    have h1 : lo + 1 - lo = 1 := by omega
    rw [h1]
    have hfun : (fun j : Fin k => lo + 1 + 2 * (j.val + 1)) =
        (fun j : Fin k => (lo + 1 + 1) + 1 + 2 * j.val) := by
      funext j; omega
    rw [hfun, ih (lo + 1 + 1) (by omega)]
    rw [List.replicate_succ, List.cons_append]
    congr 2
    have hsub : hi - (lo + 1 + 1) - 2 * k = hi - lo - 2 * (k + 1) := by omega
    rw [hsub]

lemma S0_L_block_eq (n : ℕ) (hn : 0 < n) (h : ℕ) (hh : 1 ≤ h) (h2h : 2 * h < n) :
    Test33638.S0 n hn (L_block n hn h) = (2 : ℤ) ^ (2 * h - 1) * (Nat.fib (n - 2 * h + 3) : ℤ) := by
  have hS0 : Test33638.S0 n hn (L_block n hn h) = Pivot33638.S0 n hn (Pivot33638.coordSub n (R_block n hn h)) := rfl
  rw [hS0, Pivot33638.S0_coord_eq, R_block_card n hn h (by omega)]
  have hpin := Test33638.ind_cycle_pinned_zero n hn (R_block n hn h) (mem_R_block_zero n hn h hh)
  rcases hpin with ⟨hlen, hsum, hbnd, hstrict, hRiff, hcard⟩
  set cs := ((R_block n hn h).erase ⟨0, hn⟩ |>.image Fin.val).sort (· ≤ ·)
  let target : List ℕ := List.ofFn (fun j : Fin (h - 1) => 1 + 1 + 2 * j.val)
  have hcs_eq : cs = target := by
    have htar_strict : target.Pairwise (· < ·) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [target, List.getElem_ofFn]
      omega
    have htar_nodup : target.Nodup := htar_strict.imp (fun h => ne_of_lt h)
    have hcs_nodup : cs.Nodup := hstrict.imp (fun h => ne_of_lt h)
    have hperm : cs.Perm target := by
      rw [List.perm_ext_iff_of_nodup hcs_nodup htar_nodup]
      intro v
      constructor
      · intro hv
        have hv1 := (hbnd v hv).1
        have hv2 := (hbnd v hv).2
        have hmemR : (⟨v, hv2⟩ : Fin n) ∈ R_block n hn h := (hRiff ⟨v, hv2⟩).mpr (Or.inr hv)
        rcases Finset.mem_image.mp hmemR with ⟨j, _, hj⟩
        have hveq : v = 2 * j.val := by
          have := congrArg Fin.val hj
          simp only [ix, Nat.mod_eq_of_lt (by omega : 2 * j.val < n)] at this
          omega
        simp only [target, List.mem_ofFn]
        exact ⟨⟨j.val - 1, by omega⟩, by dsimp; omega⟩
      · intro hv
        simp only [target, List.mem_ofFn] at hv
        rcases hv with ⟨j, rfl⟩
        have hlt : 1 + 1 + 2 * j.val < n := by omega
        have hmemR : (⟨1 + 1 + 2 * j.val, hlt⟩ : Fin n) ∈ R_block n hn h := by
          unfold R_block
          refine Finset.mem_image.mpr ⟨⟨j.val + 1, by omega⟩, Finset.mem_univ _, ?_⟩
          ext; simp only [ix, Nat.mod_eq_of_lt (by omega : 2 * (j.val + 1) < n)]; omega
        rcases (hRiff ⟨1 + 1 + 2 * j.val, hlt⟩).mp hmemR with h0 | hcs
        · dsimp at h0; omega
        · exact hcs
    exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
      (hstrict.imp (fun h => le_of_lt h)) (htar_strict.imp (fun h => le_of_lt h))
  have hcard' : (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      Pivot33638.ind n hn x ∧ ∀ i ∈ R_block n hn h, x i = 0)).card =
      ((Test33638.segGaps 1 n cs).map (fun a => Nat.fib (a + 2))).prod := by
    rw [← hcard]; congr 1
  rw [hcard', hcs_eq]
  rw [segGaps_evens (h - 1) 1 n (by omega)]
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    List.prod_append, List.prod_replicate, List.prod_cons, List.prod_nil, mul_one]
  have hf3 : Nat.fib (1 + 2) = 2 := by decide
  rw [hf3]
  have hidx : n - 1 - 2 * (h - 1) + 2 = n - 2 * h + 3 := by omega
  rw [hidx]
  push_cast
  rw [← mul_assoc, ← pow_add, show h + (h - 1) = 2 * h - 1 by omega]

lemma coordSub_map_shL (n : ℕ) (hn : 0 < n) (s : ℕ) (R : Finset (Fin n)) :
    (Pivot33638.coordSub n R).map (Decay33638.shL n hn s).toLinearMap =
      Pivot33638.coordSub n (R.image (fun j => ix n hn (j.val + n - s % n))) := by
  ext z
  simp only [Submodule.mem_map, Pivot33638.mem_coordSub_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩ i hi
    show w (ix n hn (i.val + s)) = 0
    apply hw
    intro hmem
    apply hi
    refine Finset.mem_image.mpr ⟨ix n hn (i.val + s), hmem, ?_⟩
    ext
    simp only [ix]
    have hsm : s % n < n := Nat.mod_lt s hn
    have hmod1 : (i.val + s) % n + n - s % n = (i.val + s) % n + (n - s % n) := by omega
    rw [hmod1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hdiv := Nat.div_add_mod s n
    have hmul : (s / n + 1) * n = n * (s / n) + n := by ring
    have hmod2 : i.val + s + (n - s % n) = i.val + (s / n + 1) * n := by omega
    rw [hmod2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  · intro hz
    refine ⟨Decay33638.sh n hn (n - s % n) z, ?_, ?_⟩
    · intro i hi
      show z (ix n hn (i.val + (n - s % n))) = 0
      apply hz
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨j, hj, heq⟩
      have hj_eq : j = i := by
        have h1 := congrArg Fin.val heq
        simp only [ix] at h1
        have hsm : s % n < n := Nat.mod_lt s hn
        have heq1 : j.val + n - s % n = j.val + (n - s % n) := by omega
        rw [heq1] at h1
        have h2 : (j.val + (n - s % n) + s % n) % n = (i.val + (n - s % n) + s % n) % n := by
          rw [Nat.add_mod, h1, ← Nat.add_mod]
        have h3j : j.val + (n - s % n) + s % n = j.val + n := by omega
        have h3i : i.val + (n - s % n) + s % n = i.val + n := by omega
        rw [h3j, h3i, Nat.add_mod_right, Nat.add_mod_right,
          Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt i.isLt] at h2
        exact Fin.ext h2
      exact hi (hj_eq ▸ hj)
    · funext i
      show z (ix n hn ((ix n hn (i.val + s)).val + (n - s % n))) = z i
      congr 1
      rw [ix_val_add]
      ext; simp only [ix]
      have hsm : s % n < n := Nat.mod_lt s hn
      have hdiv := Nat.div_add_mod s n
      have hmul : (s / n + 1) * n = n * (s / n) + n := by ring
      have heq : i.val + s + (n - s % n) = i.val + (s / n + 1) * n := by omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

lemma card_pinned_sh (n : ℕ) (hn : 0 < n) (s : ℕ) (R : Finset (Fin n)) :
    (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      Test33638.ind n hn x ∧ ∀ i ∈ R.image (fun j => ix n hn (j.val + n - s % n)), x i = 0)).card =
    (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      Test33638.ind n hn x ∧ ∀ i ∈ R, x i = 0)).card := by
  have h1 := Pivot33638.S0_coord_eq n hn R
  have h2 := Pivot33638.S0_coord_eq n hn (R.image (fun j => ix n hn (j.val + n - s % n)))
  have hinj : Function.Injective (fun j : Fin n => ix n hn (j.val + n - s % n)) := by
    intro a b hab
    have hm := congrArg Fin.val hab
    simp only [ix] at hm
    have hsm : s % n < n := Nat.mod_lt s hn
    have h1 : (a.val + n - s % n + s % n) % n = (b.val + n - s % n + s % n) % n := by
      rw [Nat.add_mod, hm, ← Nat.add_mod]
    have h2a : a.val + n - s % n + s % n = a.val + n := by omega
    have h2b : b.val + n - s % n + s % n = b.val + n := by omega
    rw [h2a, h2b, Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h1
    exact Fin.ext h1
  have hcardR : (R.image (fun j => ix n hn (j.val + n - s % n))).card = R.card :=
    Finset.card_image_of_injective R hinj
  have hS0eq : Pivot33638.S0 n hn (Pivot33638.coordSub n (R.image (fun j => ix n hn (j.val + n - s % n)))) =
      Pivot33638.S0 n hn (Pivot33638.coordSub n R) := by
    rw [← coordSub_map_shL n hn s R]
    exact Decay33638.sh_S0 n hn s (Pivot33638.coordSub n R)
  rw [h1, h2, hcardR] at hS0eq
  have hpos : (0 : ℤ) < (2 : ℤ) ^ R.card := by positivity
  have hcast : ((Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      Pivot33638.ind n hn x ∧ ∀ i ∈ R.image (fun j => ix n hn (j.val + n - s % n)), x i = 0)).card : ℤ) =
    ((Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      Pivot33638.ind n hn x ∧ ∀ i ∈ R, x i = 0)).card : ℤ) :=
    mul_left_cancel₀ hpos.ne' hS0eq
  exact_mod_cast hcast

lemma card_pinned_ge_fib_n_sub_4 (n : ℕ) (hn : 10 ≤ n) (Z : Finset (Fin n))
    (hZle : Z.card ≤ 6) (z0 : Fin n) (hz0 : z0 ∈ Z) :
    Nat.fib (n - 4) ≤ (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
      Test33638.ind n (by omega) x ∧ ∀ i ∈ Z, x i = 0)).card := by
  have hn0 : 0 < n := by omega
  let Z' := Z.image (fun j => ix n hn0 (j.val + n - z0.val % n))
  have hcard_eq := card_pinned_sh n hn0 z0.val Z
  rw [← hcard_eq]
  have hz0_in : (⟨0, hn0⟩ : Fin n) ∈ Z' := by
    refine Finset.mem_image.mpr ⟨z0, hz0, ?_⟩
    ext; simp only [ix, Nat.mod_eq_of_lt z0.isLt, show z0.val + n - z0.val = n by omega, Nat.mod_self]
  have hZ'card : Z'.card ≤ 6 := le_trans Finset.card_image_le hZle
  rcases Test33638.ind_cycle_pinned_zero n hn0 Z' hz0_in with ⟨hlen, hsum, _, _, _, hcard⟩
  rw [hcard]
  have hge := Test33638.list_fib_prod_ge (Test33638.segGaps 1 n (((Z'.erase ⟨0, hn0⟩).image Fin.val).sort (· ≤ ·)))
    (by rw [Test33638.segGaps_length]; omega)
  calc Nat.fib (n - 4)
      ≤ Nat.fib ((Test33638.segGaps 1 n (((Z'.erase ⟨0, hn0⟩).image Fin.val).sort (· ≤ ·))).sum + 2) :=
        Nat.fib_mono (by omega)
    _ ≤ _ := hge

lemma S0_coord_block_or_gap (n : ℕ) (hn : 0 < n) (h : ℕ) (hh : 1 ≤ h) (hbig : 3 * h + 10 ≤ n)
    (R : Finset (Fin n)) (hRle : R.card ≤ h) :
    (R.card = h ∧ ∃ s : ℕ, R = Finset.univ.image (fun j : Fin h => ix n hn (s + 2 * j.val))) ∨
    Test33638.S0 n hn (Pivot33638.coordSub n R) + (Nat.fib (n - 4) : ℤ) ≤
      Test33638.S0 n hn (L_block n hn h) := by
  have hLb := S0_L_block_eq n hn h hh (by omega)
  rcases Nat.eq_zero_or_pos R.card with hd0 | hdpos
  · right
    have hRempty : R = ∅ := Finset.card_eq_zero.mp hd0
    subst hRempty
    have hS0e : Test33638.S0 n hn (Pivot33638.coordSub n ∅) =
        ((Finset.univ.filter (Test33638.ind n hn)).card : ℤ) := by
      have h1 := Pivot33638.S0_coord_eq n hn ∅
      change Pivot33638.S0 n hn (Pivot33638.coordSub n ∅) = _
      rw [h1]; simp only [Finset.card_empty, pow_zero, one_mul, Finset.notMem_empty,
        IsEmpty.forall_iff, implies_true, and_true]
      congr 2
    rw [hS0e, hLb]
    have hluc := Test33638.indCard_eq_lucas n (by omega)
    have hcard_eq : (Finset.univ.filter (Test33638.ind n hn)).card = Nat.fib (n - 1) + Nat.fib (n + 1) := by
      rw [← hluc]
    rw [hcard_eq]
    have hmono := block_val_mono_pos n 1 h (le_rfl) hh (by omega)
    simp only [mul_one, show 2 - 1 = 1 by omega, pow_one,
      show n - 2 + 3 = n + 1 by omega] at hmono
    have hfib : Nat.fib (n + 1) = Nat.fib (n - 1) + Nat.fib n := by
      rw [show n + 1 = (n - 1) + 2 by omega, Nat.fib_add_two, show n - 1 + 1 = n by omega]
    have hfn : Nat.fib (n - 4) ≤ Nat.fib n := Nat.fib_mono (by omega)
    have hnat : Nat.fib (n - 1) + Nat.fib (n + 1) + Nat.fib (n - 4) ≤
        2 ^ (2 * h - 1) * Nat.fib (n - 2 * h + 3) := by omega
    exact_mod_cast hnat
  · obtain ⟨r0, hr0⟩ := Finset.card_pos.mp hdpos
    let R' := R.image (fun j => ix n hn (j.val + n - r0.val % n))
    have hinj : Function.Injective (fun j : Fin n => ix n hn (j.val + n - r0.val % n)) := by
      intro a b hab
      have hm := congrArg Fin.val hab
      simp only [ix] at hm
      have hsm : r0.val % n < n := Nat.mod_lt r0.val hn
      have h1 : (a.val + n - r0.val % n + r0.val % n) % n = (b.val + n - r0.val % n + r0.val % n) % n := by
        rw [Nat.add_mod, hm, ← Nat.add_mod]
      have h2a : a.val + n - r0.val % n + r0.val % n = a.val + n := by omega
      have h2b : b.val + n - r0.val % n + r0.val % n = b.val + n := by omega
      rw [h2a, h2b, Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h1
      exact Fin.ext h1
    have hR'card : R'.card = R.card := Finset.card_image_of_injective R hinj
    have h0in : (⟨0, hn⟩ : Fin n) ∈ R' := by
      refine Finset.mem_image.mpr ⟨r0, hr0, ?_⟩
      ext; simp only [ix, Nat.mod_eq_of_lt r0.isLt, show r0.val + n - r0.val = n by omega, Nat.mod_self]
    have hS0R : Test33638.S0 n hn (Pivot33638.coordSub n R) =
        (2 : ℤ) ^ R.card * ((Finset.univ.filter (fun x : Fin n → ZMod 2 =>
          Test33638.ind n hn x ∧ ∀ i ∈ R', x i = 0)).card : ℤ) := by
      have h1 := Pivot33638.S0_coord_eq n hn R
      have h2 := card_pinned_sh n hn r0.val R
      change Pivot33638.S0 n hn (Pivot33638.coordSub n R) = _
      rw [h1]
      congr 2
      have hflt : (Finset.univ.filter (fun x : Fin n → ZMod 2 => Pivot33638.ind n hn x ∧ ∀ i ∈ R, x i = 0)) =
          (Finset.univ.filter (fun x : Fin n → ZMod 2 => Test33638.ind n hn x ∧ ∀ i ∈ R, x i = 0)) := by
        ext x; simp [Pivot33638.ind, Test33638.ind, Pivot33638.ix, Test33638.ix]
      rw [hflt, ← h2]
    rcases Test33638.ind_cycle_pinned_zero n hn R' h0in with ⟨hlen, hsum, hbnd, hstrict, hRiff, hcard⟩
    set cs := ((R'.erase ⟨0, hn⟩).image Fin.val).sort (· ≤ ·)
    set G := Test33638.segGaps 1 n cs
    have hGlen_cs : G.length = cs.length + 1 := Test33638.segGaps_length 1 n cs
    have hGlen : G.length = R.card := by omega
    have hGsum : G.sum = n - R.card := by omega
    rcases lt_or_eq_of_le hRle with hdlt | hdeq
    · right
      have hle := Test33638.list_fib_prod_le R.card G hGlen hdpos (by omega)
      rw [hGsum] at hle
      have hprod_le : 2 ^ R.card * (G.map (fun a => Nat.fib (a + 2))).prod ≤
          2 ^ (2 * R.card - 1) * Nat.fib (n - 2 * R.card + 3) := by
        calc 2 ^ R.card * (G.map (fun a => Nat.fib (a + 2))).prod
            ≤ 2 ^ R.card * (2 ^ (R.card - 1) * Nat.fib (n - R.card - R.card + 3)) :=
              Nat.mul_le_mul_left _ hle
          _ = 2 ^ (2 * R.card - 1) * Nat.fib (n - 2 * R.card + 3) := by
              rw [← mul_assoc, ← pow_add, show R.card + (R.card - 1) = 2 * R.card - 1 by omega,
                show n - R.card - R.card + 3 = n - 2 * R.card + 3 by omega]
      have hmono := block_val_mono_pos n (R.card + 1) h (by omega) (by omega) (by omega)
      have hstep : 2 ^ (2 * R.card - 1) * Nat.fib (n - 2 * R.card + 3) +
          2 ^ (2 * R.card - 1) * Nat.fib (n - 2 * (R.card + 1) + 3) ≤
          2 ^ (2 * (R.card + 1) - 1) * Nat.fib (n - 2 * (R.card + 1) + 3) := by
        have hpow : 2 ^ (2 * (R.card + 1) - 1) = 2 ^ (2 * R.card - 1) * 4 := by
          rw [show 2 * (R.card + 1) - 1 = (2 * R.card - 1) + 2 by omega, pow_add]; norm_num
        rw [hpow, mul_assoc, ← mul_add]
        refine Nat.mul_le_mul_left _ ?_
        have h4 := fib_step_four (n - 2 * (R.card + 1) + 3) (by omega)
        rw [show n - 2 * (R.card + 1) + 3 + 2 = n - 2 * R.card + 3 by omega] at h4
        exact h4
      have hfib_gap : Nat.fib (n - 4) ≤ 2 ^ (2 * R.card - 1) * Nat.fib (n - 2 * (R.card + 1) + 3) := by
        calc Nat.fib (n - 4)
            ≤ Nat.fib (n - 2 * (R.card + 1) + 3 + (2 * R.card - 1)) := Nat.fib_mono (by omega)
          _ ≤ 2 ^ (2 * R.card - 1) * Nat.fib (n - 2 * (R.card + 1) + 3) :=
              fib_add_le_pow_two_mul _ _ (by omega)
      rw [hS0R, hcard, hLb]
      have hnat : 2 ^ R.card * (G.map (fun a => Nat.fib (a + 2))).prod + Nat.fib (n - 4) ≤
          2 ^ (2 * h - 1) * Nat.fib (n - 2 * h + 3) := by omega
      exact_mod_cast hnat
    · by_cases hperm : G.Perm (List.replicate cs.length 1 ++ [n - 2 * h + 1])
      · left
        refine ⟨hdeq, ?_⟩
        have hlen_cs : cs.length + 1 = h := by omega
        obtain ⟨s', hs'⟩ := Test33638.segGaps_perm_block n hn cs (n - 2 * h + 1) hbnd hstrict
          (by omega) hperm
        refine ⟨s' + r0.val, ?_⟩
        ext x
        rw [Finset.mem_image]
        have hxR : x ∈ R ↔ ix n hn (x.val + n - r0.val % n) ∈ R' := by
          constructor
          · intro hx; exact Finset.mem_image_of_mem _ hx
          · intro hx
            rcases Finset.mem_image.mp hx with ⟨y, hy, hyx⟩
            exact (hinj hyx) ▸ hy
        rw [hxR, hRiff, hs']
        constructor
        · rintro ⟨j, hj⟩
          refine ⟨⟨j.val, by omega⟩, Finset.mem_univ _, ?_⟩
          have h1 := congrArg Fin.val hj
          simp only [ix, Test33638.ix] at h1
          have hsm : r0.val % n < n := Nat.mod_lt r0.val hn
          have h2 : (x.val + n - r0.val % n + r0.val % n) % n = ((s' + 2 * j.val) % n + r0.val % n) % n := by
            rw [Nat.add_mod, h1, Nat.mod_mod]
          rw [show x.val + n - r0.val % n + r0.val % n = x.val + n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt] at h2
          ext; simp only [ix]
          have h3 : ((s' + 2 * j.val) % n + r0.val % n) % n = (s' + r0.val + 2 * j.val) % n := by
            rw [← Nat.add_mod, show s' + 2 * j.val + r0.val = s' + r0.val + 2 * j.val by omega]
          rw [h2, h3]
        · rintro ⟨j, _, rfl⟩
          refine ⟨⟨j.val, by omega⟩, ?_⟩
          ext; simp only [ix, Test33638.ix]
          have hsm : r0.val % n < n := Nat.mod_lt r0.val hn
          rw [show (s' + r0.val + 2 * j.val) % n + n - r0.val % n =
            (s' + r0.val + 2 * j.val) % n + (n - r0.val % n) by omega,
            Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hdiv := Nat.div_add_mod r0.val n
          have hmul : (r0.val / n + 1) * n = n * (r0.val / n) + n := by ring
          have heq : s' + r0.val + 2 * j.val + (n - r0.val % n) =
              s' + 2 * j.val + (r0.val / n + 1) * n := by omega
          rw [heq, Nat.add_mul_mod_self_right]
      · right
        have hh2 : 2 ≤ h := by
          by_contra hh1
          have hh1' : h = 1 := by omega
          have hcs0 : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
          apply hperm
          dsimp [G]; rw [hcs0, hh1']
          simp only [Test33638.segGaps, List.length_nil, List.replicate_zero, List.nil_append,
            show n - 2 * 1 + 1 = n - 1 by omega]
          exact List.Perm.refl _
        have hnot_perm : ¬ ∃ p, G.Perm (List.replicate (G.length - 1) 1 ++ [p]) := by
          rintro ⟨p, hp⟩
          have hsum_p := hp.sum_eq
          simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one,
            List.sum_cons, List.sum_nil, add_zero] at hsum_p
          have hpeq : p = n - 2 * h + 1 := by omega
          have hcs_eq : G.length - 1 = cs.length := by omega
          rw [hpeq, hcs_eq] at hp
          exact hperm hp
        have hgap := Test33638.list_fib_prod_gap G (by omega) (by rw [hGlen, hGsum, hdeq]; omega) hnot_perm
        rw [hGlen, hGsum, hdeq] at hgap
        have hmul := Nat.mul_le_mul_left (2 ^ h) hgap
        rw [mul_add, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add] at hmul
        rw [show h + (h - 2) = 2 * h - 2 by omega, show h + (h - 1) = 2 * h - 1 by omega,
          show n - h - h - 2 = n - 2 * h - 2 by omega,
          show n - h - h + 3 = n - 2 * h + 3 by omega] at hmul
        have hfib_gap : Nat.fib (n - 4) ≤ 2 ^ (2 * h - 2) * Nat.fib (n - 2 * h - 2) := by
          calc Nat.fib (n - 4)
              = Nat.fib ((n - 2 * h - 2) + (2 * h - 2)) := by congr 1; omega
            _ ≤ 2 ^ (2 * h - 2) * Nat.fib (n - 2 * h - 2) :=
                fib_add_le_pow_two_mul _ _ (by omega)
        rw [hS0R, hcard, hdeq, hLb]
        have hnat : 2 ^ h * (G.map (fun a => Nat.fib (a + 2))).prod + Nat.fib (n - 4) ≤
            2 ^ (2 * h - 1) * Nat.fib (n - 2 * h + 3) := by omega
        exact_mod_cast hnat

lemma S0_le_coord_with_gap_2m (m : ℕ) (hm : 5 ≤ m)
    (L : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hsplit : ∀ z ∈ L, Pivot33638.even (2 * m) z ∈ L) :
    ∃ R : Finset (Fin (2 * m)),
      R.card = Module.finrank (ZMod 2) L ∧
      Pivot33638.S0 (2 * m) (by omega) L ≤ Pivot33638.S0 (2 * m) (by omega) (Pivot33638.coordSub (2 * m) R) ∧
      ((∀ i ∈ R, i.val % 2 = 0) ∨ (∀ i ∈ R, i.val % 2 = 1) → L ≠ Pivot33638.coordSub (2 * m) R →
        ∃ Z : Finset (Fin (2 * m)), Z.card ≤ 6 ∧ ∃ z0 ∈ Z,
          ((Finset.univ.filter (fun x : Fin (2 * m) → ZMod 2 =>
            Pivot33638.ind (2 * m) (by omega) x ∧ ∀ i ∈ Z, x i = 0)).card : ℤ) ≤
          Pivot33638.S0 (2 * m) (by omega) (Pivot33638.coordSub (2 * m) R) -
            Pivot33638.S0 (2 * m) (by omega) L) := by
  obtain ⟨P, Q, _, hRcard, hSle, hgapQ, hgapP⟩ := Pivot33638.S0_le_coord_with_gap m (by omega) L hsplit
  set R : Finset (Fin (2 * m)) :=
    P.image (fun k => ⟨2 * k.val, by omega⟩) ∪ Q.image (fun k => ⟨2 * k.val + 1, by omega⟩)
  refine ⟨R, hRcard, hSle, ?_⟩
  intro hpar hne
  rcases hpar with hev | hod
  · have hQ0 : Q = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      have hmem : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * m)) ∈ R :=
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
      have := hev _ hmem
      dsimp at this; omega
    obtain ⟨j, hjP, r, hrP, hgap⟩ := hgapQ hQ0 hne
    have hjr : j ≠ r := fun h => hrP (h ▸ hjP)
    obtain ⟨Z, hZle, z0, hz0, hpin⟩ := Pivot33638.noncoord_gap_pinned m hm j r hjr
    refine ⟨Z, hZle, z0, hz0, le_trans (Nat.cast_le.mpr hpin) hgap⟩
  · have hP0 : P = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      have hmem : (⟨2 * k.val, by omega⟩ : Fin (2 * m)) ∈ R :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk)
      have := hod _ hmem
      dsimp at this; omega
    obtain ⟨j, hjQ, r, hrQ, hgap⟩ := hgapP hP0 hne
    have hjr : j ≠ r := fun h => hrQ (h ▸ hjQ)
    obtain ⟨Z, hZle, z0, hz0, hpin⟩ := Pivot33638.noncoord_gap_pinned m hm j r hjr
    refine ⟨Z, hZle, z0, hz0, le_trans (Nat.cast_le.mpr hpin) hgap⟩

lemma S0_le_coord_with_gap_6t (t : ℕ) (ht2 : 2 ≤ t)
    (L : Submodule (ZMod 2) (Fin (6 * t) → ZMod 2))
    (hsplit : ∀ z ∈ L, Pivot33638.even (6 * t) z ∈ L) :
    ∃ R : Finset (Fin (6 * t)),
      R.card = Module.finrank (ZMod 2) L ∧
      Pivot33638.S0 (6 * t) (by omega) L ≤ Pivot33638.S0 (6 * t) (by omega) (Pivot33638.coordSub (6 * t) R) ∧
      ((∀ i ∈ R, i.val % 2 = 0) ∨ (∀ i ∈ R, i.val % 2 = 1) → L ≠ Pivot33638.coordSub (6 * t) R →
        ∃ Z : Finset (Fin (6 * t)), Z.card ≤ 6 ∧ ∃ z0 ∈ Z,
          ((Finset.univ.filter (fun x : Fin (6 * t) → ZMod 2 =>
            Pivot33638.ind (6 * t) (by omega) x ∧ ∀ i ∈ Z, x i = 0)).card : ℤ) ≤
          Pivot33638.S0 (6 * t) (by omega) (Pivot33638.coordSub (6 * t) R) -
            Pivot33638.S0 (6 * t) (by omega) L) := by
  have haux : ∀ (n : ℕ) (hn : 0 < n), n = 2 * (3 * t) →
      ∀ (L : Submodule (ZMod 2) (Fin n → ZMod 2)),
      (∀ z ∈ L, Pivot33638.even n z ∈ L) →
      ∃ R : Finset (Fin n),
        R.card = Module.finrank (ZMod 2) L ∧
        Pivot33638.S0 n hn L ≤ Pivot33638.S0 n hn (Pivot33638.coordSub n R) ∧
        ((∀ i ∈ R, i.val % 2 = 0) ∨ (∀ i ∈ R, i.val % 2 = 1) → L ≠ Pivot33638.coordSub n R →
          ∃ Z : Finset (Fin n), Z.card ≤ 6 ∧ ∃ z0 ∈ Z,
            ((Finset.univ.filter (fun x : Fin n → ZMod 2 =>
              Pivot33638.ind n hn x ∧ ∀ i ∈ Z, x i = 0)).card : ℤ) ≤
            Pivot33638.S0 n hn (Pivot33638.coordSub n R) - Pivot33638.S0 n hn L) := by
    rintro _ hn rfl L hsplit
    exact S0_le_coord_with_gap_2m (3 * t) (by omega) L hsplit
  exact haux (6 * t) (by omega) (by omega) L hsplit

lemma pow_decay_margin (m : ℕ) (hm : 5 ≤ m) :
    (36 : ℤ) * (1458 : ℤ) ^ m < (15625 : ℤ) ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases eq_or_lt_of_le hm with h5 | hgt
    · have : m = 4 := by omega
      subst this; decide
    · have hih := ih (by omega)
      rw [pow_succ, pow_succ]
      nlinarith [pow_pos (show (0 : ℤ) < 1458 by norm_num) m]

lemma wt_le_card_of_coordSub (n : ℕ) (R : Finset (Fin n)) (z : Fin n → ZMod 2)
    (hz : z ∈ Pivot33638.coordSub n R) :
    Decay33638.wt n z ≤ R.card := by
  have hmem : ∀ i : Fin n, i ∉ R → z i = 0 :=
    (Pivot33638.mem_coordSub_iff n R z).mp hz
  have hsub : (Finset.univ.filter (fun i : Fin n => z i ≠ 0)) ⊆ R := by
    intro i hi
    by_contra hni
    exact (Finset.mem_filter.mp hi).2 (hmem i hni)
  have hwt_eq : Decay33638.wt n z = (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).card := by
    unfold Decay33638.wt; congr 1; ext i; simp
  rw [hwt_eq]
  exact Finset.card_le_card hsub

lemma D_block_disj_and_finrank (t : ℕ) (ht : 0 < t) (h : ℕ) (ht_big : 100 * (h + 4)^2 ≤ t) :
    checkSub (6 * t) ⊓ L_block (6 * t) (by omega) h = ⊥ ∧
    Module.finrank (ZMod 2) (D_block (6 * t) (by omega) h) = h + 4 := by
  have hn : 0 < 6 * t := by omega
  have h6 : 6 ∣ 6 * t := Dvd.intro t rfl
  have hdisj : checkSub (6 * t) ⊓ L_block (6 * t) hn h = ⊥ := by
    rw [eq_bot_iff]
    intro z ⟨hzc, hzl⟩
    by_contra hne
    have hge := Decay33638.check_wt_ge t ht z hzc hne
    have hle : Decay33638.wt (6 * t) z ≤ h := by
      calc Decay33638.wt (6 * t) z ≤ (R_block (6 * t) hn h).card :=
            wt_le_card_of_coordSub (6 * t) (R_block (6 * t) hn h) z hzl
        _ = h := R_block_card (6 * t) hn h (by nlinarith)
    nlinarith
  have hrank : Module.finrank (ZMod 2) (D_block (6 * t) hn h) = h + 4 := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (checkSub (6 * t)) (L_block (6 * t) hn h)
    rw [hdisj, finrank_bot, add_zero] at hsup
    have hcheck4 : Module.finrank (ZMod 2) (checkSub (6 * t)) = 4 :=
      checkSub_finrank_eq_four (6 * t) hn h6
    have hLrank : Module.finrank (ZMod 2) (L_block (6 * t) hn h) = h := by
      unfold L_block
      rw [Pivot33638.finrank_coordSub, R_block_card (6 * t) hn h (by nlinarith)]
    unfold D_block
    omega
  exact ⟨hdisj, hrank⟩

lemma S0_eq_filter_sum (n : ℕ) (hn : 0 < n) (M : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Test33638.S0 n hn M =
      ∑ z ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun z => z ∈ M), Test33638.tw0 n hn z := by
  unfold Test33638.S0
  congr 1
  ext z; simp

lemma heavy_sum_bound (t : ℕ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (ht_big : 100 * (h + 4)^2 ≤ t)
    (D L : Submodule (ZMod 2) (Fin (6 * t) → ZMod 2))
    (hLD : L ≤ D) (hfin : Module.finrank (ZMod 2) D ≤ h + 4)
    (hwt : ∀ z ∈ D, z ∉ L → 2 * t ≤ (h + 1) * Decay33638.wt (6 * t) z) :
    (15625 : ℤ) ^ (h + 4) * |Test33638.S0 (6 * t) (by omega) D - Test33638.S0 (6 * t) (by omega) L| ≤
      (1458 : ℤ) ^ (h + 4) * ((Finset.univ.filter (Test33638.ind (6 * t) (by omega))).card : ℤ) := by
  have hn : 0 < 6 * t := by omega
  let FD := (Finset.univ : Finset (Fin (6 * t) → ZMod 2)).filter (fun z => z ∈ D)
  let FL := (Finset.univ : Finset (Fin (6 * t) → ZMod 2)).filter (fun z => z ∈ L)
  have hFL_sub : FL ⊆ FD := fun z hz => by
    simp only [FD, FL, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hLD hz
  have hdiff : Test33638.S0 (6 * t) hn D - Test33638.S0 (6 * t) hn L =
      ∑ z ∈ FD \ FL, Test33638.tw0 (6 * t) hn z := by
    rw [S0_eq_filter_sum (6 * t) hn D, S0_eq_filter_sum (6 * t) hn L]
    have hs := Finset.sum_sdiff hFL_sub (f := Test33638.tw0 (6 * t) hn)
    linarith
  rw [hdiff]
  have hcard_sdiff : (FD \ FL).card ≤ 2 ^ (h + 4) := by
    calc (FD \ FL).card ≤ FD.card := Finset.card_le_card Finset.sdiff_subset
      _ = 2 ^ Module.finrank (ZMod 2) D := Pivot33638.card_submodule (6 * t) D
      _ ≤ 2 ^ (h + 4) := Nat.pow_le_pow_right (by omega) hfin
  have htri : |∑ z ∈ FD \ FL, Test33638.tw0 (6 * t) hn z| ≤
      ∑ z ∈ FD \ FL, |Test33638.tw0 (6 * t) hn z| := Finset.abs_sum_le_sum_abs _ _
  have hmul : (15625 : ℤ) ^ (h + 4) * |∑ z ∈ FD \ FL, Test33638.tw0 (6 * t) hn z| ≤
      ∑ z ∈ FD \ FL, (15625 : ℤ) ^ (h + 4) * |Test33638.tw0 (6 * t) hn z| := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left htri (by positivity)
  have hterm : ∀ z ∈ FD \ FL,
      (15625 : ℤ) ^ (h + 4) * |Test33638.tw0 (6 * t) hn z| ≤
        (729 : ℤ) ^ (h + 4) * ((Finset.univ.filter (Test33638.ind (6 * t) hn)).card : ℤ) := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    have hzD : z ∈ D := (Finset.mem_filter.mp hz.1).2
    have hzn : z ∉ L := fun hL => hz.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL⟩)
    have hbd := Decay33638.tw0_heavy_bound t ht h hh ht_big z (hwt z hzD hzn)
    have hcard_ind : (Finset.univ.filter (Decay33638.ind (6 * t) hn)).card =
        (Finset.univ.filter (Test33638.ind (6 * t) hn)).card := by
      congr 1; ext x; simp [Decay33638.ind, Test33638.ind, Decay33638.ix, Test33638.ix]
    change (15625 : ℤ) ^ (h + 4) * |Decay33638.tw0 (6 * t) hn z| ≤ _
    rw [← hcard_ind]
    exact hbd
  calc (15625 : ℤ) ^ (h + 4) * |∑ z ∈ FD \ FL, Test33638.tw0 (6 * t) hn z|
      ≤ ∑ z ∈ FD \ FL, (15625 : ℤ) ^ (h + 4) * |Test33638.tw0 (6 * t) hn z| := hmul
    _ ≤ ∑ _z ∈ FD \ FL, ((729 : ℤ) ^ (h + 4) * ((Finset.univ.filter (Test33638.ind (6 * t) hn)).card : ℤ)) :=
        Finset.sum_le_sum hterm
    _ = ((FD \ FL).card : ℤ) * ((729 : ℤ) ^ (h + 4) * ((Finset.univ.filter (Test33638.ind (6 * t) hn)).card : ℤ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 : ℤ) ^ (h + 4)) * ((729 : ℤ) ^ (h + 4) * ((Finset.univ.filter (Test33638.ind (6 * t) hn)).card : ℤ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hcard_sdiff
    _ = (1458 : ℤ) ^ (h + 4) * ((Finset.univ.filter (Test33638.ind (6 * t) hn)).card : ℤ) := by
        rw [← mul_assoc, ← mul_pow]; norm_num

lemma S0_le_S0_D_block (t : ℕ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (ht_big : 100 * (h + 4)^2 ≤ t)
    (D : Submodule (ZMod 2) (Fin (6 * t) → ZMod 2))
    (hbase : ∀ j, base (6 * t) j ∈ D) (heven : ∀ z ∈ D, even (6 * t) z ∈ D)
    (hfin : Module.finrank (ZMod 2) D ≤ h + 4) :
    Test33638.S0 (6 * t) (by omega) D ≤ Test33638.S0 (6 * t) (by omega) (D_block (6 * t) (by omega) h) := by
  have hn : 0 < 6 * t := by omega
  have h6 : 6 ∣ 6 * t := Dvd.intro t rfl
  have hcheck4 : Module.finrank (ZMod 2) (checkSub (6 * t)) = 4 :=
    checkSub_finrank_eq_four (6 * t) hn h6
  have hcheckD : checkSub (6 * t) ≤ D := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact hbase j
  let L := Decay33638.lightSpan t h D
  have hLD : L ≤ D := Decay33638.lightSpan_le t h D
  have hLsplit : ∀ z ∈ L, Pivot33638.even (6 * t) z ∈ L := Decay33638.lightSpan_split t h D heven
  have ⟨hLdisj, hLrank⟩ := Decay33638.lightSpan_disj_and_finrank t ht h D hbase hfin hcheck4
  obtain ⟨R, hRcard, hSle, hnoncoord⟩ := S0_le_coord_with_gap_6t t (by nlinarith) L hLsplit
  have hRle : R.card ≤ h := by rw [hRcard]; exact hLrank
  have finish_gap :
      Test33638.S0 (6 * t) hn L + (Nat.fib (6 * t - 4) : ℤ) ≤
        Test33638.S0 (6 * t) hn (L_block (6 * t) hn h) →
      Test33638.S0 (6 * t) hn D ≤ Test33638.S0 (6 * t) hn (D_block (6 * t) hn h) := by
    intro hgapL
    have hD_err := heavy_sum_bound t ht h hh ht_big D L hLD hfin
      (fun z hzD hzn => Decay33638.outside_lightSpan_wt t h D z hzD hzn)
    have ⟨_, hDb_rank⟩ := D_block_disj_and_finrank t ht h ht_big
    have hDb_err := heavy_sum_bound t ht h hh ht_big (D_block (6 * t) hn h) (L_block (6 * t) hn h)
      le_sup_right (by omega) (by
        intro z hzD hzn
        rw [D_block, Submodule.mem_sup] at hzD
        rcases hzD with ⟨c, hc, l, hl, rfl⟩
        have hcne : c ≠ 0 := by
          rintro rfl; rw [zero_add] at hzn; exact hzn hl
        have hwtc := Decay33638.check_wt_ge t ht c hc hcne
        have hwtl : Decay33638.wt (6 * t) l ≤ h := by
          calc Decay33638.wt (6 * t) l ≤ (R_block (6 * t) hn h).card :=
                wt_le_card_of_coordSub (6 * t) (R_block (6 * t) hn h) l hl
            _ = h := R_block_card (6 * t) hn h (by nlinarith)
        have htri : Decay33638.wt (6 * t) c ≤ Decay33638.wt (6 * t) (c + l) + Decay33638.wt (6 * t) l := by
          have hcl : c = (c + l) + l := by rw [add_assoc, fn_add_self, add_zero]
          conv_lhs => rw [hcl]
          exact Decay33638.wt_add_le (6 * t) (c + l) l
        nlinarith)
    have hluc := Test33638.indCard_eq_lucas (6 * t) (by nlinarith)
    have h18 := Test33638.lucas_le_18_fib (6 * t) (by nlinarith)
    have hind_le : ((Finset.univ.filter (Test33638.ind (6 * t) hn)).card : ℤ) ≤
        18 * (Nat.fib (6 * t - 4) : ℤ) := by
      have hnat : (Finset.univ.filter (Test33638.ind (6 * t) hn)).card ≤ 18 * Nat.fib (6 * t - 4) := by
        rw [hluc]; exact h18
      exact_mod_cast hnat
    have hmargin := pow_decay_margin (h + 4) (by omega)
    have hfib_pos : (0 : ℤ) < (Nat.fib (6 * t - 4) : ℤ) := by
      have hpos : 0 < Nat.fib (6 * t - 4) := Nat.fib_pos.mpr (by omega)
      exact_mod_cast hpos
    have hsum_err : (15625 : ℤ) ^ (h + 4) *
        (|Test33638.S0 (6 * t) hn D - Test33638.S0 (6 * t) hn L| +
         |Test33638.S0 (6 * t) hn (D_block (6 * t) hn h) - Test33638.S0 (6 * t) hn (L_block (6 * t) hn h)|) <
        (15625 : ℤ) ^ (h + 4) * (Nat.fib (6 * t - 4) : ℤ) := by
      calc (15625 : ℤ) ^ (h + 4) *
            (|Test33638.S0 (6 * t) hn D - Test33638.S0 (6 * t) hn L| +
             |Test33638.S0 (6 * t) hn (D_block (6 * t) hn h) - Test33638.S0 (6 * t) hn (L_block (6 * t) hn h)|)
          ≤ 2 * ((1458 : ℤ) ^ (h + 4) * ((Finset.univ.filter (Test33638.ind (6 * t) hn)).card : ℤ)) := by
            linarith
        _ ≤ 2 * ((1458 : ℤ) ^ (h + 4) * (18 * (Nat.fib (6 * t - 4) : ℤ))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hind_le (by positivity)) (by norm_num)
        _ = ((36 : ℤ) * (1458 : ℤ) ^ (h + 4)) * (Nat.fib (6 * t - 4) : ℤ) := by ring
        _ < (15625 : ℤ) ^ (h + 4) * (Nat.fib (6 * t - 4) : ℤ) :=
            mul_lt_mul_of_pos_right hmargin hfib_pos
    have herr_lt : |Test33638.S0 (6 * t) hn D - Test33638.S0 (6 * t) hn L| +
        |Test33638.S0 (6 * t) hn (D_block (6 * t) hn h) - Test33638.S0 (6 * t) hn (L_block (6 * t) hn h)| <
        (Nat.fib (6 * t - 4) : ℤ) :=
      lt_of_mul_lt_mul_left hsum_err (by positivity)
    have h1 := le_abs_self (Test33638.S0 (6 * t) hn D - Test33638.S0 (6 * t) hn L)
    have h2 := neg_le_abs (Test33638.S0 (6 * t) hn (D_block (6 * t) hn h) - Test33638.S0 (6 * t) hn (L_block (6 * t) hn h))
    linarith
  rcases S0_coord_block_or_gap (6 * t) hn h hh (by nlinarith) R hRle with ⟨hRh, s, hRblock⟩ | hgapR
  · have hR_sh : R = (R_block (6 * t) hn h).image
        (fun j => ix (6 * t) hn (j.val + 6 * t - (6 * t - s % (6 * t)) % (6 * t))) := by
      rw [hRblock]
      unfold R_block
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨ix (6 * t) hn (2 * j.val), ⟨j, rfl⟩, ?_⟩
        ext; simp only [ix]
        have hsm : s % (6 * t) < 6 * t := Nat.mod_lt s hn
        rcases Nat.eq_zero_or_pos (s % (6 * t)) with hs0 | hspos
        · rw [hs0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod]
          rw [Nat.add_mod, hs0, zero_add, Nat.mod_mod]
        · rw [Nat.mod_eq_of_lt (by omega : 6 * t - s % (6 * t) < 6 * t)]
          rw [show (2 * j.val) % (6 * t) + 6 * t - (6 * t - s % (6 * t)) =
            (2 * j.val) % (6 * t) + s % (6 * t) by omega]
          rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.add_mod, add_comm]
      · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
        refine ⟨j, ?_⟩
        ext; simp only [ix]
        have hsm : s % (6 * t) < 6 * t := Nat.mod_lt s hn
        rcases Nat.eq_zero_or_pos (s % (6 * t)) with hs0 | hspos
        · rw [hs0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod]
          rw [Nat.add_mod, hs0, zero_add, Nat.mod_mod]
        · rw [Nat.mod_eq_of_lt (by omega : 6 * t - s % (6 * t) < 6 * t)]
          rw [show (2 * j.val) % (6 * t) + 6 * t - (6 * t - s % (6 * t)) =
            (2 * j.val) % (6 * t) + s % (6 * t) by omega]
          rw [Nat.add_mod, add_comm]
    have hcoord_sh : Pivot33638.coordSub (6 * t) R =
        (L_block (6 * t) hn h).map (Decay33638.shL (6 * t) hn (6 * t - s % (6 * t))).toLinearMap := by
      rw [hR_sh]
      exact (coordSub_map_shL (6 * t) hn (6 * t - s % (6 * t)) (R_block (6 * t) hn h)).symm
    by_cases hLcoord : L = Pivot33638.coordSub (6 * t) R
    · have hsup_le : checkSub (6 * t) ⊔ L ≤ D := sup_le hcheckD hLD
      have hsup_rank : Module.finrank (ZMod 2) ↥(checkSub (6 * t) ⊔ L) = h + 4 := by
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq (checkSub (6 * t)) L
        have hinf : checkSub (6 * t) ⊓ L = ⊥ := by rw [inf_comm]; exact hLdisj
        rw [hinf, finrank_bot, add_zero] at h1
        have hLrank_eq : Module.finrank (ZMod 2) L = h := by rw [← hRcard, hRh]
        omega
      have hDeq : D = checkSub (6 * t) ⊔ L :=
        (Submodule.eq_of_le_of_finrank_le hsup_le (by omega)).symm
      have hDmap : (D_block (6 * t) hn h).map (Decay33638.shL (6 * t) hn (6 * t - s % (6 * t))).toLinearMap = D := by
        rw [hDeq, D_block, Submodule.map_sup]
        have hchk := Decay33638.sh_check t ht (6 * t - s % (6 * t))
        change (Submodule.span (ZMod 2) (Set.range (Decay33638.base (6 * t)))).map
            (Decay33638.shL (6 * t) hn (6 * t - s % (6 * t))).toLinearMap ⊔ _ = _
        rw [hchk, ← hcoord_sh, ← hLcoord]
        rfl
      have hS0eq : Test33638.S0 (6 * t) hn D = Test33638.S0 (6 * t) hn (D_block (6 * t) hn h) := by
        rw [← hDmap]
        exact Decay33638.sh_S0 (6 * t) hn (6 * t - s % (6 * t)) (D_block (6 * t) hn h)
      exact le_of_eq hS0eq
    · have hpar : (∀ i ∈ R, i.val % 2 = 0) ∨ (∀ i ∈ R, i.val % 2 = 1) := by
        rcases Nat.mod_two_eq_zero_or_one s with hs0 | hs1
        · left
          intro i hi
          rw [hRblock] at hi
          rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
          simp only [ix]
          have h2dvd : 2 ∣ 6 * t := ⟨3 * t, by omega⟩
          rw [Nat.mod_mod_of_dvd _ h2dvd]; omega
        · right
          intro i hi
          rw [hRblock] at hi
          rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
          simp only [ix]
          have h2dvd : 2 ∣ 6 * t := ⟨3 * t, by omega⟩
          rw [Nat.mod_mod_of_dvd _ h2dvd]; omega
      obtain ⟨Z, hZle, z0, hz0, hgapZ⟩ := hnoncoord hpar hLcoord
      have hfib_le := card_pinned_ge_fib_n_sub_4 (6 * t) (by nlinarith) Z hZle z0 hz0
      have hS0R_eq : Test33638.S0 (6 * t) hn (Pivot33638.coordSub (6 * t) R) =
          Test33638.S0 (6 * t) hn (L_block (6 * t) hn h) := by
        rw [hcoord_sh]
        exact Decay33638.sh_S0 (6 * t) hn (6 * t - s % (6 * t)) (L_block (6 * t) hn h)
      apply finish_gap
      have hfib_leZ : (Nat.fib (6 * t - 4) : ℤ) ≤
          ((Finset.univ.filter (fun x : Fin (6 * t) → ZMod 2 =>
            Pivot33638.ind (6 * t) hn x ∧ ∀ i ∈ Z, x i = 0)).card : ℤ) := by
        exact_mod_cast hfib_le
      have hgapL : Test33638.S0 (6 * t) hn L + (Nat.fib (6 * t - 4) : ℤ) ≤
          Test33638.S0 (6 * t) hn (Pivot33638.coordSub (6 * t) R) := by
        change Pivot33638.S0 (6 * t) hn L + _ ≤ Pivot33638.S0 (6 * t) hn (Pivot33638.coordSub (6 * t) R)
        linarith
      linarith
  · apply finish_gap
    have hSle' : Test33638.S0 (6 * t) hn L ≤ Test33638.S0 (6 * t) hn (Pivot33638.coordSub (6 * t) R) := hSle
    linarith

lemma ker_mix_card_eq (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    Nat.card {w : Fin n → ZMod 2 // mix n hn w = 0} = 2 ^ 4 := by
  have hoc := orth_card n (mixL n hn)
  rw [← h3_orth_eq_span n hn h6] at hoc
  have hcard_W : Nat.card (Fin n → ZMod 2) = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hcard_chk : Nat.card (Submodule.span (ZMod 2) (Set.range (base n))) = 2 ^ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
      Pivot33638.card_submodule n (Submodule.span (ZMod 2) (Set.range (base n)))]
    exact congrArg (2 ^ ·) (checkSub_finrank_eq_four n hn h6)
  rw [hcard_W, hcard_chk] at hoc
  exact (Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ n) hoc).symm

lemma block_lower_and_zeros (t : ℕ) (ht : 0 < t) (h : ℕ) (_hh : 1 ≤ h) (ht_big : 100 * (h + 4)^2 ≤ t)
    (name c : Fin (6 * t) → ZMod 2) :
    let hn : 0 < 6 * t := Nat.mul_pos (Nat.zero_lt_succ 5) ht
    let zeros := Nat.card {w : Fin (6 * t) → ZMod 2 //
      (∀ j : Fin h, mix (6 * t) hn w (ix (6 * t) hn (2 * j.val)) = 0) ∧
      (∀ i, mix (6 * t) hn w i * mix (6 * t) hn w (ix (6 * t) hn (i.val + 1)) = 0)}
    ((2 ^ h * zeros : ℕ) : ℤ) = Test33638.S0 (6 * t) hn (D_block (6 * t) hn h) ∧
    ∃ (ask : Fin h → ℕ → (Fin (6 * t) → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (A : ℕ → (Fin (6 * t) → ZMod 2) →ₗ[ZMod 2] (Fin (6 * t) → ZMod 2))
      (b : ℕ → (Fin (6 * t) → ZMod 2)),
      (∀ j p w, ask j p w = mix (6 * t) hn w (ix (6 * t) hn (2 * j.val))) ∧
      Nat.card {w : Fin (6 * t) → ZMod 2 //
        out (6 * t) hn name c w = A (run (6 * t) h ask w) w + b (run (6 * t) h ask w)} = 2 ^ h * zeros := by
  intro hn zeros
  have h6 : 6 ∣ 6 * t := Dvd.intro t rfl
  let v : Fin h → (Fin (6 * t) → ZMod 2) := fun j => Pivot33638.eVec (6 * t) (ix (6 * t) hn (2 * j.val))
  let φ : Fin h → (Fin (6 * t) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    fun j => (dotL (6 * t) (v j)).comp (mixL (6 * t) hn)
  have hφ_dot : ∀ j w, φ j w = dot (6 * t) (v j) (mix (6 * t) hn w) := by
    intro j w
    show dot (6 * t) (mix (6 * t) hn w) (v j) = dot (6 * t) (v j) (mix (6 * t) hn w)
    exact dot_comm (6 * t) _ _
  have hφ_eval : ∀ j w, φ j w = mix (6 * t) hn w (ix (6 * t) hn (2 * j.val)) := by
    intro j w
    rw [hφ_dot]
    unfold dot v Pivot33638.eVec
    rw [Finset.sum_eq_single (ix (6 * t) hn (2 * j.val))]
    · simp
    · intro i _ hne; simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  let K := LinearMap.ker (LinearMap.pi φ)
  let τ := (mixL (6 * t) hn).comp K.subtype
  have hspan_v : Submodule.span (ZMod 2) (Set.range v) = L_block (6 * t) hn h := by
    unfold L_block Pivot33638.coordSub R_block
    congr 1
    ext x
    simp [v]
  have horth : orth (6 * t) τ = D_block (6 * t) hn h := by
    refine h6_orth_eq (6 * t) hn h6 h (D_block (6 * t) hn h) ?_ v ?_ ?_ φ hφ_dot
    · intro j; exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)
    · intro j
      apply Submodule.mem_sup_right
      rw [← hspan_v]
      exact Submodule.subset_span ⟨j, rfl⟩
    · rw [hspan_v]; exact le_rfl
  have hcard_D : Nat.card (D_block (6 * t) hn h) = 2 ^ (h + 4) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Pivot33638.card_submodule (6 * t) (D_block (6 * t) hn h)]
    rw [(D_block_disj_and_finrank t ht h ht_big).2]
  have hker_τ : Nat.card {u : K // τ u = 0} = 2 ^ 4 := by
    have heq : Nat.card {u : K // τ u = 0} = Nat.card {w : Fin (6 * t) → ZMod 2 // mix (6 * t) hn w = 0} := by
      refine Nat.card_congr
        { toFun := fun u => ⟨u.1.1, u.2⟩
          invFun := fun w => ⟨⟨w.1, by
            rw [LinearMap.mem_ker]
            funext j
            show φ j w.1 = 0
            rw [hφ_eval, w.2]; rfl⟩, w.2⟩
          left_inv := fun u => rfl
          right_inv := fun w => rfl }
    rw [heq]
    exact ker_mix_card_eq (6 * t) hn h6
  have hKcard : Nat.card K * 2 ^ h = 2 ^ (6 * t) := by
    have hoc := orth_card (6 * t) τ
    rw [horth, hcard_D, hker_τ] at hoc
    have hpow : 2 ^ (h + 4) = 2 ^ h * 2 ^ 4 := by rw [pow_add]
    rw [hpow, ← mul_assoc] at hoc
    have h16 : 0 < 2 ^ 4 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right h16 hoc
  have hzeros_eq : Nat.card {u : K // adm (6 * t) hn (fun _ => true) (τ u)} = zeros := by
    refine Nat.card_congr
      { toFun := fun u => ⟨u.1.1, ?_, (adm_true_iff_ind (6 * t) hn _).mp u.2⟩
        invFun := fun w => ⟨⟨w.1, by
          rw [LinearMap.mem_ker]
          funext j
          show φ j w.1 = 0
          rw [hφ_eval]; exact w.2.1 j⟩, (adm_true_iff_ind (6 * t) hn _).mpr w.2.2⟩
        left_inv := fun u => rfl
        right_inv := fun w => rfl }
    intro j
    have hu := u.1.2
    rw [LinearMap.mem_ker] at hu
    have hj : φ j u.1.1 = 0 := congrFun hu j
    rwa [hφ_eval] at hj
  have hKpos : (0 : ℤ) < (Nat.card K : ℤ) := by exact_mod_cast Nat.card_pos (α := K)
  have hS0_eq : ((2 ^ h * zeros : ℕ) : ℤ) = Test33638.S0 (6 * t) hn (D_block (6 * t) hn h) := by
    have hF := fourier_count (6 * t) hn (fun _ => true) τ
    rw [horth, hzeros_eq, Ssum_true_eq_S0] at hF
    have hKcardZ : (Nat.card K : ℤ) * (2 : ℤ) ^ h = (2 : ℤ) ^ (6 * t) := by exact_mod_cast hKcard
    rw [← hKcardZ, mul_assoc] at hF
    have hEq := mul_left_cancel₀ hKpos.ne' hF
    push_cast
    exact hEq
  obtain ⟨A, b, hAb⟩ := nonadaptive_count (6 * t) hn h (fun _ => true) name c φ
  have hcard_out : Nat.card {w : Fin (6 * t) → ZMod 2 //
      out (6 * t) hn name c w = A (run (6 * t) h (fun j _ => φ j) w) w + b (run (6 * t) h (fun j _ => φ j) w)} =
      Nat.card {w : Fin (6 * t) → ZMod 2 // ∀ i, (fun _ => true) i = true →
        out (6 * t) hn name c w i = (A (run (6 * t) h (fun j _ => φ j) w) w + b (run (6 * t) h (fun j _ => φ j) w)) i} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    constructor
    · intro h i _; exact congrFun h i
    · intro h; funext i; exact h i rfl
  have hcount_eq : Nat.card {w : Fin (6 * t) → ZMod 2 //
      out (6 * t) hn name c w = A (run (6 * t) h (fun j _ => φ j) w) w + b (run (6 * t) h (fun j _ => φ j) w)} =
      2 ^ h * zeros := by
    rw [hcard_out]
    change Nat.card K * _ = 2 ^ (6 * t) * Nat.card {u : K // adm (6 * t) hn (fun _ => true) (τ u)} at hAb
    rw [hzeros_eq, ← hKcard, mul_assoc] at hAb
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K)) hAb
  exact ⟨hS0_eq, fun j _ => φ j, A, b, fun j _ w => hφ_eval j w, hcount_eq⟩

lemma final_33638 (t : ℕ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (ht_big : 100 * (h + 4)^2 ≤ t)
    (name c : Fin (6 * t) → ZMod 2) (fixed : Bool) (k : ℕ) :
    let hn : 0 < 6 * t := Nat.mul_pos (Nat.zero_lt_succ 5) ht
    let zeros := Nat.card {w : Fin (6 * t) → ZMod 2 //
      (∀ j : Fin h, mix (6 * t) hn w (ix (6 * t) hn (2 * j.val)) = 0) ∧
      (∀ i, mix (6 * t) hn w i * mix (6 * t) hn w (ix (6 * t) hn (i.val + 1)) = 0)}
    (∃ (ask : Fin h → ℕ → (Fin (6 * t) → ZMod 2) →ₗ[ZMod 2] ZMod 2)
       (A : ℕ → (Fin (6 * t) → ZMod 2) →ₗ[ZMod 2] (Fin (6 * t) → ZMod 2))
       (b : ℕ → (Fin (6 * t) → ZMod 2)),
      (fixed = true → ∀ j p w, ask j p w = mix (6 * t) hn w (ix (6 * t) hn (2 * j.val))) ∧
      k ≤ Nat.card {w : Fin (6 * t) → ZMod 2 //
        out (6 * t) hn name c w = A (run (6 * t) h ask w) w + b (run (6 * t) h ask w)}) ↔
      k ≤ 2 ^ h * zeros := by
  intro hn zeros
  have h6 : 6 ∣ 6 * t := Dvd.intro t rfl
  obtain ⟨hS0_zeros, ask0, A0, b0, hfix0, hcard0⟩ := block_lower_and_zeros t ht h hh ht_big name c
  constructor
  · rintro ⟨ask, A, b, -, hk⟩
    obtain ⟨D, hbase, heven, hfin, hup⟩ := upper (6 * t) hn h6 h (fun _ => true) name c ask A b
    have hcard_eq : Nat.card {w : Fin (6 * t) → ZMod 2 //
        out (6 * t) hn name c w = A (run (6 * t) h ask w) w + b (run (6 * t) h ask w)} =
        Nat.card {w : Fin (6 * t) → ZMod 2 // ∀ i, (fun _ => true) i = true →
          out (6 * t) hn name c w i = (A (run (6 * t) h ask w) w + b (run (6 * t) h ask w)) i} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
      constructor
      · intro h i _; exact congrFun h i
      · intro h; funext i; exact h i rfl
    rw [hcard_eq] at hk
    have hkZ : (k : ℤ) ≤ Ssum (6 * t) hn (fun _ => true) D :=
      le_trans (Nat.cast_le.mpr hk) hup
    rw [Ssum_true_eq_S0] at hkZ
    have hle := S0_le_S0_D_block t ht h hh ht_big D hbase heven hfin
    have htot : (k : ℤ) ≤ ((2 ^ h * zeros : ℕ) : ℤ) := by
      rw [hS0_zeros]; exact le_trans hkZ hle
    exact_mod_cast htot
  · intro hk
    refine ⟨ask0, A0, b0, fun _ => hfix0, ?_⟩
    rw [hcard0]; exact hk

end Assembly33638

end PEqualNP.Outside.L_meta_33638

theorem PEqualNP.Outside.L_meta_33638 : (∀ (t : ℕ) (ht : 0 < t) (h : ℕ), 1 ≤ h → 100*(h+4)^2 ≤ t →
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
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  let zeros := Nat.card {w : W //
    (∀ j : Fin h, mix w (ix (2*j.val)) = 0) ∧ (∀ i, mix w i * mix w (ix (i.val+1)) = 0)}
  ∀ (name c : W) (fixed : Bool) (k : ℕ),
    (∃ (ask : Fin h → ℕ → W →ₗ[F] F) (A : ℕ → W →ₗ[F] W) (b : ℕ → W),
      (fixed = true → ∀ j p w, ask j p w = mix w (ix (2*j.val))) ∧
      k ≤ Nat.card {w : W // out name c w = A (run ask w) w + b (run ask w)}) ↔ k ≤ 2^h*zeros) := by
  intro t ht h hh ht_big
  exact fun name c fixed k =>
    PEqualNP.Outside.L_meta_33638.Assembly33638.final_33638 t ht h hh ht_big name c fixed k

