import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity

namespace PEqualNP.Outside.L_meta_25572

private lemma z2_eq (a : ZMod 2) : a = 0 ∨ a = 1 := by
  rcases a with ⟨n, hn⟩
  match n, hn with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

private lemma z2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases z2_eq a with rfl | rfl <;> rfl

private lemma z2_add_eq_zero {a b : ZMod 2} : a + b = 0 ↔ a = b := by
  rcases z2_eq a with rfl | rfl <;> rcases z2_eq b with rfl | rfl <;> decide

private lemma z2_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 :=
  (z2_eq a).resolve_left h

private lemma z2_lin (a b c : ZMod 2) :
    a + (a + b) + (a + c) + (a + b + c) = 0 := by
  have h : a + (a + b) + (a + c) + (a + b + c) =
      (a + a) + (a + a) + (b + b) + (c + c) := by ac_rfl
  rw [h]
  simp only [z2_add_self, zero_add]

private lemma z2_mul_polar (a1 a2 b1 b2 c1 c2 : ZMod 2) :
    a1 * a2 + (a1 + b1) * (a2 + b2) + (a1 + c1) * (a2 + c2) +
      (a1 + b1 + c1) * (a2 + b2 + c2) = b1 * c2 + c1 * b2 := by
  have h : a1 * a2 + (a1 + b1) * (a2 + b2) + (a1 + c1) * (a2 + c2) +
      (a1 + b1 + c1) * (a2 + b2 + c2) =
      (a1 * a2 + a1 * a2) + (a1 * a2 + a1 * a2) +
      (a1 * b2 + a1 * b2) + (b1 * a2 + b1 * a2) + (b1 * b2 + b1 * b2) +
      (a1 * c2 + a1 * c2) + (c1 * a2 + c1 * a2) + (c1 * c2 + c1 * c2) +
      (b1 * c2 + c1 * b2) := by
    simp only [mul_add, add_mul]
    ac_rfl
  rw [h]
  simp only [z2_add_self, zero_add]

private lemma z2_polar (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ZMod 2) :
    (a0 + (1 + a1) * a2) + ((a0 + b0) + (1 + (a1 + b1)) * (a2 + b2)) +
    ((a0 + c0) + (1 + (a1 + c1)) * (a2 + c2)) +
    ((a0 + b0 + c0) + (1 + (a1 + b1 + c1)) * (a2 + b2 + c2)) =
    b1 * c2 + c1 * b2 := by
  have h : (a0 + (1 + a1) * a2) + ((a0 + b0) + (1 + (a1 + b1)) * (a2 + b2)) +
      ((a0 + c0) + (1 + (a1 + c1)) * (a2 + c2)) +
      ((a0 + b0 + c0) + (1 + (a1 + b1 + c1)) * (a2 + b2 + c2)) =
      (a0 + (a0 + b0) + (a0 + c0) + (a0 + b0 + c0)) +
      (a2 + (a2 + b2) + (a2 + c2) + (a2 + b2 + c2)) +
      (a1 * a2 + (a1 + b1) * (a2 + b2) + (a1 + c1) * (a2 + c2) +
        (a1 + b1 + c1) * (a2 + b2 + c2)) := by
    simp only [add_mul, one_mul]
    ac_rfl
  rw [h, z2_lin, z2_lin, z2_mul_polar, zero_add, zero_add]

private def atPos (k : Nat) (hk : 0 < k) (i : Nat) : Fin k :=
  ⟨i % k, Nat.mod_lt _ hk⟩

private lemma atPos_self {k : Nat} (hk : 0 < k) (i : Fin k) :
    atPos k hk i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

private lemma atPos_add_mod {k : Nat} (hk : 0 < k) (i m : Nat) :
    atPos k hk ((atPos k hk i).val + m) = atPos k hk (i + m) := by
  apply Fin.ext
  change (i % k + m) % k = (i + m) % k
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private lemma atPos_add_k {k : Nat} (hk : 0 < k) (i : Nat) :
    atPos k hk (i + k) = atPos k hk i :=
  Fin.ext (Nat.add_mod_right i k)

private lemma atPos_add_mul_k {k : Nat} (hk : 0 < k) (i m : Nat) :
    atPos k hk (i + k * m) = atPos k hk i :=
  Fin.ext (Nat.add_mul_mod_self_left i k m)

private lemma atPos_sub_add_comm {k : Nat} (hk : 0 < k) (i t : Fin k) (m : Nat) :
    atPos k hk ((atPos k hk (i.val + m)).val + k - t.val) =
      atPos k hk ((atPos k hk (i.val + k - t.val)).val + m) := by
  have ht : t.val ≤ k := Nat.le_of_lt t.isLt
  apply Fin.ext
  change ((i.val + m) % k + k - t.val) % k = ((i.val + k - t.val) % k + m) % k
  rw [Nat.add_sub_assoc ht, Nat.add_sub_assoc ht]
  rw [Nat.add_mod ((i.val + m) % k), Nat.mod_mod, ← Nat.add_mod]
  rw [Nat.add_mod ((i.val + (k - t.val)) % k), Nat.mod_mod, ← Nat.add_mod]
  rw [Nat.add_right_comm]

private lemma atPos_sub_symm {k : Nat} (hk : 0 < k) {j t r : Fin k}
    (h : atPos k hk (j.val + k - t.val) = r) :
    atPos k hk (j.val + k - r.val) = t := by
  have hval : (j.val + k - t.val) % k = r.val := congrArg Fin.val h
  apply Fin.ext
  change (j.val + k - r.val) % k = t.val
  by_cases hle : t.val ≤ j.val
  · have h1 : j.val + k - t.val = (j.val - t.val) + k := by omega
    have h2 : (j.val + k - t.val) % k = j.val - t.val := by
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hr : r.val = j.val - t.val := by omega
    have h3 : j.val + k - r.val = t.val + k := by omega
    rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt t.isLt]
  · have hlt : j.val + k - t.val < k := by omega
    have hr : r.val = j.val + k - t.val := by
      rw [Nat.mod_eq_of_lt hlt] at hval
      exact hval.symm
    have h3 : j.val + k - r.val = t.val := by omega
    rw [h3, Nat.mod_eq_of_lt t.isLt]

private lemma atPos_sub_iff {k : Nat} (hk : 0 < k) (j t r : Fin k) :
    atPos k hk (j.val + k - t.val) = r ↔ t = atPos k hk (j.val + k - r.val) :=
  ⟨fun h => (atPos_sub_symm hk h).symm, fun h => atPos_sub_symm hk h.symm⟩

private lemma atPos_neg_neg {k : Nat} (hk : 0 < k) (t : Fin k) :
    atPos k hk (k - (atPos k hk (k - t.val)).val) = t := by
  have h := atPos_sub_symm hk (j := ⟨0, hk⟩) (t := t) (r := atPos k hk (k - t.val))
    (by simp [atPos])
  simpa [atPos] using h

private lemma atPos_sub_add_cancel {k : Nat} (hk : 0 < k) (i t : Fin k) :
    atPos k hk ((atPos k hk (i.val + k - t.val)).val + t.val) = i := by
  rw [atPos_add_mod]
  have h1 : i.val + k - t.val + t.val = i.val + k := by omega
  rw [h1, atPos_add_k, atPos_self]

private lemma atPos_add_sub_cancel {k : Nat} (hk : 0 < k) (j t : Fin k) :
    atPos k hk ((atPos k hk (j.val + t.val)).val + k - t.val) = j := by
  apply Fin.ext
  change ((j.val + t.val) % k + k - t.val) % k = j.val
  rw [Nat.add_sub_assoc (Nat.le_of_lt t.isLt), Nat.add_mod ((j.val + t.val) % k),
    Nat.mod_mod, ← Nat.add_mod]
  have h1 : j.val + t.val + (k - t.val) = j.val + k := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

private lemma atPos_sub_neg {k : Nat} (hk : 0 < k) (i t : Fin k) :
    atPos k hk ((atPos k hk (i.val + k - t.val)).val + k - i.val) =
      atPos k hk (k - t.val) := by
  have hi : i.val ≤ k := Nat.le_of_lt i.isLt
  have ht : t.val ≤ k := Nat.le_of_lt t.isLt
  apply Fin.ext
  change ((i.val + k - t.val) % k + k - i.val) % k = (k - t.val) % k
  rw [Nat.add_sub_assoc hi, Nat.add_mod ((i.val + k - t.val) % k), Nat.mod_mod, ← Nat.add_mod]
  have h1 : i.val + k - t.val + (k - i.val) = (k - t.val) + k := by omega
  rw [h1, Nat.add_mod_right]

private lemma atPos_sub_sub_neg {k : Nat} (hk : 0 < k) (i t : Fin k) :
    atPos k hk ((atPos k hk (i.val + k - t.val)).val + k -
      (atPos k hk (k - t.val)).val) = i := by
  have hle : (atPos k hk (k - t.val)).val ≤ k := Nat.le_of_lt (atPos k hk (k - t.val)).isLt
  have h1 : atPos k hk ((atPos k hk (i.val + k - t.val)).val + k -
      (atPos k hk (k - t.val)).val) =
      atPos k hk ((atPos k hk (i.val + k - t.val)).val +
        (atPos k hk (k - (atPos k hk (k - t.val)).val)).val) := by
    apply Fin.ext
    change ((atPos k hk (i.val + k - t.val)).val + k - (atPos k hk (k - t.val)).val) % k =
      ((atPos k hk (i.val + k - t.val)).val + (k - (atPos k hk (k - t.val)).val) % k) % k
    rw [Nat.add_sub_assoc hle, Nat.add_mod _ ((k - _) % k), Nat.mod_mod, ← Nat.add_mod]
  rw [h1, atPos_neg_neg, atPos_sub_add_cancel]

private def shift (k : Nat) (hk : 0 < k) (m : Nat) (v : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  v (atPos k hk (i.val + m))

private def project (k : Nat) (hk : 0 < k) (p v : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  ∑ t : Fin k, p t * v (atPos k hk (i.val + k - t.val))

private def mix (k : Nat) (hk : 0 < k) (s : Nat) (v : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  v i + v (atPos k hk (i.val + s)) + v (atPos k hk (i.val + k - s % k))

private def B (k : Nat) (w f g : Fin k → ZMod 2) : ZMod 2 :=
  ∑ j : Fin k, w j * f j * g j

private lemma shift_zero {k : Nat} (hk : 0 < k) (v : Fin k → ZMod 2) :
    shift k hk 0 v = v := by
  funext i
  simp [shift, atPos_self]

private lemma shift_comp {k : Nat} (hk : 0 < k) (m n : Nat) (v : Fin k → ZMod 2) :
    shift k hk m (shift k hk n v) = shift k hk (m + n) v := by
  funext i
  simp only [shift, atPos_add_mod, Nat.add_assoc]

private lemma shift_add {k : Nat} (hk : 0 < k) (m : Nat) (u v : Fin k → ZMod 2) :
    shift k hk m (u + v) = shift k hk m u + shift k hk m v := rfl

private lemma shift_mul_k {k : Nat} (hk : 0 < k) (m : Nat) (v : Fin k → ZMod 2) :
    shift k hk (k * m) v = v := by
  funext i
  simp [shift, atPos_add_mul_k, atPos_self]

private lemma shift_inv_mod {k : Nat} (hk : 0 < k) (s : Nat) (v : Fin k → ZMod 2) :
    shift k hk (k - s % k) (shift k hk s v) = v := by
  rw [shift_comp]
  have h1 : k - s % k + s = k * (s / k + 1) := by
    have hdm := Nat.div_add_mod s k
    have hlt := Nat.mod_lt s hk
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [h1, shift_mul_k]

private lemma shift_inv_mod_right {k : Nat} (hk : 0 < k) (s : Nat) (v : Fin k → ZMod 2) :
    shift k hk s (shift k hk (k - s % k) v) = v := by
  rw [shift_comp, Nat.add_comm, ← shift_comp, shift_inv_mod]

private lemma shift_quad_comm {k : Nat} (hk : 0 < k) (s m : Nat) (T : Fin k → ZMod 2) :
    shift k hk m T + shift k hk s (shift k hk m T) +
      shift k hk (2 * s) (shift k hk m T) =
      shift k hk m (T + shift k hk s T + shift k hk (2 * s) T) := by
  rw [shift_add, shift_add, shift_comp, shift_comp, shift_comp, shift_comp,
    Nat.add_comm s m, Nat.add_comm (2 * s) m]

private lemma project_add {k : Nat} (hk : 0 < k) (p u v : Fin k → ZMod 2) :
    project k hk p (u + v) = project k hk p u + project k hk p v := by
  funext i
  simp only [project, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma shift_project {k : Nat} (hk : 0 < k) (m : Nat) (p v : Fin k → ZMod 2) :
    shift k hk m (project k hk p v) = project k hk p (shift k hk m v) := by
  funext i
  simp only [shift, project, atPos_sub_add_comm]

private lemma mix_add {k : Nat} (hk : 0 < k) (s : Nat) (u v : Fin k → ZMod 2) :
    mix k hk s (u + v) = mix k hk s u + mix k hk s v := by
  funext i
  simp only [mix, Pi.add_apply]
  ac_rfl

private lemma mix_eq_shifts {k : Nat} (hk : 0 < k) (s : Nat) (v : Fin k → ZMod 2) :
    mix k hk s v = v + shift k hk s v + shift k hk (k - s % k) v := by
  funext i
  have hle : s % k ≤ k := Nat.le_of_lt (Nat.mod_lt s hk)
  simp only [mix, shift, Pi.add_apply, Nat.add_sub_assoc hle]

private lemma mix_project {k : Nat} (hk : 0 < k) (s : Nat) (p v : Fin k → ZMod 2) :
    mix k hk s (project k hk p v) = project k hk p (mix k hk s v) := by
  rw [mix_eq_shifts, mix_eq_shifts, project_add, project_add, shift_project, shift_project]

private lemma sum_three_blocks (q : Nat) (f : Nat → ZMod 2) :
    (∑ m : Fin q, (f (3 * m.val) + f (3 * m.val + 1) + f (3 * m.val + 2))) =
      ∑ j : Fin (3 * q), f j.val := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have hcast : ∀ (n m : Nat), n = m →
        (∑ j : Fin n, f j.val) = ∑ j : Fin m, f j.val := by
      rintro n _ rfl; rfl
    rw [hcast (3 * (q + 1)) (3 * q + 1 + 1 + 1) (by omega),
      Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    ac_rfl

private lemma sum_shift_all_inv {k : Nat} (hk : 0 < k) (s : Nat) (v : Fin k → ZMod 2) :
    shift k hk s (fun i => ∑ j : Fin k, shift k hk (j.val * s) v i) =
      fun i => ∑ j : Fin k, shift k hk (j.val * s) v i := by
  funext i
  have h1 : shift k hk s (fun i => ∑ j : Fin k, shift k hk (j.val * s) v i) i =
      ∑ j : Fin k, shift k hk ((j.val + 1) * s) v i := by
    simp only [shift]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [atPos_add_mod]
    congr 1
    apply Fin.ext
    change (i.val + s + j.val * s) % k = (i.val + (j.val + 1) * s) % k
    have : i.val + s + j.val * s = i.val + (j.val + 1) * s := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [this]
  rw [h1]
  let f : Fin (k + 1) → ZMod 2 := fun j => shift k hk (j.val * s) v i
  have hs1 : ∑ j : Fin (k + 1), f j = f 0 + ∑ j : Fin k, f j.succ := Fin.sum_univ_succ f
  have hs2 : ∑ j : Fin (k + 1), f j = (∑ j : Fin k, f j.castSucc) + f (Fin.last k) :=
    Fin.sum_univ_castSucc f
  have h0k : f 0 = f (Fin.last k) := by
    change shift k hk (0 * s) v i = shift k hk (k * s) v i
    rw [Nat.zero_mul, shift_zero, shift_mul_k]
  have hcomb : f 0 + ∑ j : Fin k, f j.succ = f 0 + ∑ j : Fin k, f j.castSucc := by
    rw [← hs1, hs2, ← h0k, add_comm]
  exact add_left_cancel hcomb

private lemma mix_quad_step {k : Nat} (hk : 0 < k) (s : Nat) (w : Fin k → ZMod 2) :
    mix k hk s w = shift k hk (k - s % k) (w + shift k hk s w + shift k hk (2 * s) w) := by
  rw [mix_eq_shifts, shift_add, shift_add, shift_inv_mod]
  have h2 : shift k hk (k - s % k) (shift k hk (2 * s) w) = shift k hk s w := by
    have hsplit : 2 * s = s + s := by omega
    rw [hsplit, ← shift_comp, shift_inv_mod]
  rw [h2]
  funext i
  simp only [Pi.add_apply]
  ac_rfl

private lemma mix_surjective {k : Nat} (hk : 0 < k) (hk3 : k % 3 ≠ 0) (s : Nat)
    (y : Fin k → ZMod 2) : ∃ v : Fin k → ZMod 2, mix k hk s v = y := by
  let S : Fin k → ZMod 2 := fun i => ∑ j : Fin k, shift k hk (j.val * s) y i
  have hS1 : shift k hk s S = S := sum_shift_all_inv hk s y
  have hS2 : shift k hk (2 * s) S = S := by
    have hsplit : 2 * s = s + s := by omega
    rw [hsplit, ← shift_comp, hS1, hS1]
  have hS3 : S + shift k hk s S + shift k hk (2 * s) S = S := by
    rw [hS1, hS2]
    funext i
    simp only [Pi.add_apply, z2_add_self, zero_add]
  have hQ_step : ∀ (q : Nat),
      let Q : Fin k → ZMod 2 := fun i => ∑ m : Fin q, shift k hk (3 * m.val * s) y i
      Q + shift k hk s Q + shift k hk (2 * s) Q =
        fun i => ∑ j : Fin (3 * q), shift k hk (j.val * s) y i := by
    intro q
    funext i
    simp only [Pi.add_apply]
    have hq1 : shift k hk s (fun i => ∑ m : Fin q, shift k hk (3 * m.val * s) y i) i =
        ∑ m : Fin q, shift k hk ((3 * m.val + 1) * s) y i := by
      simp only [shift]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [atPos_add_mod]
      congr 1
      apply Fin.ext
      change (i.val + s + 3 * m.val * s) % k = (i.val + (3 * m.val + 1) * s) % k
      have : i.val + s + 3 * m.val * s = i.val + (3 * m.val + 1) * s := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [this]
    have hq2 : shift k hk (2 * s) (fun i => ∑ m : Fin q, shift k hk (3 * m.val * s) y i) i =
        ∑ m : Fin q, shift k hk ((3 * m.val + 2) * s) y i := by
      simp only [shift]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [atPos_add_mod]
      congr 1
      apply Fin.ext
      change (i.val + 2 * s + 3 * m.val * s) % k = (i.val + (3 * m.val + 2) * s) % k
      have : i.val + 2 * s + 3 * m.val * s = i.val + (3 * m.val + 2) * s := by
        rw [Nat.add_mul]
        omega
      rw [this]
    rw [hq1, hq2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact sum_three_blocks q (fun n => shift k hk (n * s) y i)
  have hmod : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · let q := k / 3
    have hkq : k = 3 * q + 1 := by omega
    let Q : Fin k → ZMod 2 := fun i => ∑ m : Fin q, shift k hk (3 * m.val * s) y i
    let T : Fin k → ZMod 2 := Q + S
    refine ⟨shift k hk (2 * s) T, ?_⟩
    rw [mix_quad_step, shift_quad_comm]
    have hT : T + shift k hk s T + shift k hk (2 * s) T = shift k hk (3 * q * s) y := by
      have hsplit : T + shift k hk s T + shift k hk (2 * s) T =
          (Q + shift k hk s Q + shift k hk (2 * s) Q) +
          (S + shift k hk s S + shift k hk (2 * s) S) := by
        funext i
        simp only [T, shift_add, Pi.add_apply]
        ac_rfl
      rw [hsplit, hQ_step q, hS3]
      funext i
      simp only [Pi.add_apply, S]
      have hS_eq : (∑ j : Fin k, shift k hk (j.val * s) y i) =
          (∑ j : Fin (3 * q), shift k hk (j.val * s) y i) +
            shift k hk (3 * q * s) y i := by
        have hcast : ∀ (n m : Nat) (hnm : n = m) (g : Nat → ZMod 2),
            (∑ j : Fin n, g j.val) = ∑ j : Fin m, g j.val := by
          rintro n _ rfl g; rfl
        rw [hcast k (3 * q + 1) hkq (fun n => shift k hk (n * s) y i), Fin.sum_univ_castSucc]
        rfl
      rw [hS_eq, ← add_assoc, z2_add_self, zero_add]
    rw [hT]
    have h2s : shift k hk (k - s % k) (shift k hk (2 * s) (shift k hk (3 * q * s) y)) = y := by
      have hsplit : 2 * s = s + s := by omega
      rw [hsplit, ← shift_comp, shift_inv_mod, shift_comp]
      have htot : s + 3 * q * s = k * s := by
        rw [hkq, Nat.add_mul, Nat.one_mul]
        omega
      rw [htot, shift_mul_k]
    exact h2s
  · let q := k / 3 + 1
    have hkq : 3 * q = k + 1 := by omega
    let Q : Fin k → ZMod 2 := fun i => ∑ m : Fin q, shift k hk (3 * m.val * s) y i
    let T : Fin k → ZMod 2 := Q + S
    refine ⟨shift k hk s T, ?_⟩
    rw [mix_quad_step, shift_quad_comm, shift_inv_mod]
    have hsplit : T + shift k hk s T + shift k hk (2 * s) T =
        (Q + shift k hk s Q + shift k hk (2 * s) Q) +
        (S + shift k hk s S + shift k hk (2 * s) S) := by
      funext i
      simp only [T, shift_add, Pi.add_apply]
      ac_rfl
    rw [hsplit, hQ_step q, hS3]
    funext i
    simp only [Pi.add_apply, S]
    have hQ_eq : (∑ j : Fin (3 * q), shift k hk (j.val * s) y i) =
        (∑ j : Fin k, shift k hk (j.val * s) y i) + y i := by
      have hcast : ∀ (n m : Nat) (hnm : n = m) (g : Nat → ZMod 2),
          (∑ j : Fin n, g j.val) = ∑ j : Fin m, g j.val := by
        rintro n _ rfl g; rfl
      rw [hcast (3 * q) (k + 1) hkq (fun n => shift k hk (n * s) y i), Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, shift_mul_k]
    rw [hQ_eq, add_right_comm, z2_add_self, zero_add]

private lemma B_symm {k : Nat} (w f g : Fin k → ZMod 2) :
    B k w f g = B k w g f := by
  simp only [B]
  refine Finset.sum_congr rfl fun j _ => ?_
  ac_rfl

private lemma B_add_right {k : Nat} (w f g1 g2 : Fin k → ZMod 2) :
    B k w f (g1 + g2) = B k w f g1 + B k w f g2 := by
  simp only [B, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma B_zero_right {k : Nat} (w f : Fin k → ZMod 2) :
    B k w f 0 = 0 := by
  simp [B]

private lemma B_project_left {k : Nat} (hk : 0 < k) (w p u v : Fin k → ZMod 2) :
    B k w (project k hk p u) v =
      ∑ t : Fin k, p t * B k w (shift k hk (k - t.val) u) v := by
  simp only [B, project, shift]
  have h1 : (∑ j : Fin k, w j * (∑ t : Fin k, p t * u (atPos k hk (j.val + k - t.val))) * v j) =
      ∑ j : Fin k, ∑ t : Fin k, p t * (w j * u (atPos k hk (j.val + (k - t.val))) * v j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Nat.add_sub_assoc (Nat.le_of_lt t.isLt)]
    ac_rfl
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]

private lemma B_project_right {k : Nat} (hk : 0 < k) (w p u v : Fin k → ZMod 2) :
    B k w u (project k hk p v) =
      ∑ t : Fin k, p t * B k w u (shift k hk (k - t.val) v) := by
  rw [B_symm, B_project_left]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [B_symm]

private lemma B_shift_pow {k : Nat} (hk : 0 < k) (w p : Fin k → ZMod 2)
    (h1 : ∀ a b : Fin k → ZMod 2,
      B k w (project k hk p a) (shift k hk 1 (b + project k hk p b)) =
        B k w (shift k hk 1 (project k hk p a)) (b + project k hk p b)) :
    ∀ (n : Nat) (a b : Fin k → ZMod 2),
      B k w (project k hk p a) (shift k hk n (b + project k hk p b)) =
        B k w (shift k hk n (project k hk p a)) (b + project k hk p b) := by
  intro n
  induction n with
  | zero =>
    intro a b
    simp [shift_zero]
  | succ n ih =>
    intro a b
    have hsn : shift k hk (n + 1) (b + project k hk p b) =
        shift k hk 1 (shift k hk n b + project k hk p (shift k hk n b)) := by
      rw [← shift_project, ← shift_add, shift_comp, Nat.add_comm]
    have hsp : shift k hk 1 (project k hk p a) = project k hk p (shift k hk 1 a) :=
      shift_project hk 1 p a
    have hsb : shift k hk n b + project k hk p (shift k hk n b) =
        shift k hk n (b + project k hk p b) := by
      rw [shift_add, shift_project]
    rw [hsn, h1 a (shift k hk n b), hsp, hsb, ih (shift k hk 1 a) b, ← shift_project, shift_comp]

private lemma B_ortho_of_shift {k : Nat} (hk : 0 < k) (w p : Fin k → ZMod 2)
    (hidem : ∀ v, project k hk p (project k hk p v) = project k hk p v)
    (h1 : ∀ a b : Fin k → ZMod 2,
      B k w (project k hk p a) (shift k hk 1 (b + project k hk p b)) =
        B k w (shift k hk 1 (project k hk p a)) (b + project k hk p b)) :
    ∀ a b : Fin k → ZMod 2, B k w (project k hk p a) (b + project k hk p b) = 0 := by
  intro a b
  have hpow := B_shift_pow hk w p h1
  have hpk : project k hk p (b + project k hk p b) = 0 := by
    rw [project_add, hidem]
    funext i
    exact z2_add_self _
  calc
    B k w (project k hk p a) (b + project k hk p b)
      = B k w (project k hk p (project k hk p a)) (b + project k hk p b) := by rw [hidem]
    _ = ∑ t : Fin k, p t * B k w (shift k hk (k - t.val) (project k hk p a))
          (b + project k hk p b) := B_project_left hk w p _ _
    _ = ∑ t : Fin k, p t * B k w (project k hk p a)
          (shift k hk (k - t.val) (b + project k hk p b)) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hpow (k - t.val) a b]
    _ = B k w (project k hk p a) (project k hk p (b + project k hk p b)) :=
          (B_project_right hk w p _ _).symm
    _ = 0 := by rw [hpk, B_zero_right]

private lemma B_self_adj_of_ortho {k : Nat} (hk : 0 < k) (w p : Fin k → ZMod 2)
    (hortho : ∀ a b : Fin k → ZMod 2, B k w (project k hk p a) (b + project k hk p b) = 0) :
    ∀ a b : Fin k → ZMod 2, B k w (project k hk p a) b = B k w a (project k hk p b) := by
  have heq : ∀ a b, B k w (project k hk p a) b = B k w (project k hk p a) (project k hk p b) := by
    intro a b
    have h := hortho a b
    rw [B_add_right] at h
    exact z2_add_eq_zero.mp h
  intro a b
  rw [heq a b, B_symm, ← heq b a, B_symm]

private def delta (k : Nat) (r : Fin k) (x : Fin k) : ZMod 2 :=
  if x = r then 1 else 0

private lemma project_delta {k : Nat} (hk : 0 < k) (p : Fin k → ZMod 2) (r j : Fin k) :
    project k hk p (delta k r) j = p (atPos k hk (j.val + k - r.val)) := by
  simp only [project, delta]
  have h : (∑ t : Fin k, p t * (if atPos k hk (j.val + k - t.val) = r then 1 else 0)) =
      ∑ t : Fin k, if t = atPos k hk (j.val + k - r.val) then p t else 0 := by
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [atPos_sub_iff hk j t r]
    split_ifs <;> simp
  rw [h, Finset.sum_ite_eq']
  simp

private lemma B_delta_right {k : Nat} (w f : Fin k → ZMod 2) (i : Fin k) :
    B k w f (delta k i) = w i * f i := by
  simp only [B, delta]
  have h : (∑ j : Fin k, w j * f j * (if j = i then 1 else 0)) =
      ∑ j : Fin k, if j = i then w j * f j else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [h, Finset.sum_ite_eq']
  simp

private lemma coord_eq_of_self_adj {k : Nat} (hk : 0 < k) (w p : Fin k → ZMod 2)
    (hsa : ∀ a b : Fin k → ZMod 2, B k w (project k hk p a) b = B k w a (project k hk p b)) :
    ∀ i t : Fin k, w i * p t = w (atPos k hk (i.val + k - t.val)) * p (atPos k hk (k - t.val)) := by
  intro i t
  let r := atPos k hk (i.val + k - t.val)
  have h := hsa (delta k r) (delta k i)
  rw [B_delta_right, B_symm, B_delta_right, project_delta, project_delta] at h
  have h1 : atPos k hk (i.val + k - r.val) = t := atPos_sub_symm hk rfl
  have h2 : atPos k hk (r.val + k - i.val) = atPos k hk (k - t.val) := atPos_sub_neg hk i t
  rw [h1, h2] at h
  exact h

private lemma self_adj_of_coord_eq {k : Nat} (hk : 0 < k) (w p : Fin k → ZMod 2)
    (hc : ∀ i t : Fin k,
      w i * p t = w (atPos k hk (i.val + k - t.val)) * p (atPos k hk (k - t.val))) :
    ∀ a b : Fin k → ZMod 2, B k w (project k hk p a) b = B k w a (project k hk p b) := by
  intro a b
  have hL : B k w (project k hk p a) b =
      ∑ x : Fin k × Fin k,
        (w x.1 * p x.2) * a (atPos k hk (x.1.val + k - x.2.val)) * b x.1 := by
    simp only [B, project, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    ac_rfl
  have hR : B k w a (project k hk p b) =
      ∑ x : Fin k × Fin k,
        (w x.1 * p x.2) * a x.1 * b (atPos k hk (x.1.val + k - x.2.val)) := by
    simp only [B, project, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ac_rfl
  rw [hL, hR]
  let φ : Fin k × Fin k → Fin k × Fin k := fun x =>
    (atPos k hk (x.1.val + k - x.2.val), atPos k hk (k - x.2.val))
  have hinv : ∀ x : Fin k × Fin k, φ (φ x) = x := by
    rintro ⟨j, t⟩
    exact Prod.ext (atPos_sub_sub_neg hk j t) (atPos_neg_neg hk t)
  refine Fintype.sum_equiv
    { toFun := φ, invFun := φ, left_inv := hinv, right_inv := hinv } _ _ ?_
  rintro ⟨j, t⟩
  dsimp only [Equiv.coe_fn_mk, φ]
  rw [hc j t, atPos_sub_sub_neg hk j t]

private def IsPeriod (k : Nat) (hk : 0 < k) (w : Fin k → ZMod 2) (d : Nat) : Prop :=
  ∀ j : Fin k, w (atPos k hk (j.val + d)) = w j

private lemma isPeriod_zero {k : Nat} (hk : 0 < k) (w : Fin k → ZMod 2) :
    IsPeriod k hk w 0 := by
  intro j
  simp [atPos_self]

private lemma isPeriod_k {k : Nat} (hk : 0 < k) (w : Fin k → ZMod 2) :
    IsPeriod k hk w k := by
  intro j
  rw [atPos_add_k, atPos_self]

private lemma isPeriod_add {k : Nat} (hk : 0 < k) {w : Fin k → ZMod 2} {a b : Nat}
    (ha : IsPeriod k hk w a) (hb : IsPeriod k hk w b) :
    IsPeriod k hk w (a + b) := by
  intro j
  rw [← Nat.add_assoc, ← atPos_add_mod, hb, ha]

private lemma isPeriod_mul {k : Nat} (hk : 0 < k) {w : Fin k → ZMod 2} {a : Nat}
    (ha : IsPeriod k hk w a) (m : Nat) :
    IsPeriod k hk w (a * m) := by
  induction m with
  | zero =>
    rw [Nat.mul_zero]
    exact isPeriod_zero hk w
  | succ m ih =>
    rw [Nat.mul_succ]
    exact isPeriod_add hk ih ha

private lemma isPeriod_sub {k : Nat} (hk : 0 < k) {w : Fin k → ZMod 2} {a b : Nat}
    (ha : IsPeriod k hk w a) (hb : IsPeriod k hk w b) (hle : a ≤ b) :
    IsPeriod k hk w (b - a) := by
  intro j
  have h1 := ha (atPos k hk (j.val + (b - a)))
  rw [atPos_add_mod, Nat.add_assoc, Nat.sub_add_cancel hle, hb] at h1
  exact h1.symm

private lemma isPeriod_mod {k : Nat} (hk : 0 < k) {w : Fin k → ZMod 2} {a b : Nat}
    (ha : IsPeriod k hk w a) (hb : IsPeriod k hk w b) :
    IsPeriod k hk w (a % b) := by
  have hdm := Nat.div_add_mod a b
  have hle : b * (a / b) ≤ a := by omega
  have heq : a % b = a - b * (a / b) := by omega
  rw [heq]
  exact isPeriod_sub hk (isPeriod_mul hk hb (a / b)) ha hle

private lemma isPeriod_gcd {k : Nat} (hk : 0 < k) {w : Fin k → ZMod 2} :
    ∀ a b : Nat, IsPeriod k hk w a → IsPeriod k hk w b → IsPeriod k hk w (Nat.gcd a b) := by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro b ha hb
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simpa using hb
    · rw [Nat.gcd_rec]
      exact ih (b % a) (Nat.mod_lt b hpos) a (isPeriod_mod hk hb ha) ha

private lemma isPeriod_finset_gcd {k : Nat} (hk : 0 < k) {w : Fin k → ZMod 2}
    (S : Finset (Fin k)) (f : Fin k → Nat)
    (hf : ∀ t ∈ S, IsPeriod k hk w (f t)) :
    IsPeriod k hk w (S.gcd f) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.gcd_empty]
    exact isPeriod_zero hk w
  | insert a s _ ih =>
    rw [Finset.gcd_insert]
    exact isPeriod_gcd hk (f a) (s.gcd f)
      (hf a (Finset.mem_insert_self a s))
      (ih fun t ht => hf t (Finset.mem_insert_of_mem ht))

private lemma isPeriod_of_dvd {k : Nat} (hk : 0 < k) {w : Fin k → ZMod 2} {d n : Nat}
    (hdvd : d ∣ n) (hd : IsPeriod k hk w d) :
    IsPeriod k hk w n := by
  rcases hdvd with ⟨m, rfl⟩
  exact isPeriod_mul hk hd m

private def outputFn (k : Nat) (hk : 0 < k) (s : Nat) (v : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  let y := mix k hk s v
  y i + (1 + y (atPos k hk (i.val + 1))) * y (atPos k hk (i.val + 2))

private lemma polarization_sum {k : Nat} (hk : 0 < k) (s : Nat) (x mask u v : Fin k → ZMod 2) :
    (∑ j : Fin k, mask j *
      (outputFn k hk s x j + outputFn k hk s (x + u) j +
        outputFn k hk s (x + v) j + outputFn k hk s (x + u + v) j)) =
      B k mask (shift k hk 1 (mix k hk s u)) (shift k hk 2 (mix k hk s v)) +
      B k mask (shift k hk 2 (mix k hk s u)) (shift k hk 1 (mix k hk s v)) := by
  have hterm : ∀ j : Fin k,
      outputFn k hk s x j + outputFn k hk s (x + u) j +
        outputFn k hk s (x + v) j + outputFn k hk s (x + u + v) j =
      shift k hk 1 (mix k hk s u) j * shift k hk 2 (mix k hk s v) j +
      shift k hk 2 (mix k hk s u) j * shift k hk 1 (mix k hk s v) j := by
    intro j
    dsimp only [outputFn, shift]
    rw [mix_add, mix_add, mix_add, mix_add]
    simp only [Pi.add_apply]
    have hp := z2_polar
      (mix k hk s x j)
      (mix k hk s x (atPos k hk (j.val + 1)))
      (mix k hk s x (atPos k hk (j.val + 2)))
      (mix k hk s u j)
      (mix k hk s u (atPos k hk (j.val + 1)))
      (mix k hk s u (atPos k hk (j.val + 2)))
      (mix k hk s v j)
      (mix k hk s v (atPos k hk (j.val + 1)))
      (mix k hk s v (atPos k hk (j.val + 2)))
    rw [hp]
    ac_rfl
  simp only [hterm, mul_add, Finset.sum_add_distrib, B]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ac_rfl

private lemma main (k : Nat) (hk : 0 < k) (hk3 : k % 3 ≠ 0) (p : Fin k → ZMod 2)
    (hidem : ∀ v, project k hk p (project k hk p v) = project k hk p v)
    (s : Nat) (x mask : Fin k → ZMod 2) :
    (∀ a b : Fin k → ZMod 2,
      let u := project k hk p a
      let v := b + project k hk p b
      (∑ j : Fin k, mask j *
        (outputFn k hk s x j + outputFn k hk s (x + u) j +
          outputFn k hk s (x + v) j + outputFn k hk s (x + u + v) j)) = 0) ↔
    mask = 0 ∨ ((∀ t : Fin k, p t = p (atPos k hk (k - t.val))) ∧
      ∀ j : Fin k, mask (atPos k hk (j.val + Nat.gcd k ((Finset.univ : Finset (Fin k)).gcd
        (fun t => if p t = 0 then 0 else t.val)))) = mask j) := by
  let stride := Nat.gcd k ((Finset.univ : Finset (Fin k)).gcd
    (fun t => if p t = 0 then 0 else t.val))
  let symmetric := ∀ t : Fin k, p t = p (atPos k hk (k - t.val))
  constructor
  · intro hadd
    have hshift1 : ∀ a b : Fin k → ZMod 2,
        B k mask (project k hk p a) (shift k hk 1 (b + project k hk p b)) =
        B k mask (shift k hk 1 (project k hk p a)) (b + project k hk p b) := by
      intro a' b'
      obtain ⟨a, ha⟩ := mix_surjective hk hk3 s (shift k hk (k - 1 % k) a')
      obtain ⟨b, hb⟩ := mix_surjective hk hk3 s (shift k hk (k - 1 % k) b')
      have h0 := hadd a b
      dsimp only at h0
      rw [polarization_sum hk s x mask] at h0
      have hu : shift k hk 1 (mix k hk s (project k hk p a)) = project k hk p a' := by
        rw [mix_project, ha, ← shift_project, shift_inv_mod_right]
      have hv : shift k hk 1 (mix k hk s (b + project k hk p b)) = b' + project k hk p b' := by
        rw [mix_add, mix_project, hb, shift_add, ← shift_project,
          shift_inv_mod_right, shift_inv_mod_right]
      have hu2 : shift k hk 2 (mix k hk s (project k hk p a)) =
          shift k hk 1 (project k hk p a') := by
        rw [← hu, shift_comp]
      have hv2 : shift k hk 2 (mix k hk s (b + project k hk p b)) =
          shift k hk 1 (b' + project k hk p b') := by
        rw [← hv, shift_comp]
      rw [hu, hv, hu2, hv2] at h0
      exact z2_add_eq_zero.mp h0
    have hortho := B_ortho_of_shift hk mask p hidem hshift1
    have hsa := B_self_adj_of_ortho hk mask p hortho
    have hc := coord_eq_of_self_adj hk mask p hsa
    by_cases hsym : symmetric
    · right
      refine ⟨hsym, ?_⟩
      have hper_t : ∀ t : Fin k, IsPeriod k hk mask (if p t = 0 then 0 else t.val) := by
        intro t
        by_cases hpt : p t = 0
        · simp only [hpt, ↓reduceIte]
          exact isPeriod_zero hk mask
        · simp only [hpt, ↓reduceIte]
          have hpt1 : p t = 1 := z2_ne_zero hpt
          have hptn1 : p (atPos k hk (k - t.val)) = 1 := by
            rw [← hsym t, hpt1]
          intro j
          let i := atPos k hk (j.val + t.val)
          have hci := hc i t
          rw [hpt1, hptn1, mul_one, mul_one, atPos_add_sub_cancel hk j t] at hci
          exact hci
      exact isPeriod_gcd hk k _ (isPeriod_k hk mask)
        (isPeriod_finset_gcd hk Finset.univ _ fun t _ => hper_t t)
    · left
      have hne : ∃ t : Fin k, p t ≠ p (atPos k hk (k - t.val)) := by
        by_contra hall
        apply hsym
        intro t
        by_contra hnt
        exact hall ⟨t, hnt⟩
      rcases hne with ⟨t, hnt⟩
      funext j
      rcases z2_eq (p t) with hpt0 | hpt1
      · have hptn1 : p (atPos k hk (k - t.val)) = 1 :=
          z2_ne_zero (by rw [hpt0] at hnt; exact hnt.symm)
        let i := atPos k hk (j.val + t.val)
        have hci := hc i t
        rw [hpt0, hptn1, mul_zero, mul_one, atPos_add_sub_cancel hk j t] at hci
        exact hci.symm
      · have hptn0 : p (atPos k hk (k - t.val)) = 0 := by
          rcases z2_eq (p (atPos k hk (k - t.val))) with h0 | h1
          · exact h0
          · exact absurd (hpt1.trans h1.symm) hnt
        have hcj := hc j t
        rw [hpt1, hptn0, mul_one, mul_zero] at hcj
        exact hcj
  · rintro (rfl | ⟨hsym, hper⟩)
    · intro a b
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    · have hc : ∀ i t : Fin k,
          mask i * p t =
            mask (atPos k hk (i.val + k - t.val)) * p (atPos k hk (k - t.val)) := by
        intro i t
        by_cases hpt : p t = 0
        · have hptn : p (atPos k hk (k - t.val)) = 0 := by
            rw [← hsym t, hpt]
          rw [hpt, hptn, mul_zero, mul_zero]
        · have hdvd1 : stride ∣ (Finset.univ : Finset (Fin k)).gcd
              (fun t => if p t = 0 then 0 else t.val) := Nat.gcd_dvd_right _ _
          have hdvd2 : (Finset.univ : Finset (Fin k)).gcd
              (fun t => if p t = 0 then 0 else t.val) ∣ (if p t = 0 then 0 else t.val) :=
            Finset.gcd_dvd (Finset.mem_univ t)
          have hdvd : stride ∣ t.val := by
            have h3 := Nat.dvd_trans hdvd1 hdvd2
            simpa only [hpt, ↓reduceIte] using h3
          have hpt_per : IsPeriod k hk mask t.val := isPeriod_of_dvd hk hdvd hper
          have hm : mask (atPos k hk (i.val + k - t.val)) = mask i := by
            have h1 := hpt_per (atPos k hk (i.val + k - t.val))
            rw [atPos_sub_add_cancel] at h1
            exact h1.symm
          rw [hm, ← hsym t]
      have hsa := self_adj_of_coord_eq hk mask p hc
      have hortho : ∀ a b : Fin k → ZMod 2,
          B k mask (project k hk p a) (b + project k hk p b) = 0 := by
        intro a b
        rw [B_add_right, ← hsa, hidem]
        exact z2_add_self _
      intro a b
      dsimp only
      rw [polarization_sum hk s x mask]
      have hu1 : shift k hk 1 (mix k hk s (project k hk p a)) =
          project k hk p (shift k hk 1 (mix k hk s a)) := by
        rw [mix_project, shift_project]
      have hu2 : shift k hk 2 (mix k hk s (project k hk p a)) =
          project k hk p (shift k hk 2 (mix k hk s a)) := by
        rw [mix_project, shift_project]
      have hv1 : shift k hk 1 (mix k hk s (b + project k hk p b)) =
          shift k hk 1 (mix k hk s b) + project k hk p (shift k hk 1 (mix k hk s b)) := by
        rw [mix_add, mix_project, shift_add, shift_project]
      have hv2 : shift k hk 2 (mix k hk s (b + project k hk p b)) =
          shift k hk 2 (mix k hk s b) + project k hk p (shift k hk 2 (mix k hk s b)) := by
        rw [mix_add, mix_project, shift_add, shift_project]
      rw [hu1, hu2, hv1, hv2, hortho, hortho, zero_add]

end PEqualNP.Outside.L_meta_25572

theorem PEqualNP.Outside.L_meta_25572 : ∀ (k : Nat) (hk : 0 < k), Odd k → k % 3 ≠ 0 →
  let atPos := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let word := Fin k → ZMod 2
  ∀ (p : word),
    let project := fun (v : word) (i : Fin k) =>
      ∑ t : Fin k, p t * v (atPos (i.val + k - t.val))
    (∀ v : word, project (project v) = project v) →
    let stride := Nat.gcd k ((Finset.univ : Finset (Fin k)).gcd
      (fun t => if p t = 0 then 0 else t.val))
    let symmetric := ∀ t : Fin k, p t = p (atPos (k - t.val))
    ∀ (s : Nat), (s = 1 ∨ s = 2) →
    let mix := fun (v : word) (i : Fin k) =>
      v i + v (atPos (i.val + s)) + v (atPos (i.val + k - s % k))
    let output := fun (v : word) (i : Fin k) =>
      let y := mix v
      y i + (1 + y (atPos (i.val + 1))) * y (atPos (i.val + 2))
    ∀ x mask : word,
      (∀ a b : word,
        let u := project a
        let v := b + project b
        (∑ j : Fin k, mask j *
          (output x j + output (x + u) j + output (x + v) j +
            output (x + u + v) j)) = 0) ↔
      mask = 0 ∨ (symmetric ∧
        ∀ j : Fin k, mask (atPos (j.val + stride)) = mask j) := by
  intro k hk _hkOdd hk3 _ _ p _ hidem _ _ s _hs _ _ x mask
  exact PEqualNP.Outside.L_meta_25572.main k hk hk3 p hidem s x mask
