import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33688_aux

lemma testBit_eq_of_div_mod_eq {n m k : Nat} (h : (n / 2 ^ k) % 2 = (m / 2 ^ k) % 2) :
    n.testBit k = m.testBit k := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.and_comm 1, Nat.and_comm 1, Nat.and_one_is_mod, Nat.and_one_is_mod, h]

lemma testBit_eq_false_of_div_mod_zero {n k : Nat} (h : (n / 2 ^ k) % 2 = 0) :
    n.testBit k = false := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.and_comm 1, Nat.and_one_is_mod, h]
  rfl

lemma nat_add_eq_xor_of_dvd_two_pow {d x y : Nat} (hx : 2 ^ d ∣ x) (hy : y < 2 ^ d) :
    x + y = x ^^^ y := by
  obtain ⟨q, rfl⟩ := hx
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor]
  by_cases hk : k < d
  · have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hd : 2 ^ d = 2 ^ k * (2 * 2 ^ (d - k - 1)) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]
      congr 1
      omega
    have hxdiv : (2 ^ d * q) / 2 ^ k = 2 * (2 ^ (d - k - 1) * q) := by
      rw [hd, show 2 ^ k * (2 * 2 ^ (d - k - 1)) * q = 2 ^ k * (2 * (2 ^ (d - k - 1) * q)) by ring]
      exact Nat.mul_div_right _ hpos
    have hxydiv : (2 ^ d * q + y) / 2 ^ k = 2 * (2 ^ (d - k - 1) * q) + y / 2 ^ k := by
      rw [hd, show 2 ^ k * (2 * 2 ^ (d - k - 1)) * q = 2 ^ k * (2 * (2 ^ (d - k - 1) * q)) by ring]
      exact Nat.mul_add_div hpos _ _
    have hxbit : (2 ^ d * q).testBit k = false := by
      apply testBit_eq_false_of_div_mod_zero
      rw [hxdiv]
      exact Nat.mul_mod_right 2 _
    have hxybit : (2 ^ d * q + y).testBit k = y.testBit k := by
      apply testBit_eq_of_div_mod_eq
      rw [hxydiv]
      exact Nat.mul_add_mod 2 _ _
    rw [hxbit, hxybit, Bool.false_xor]
  · have hle : d ≤ k := by omega
    have hkpow : 2 ^ k = 2 ^ d * 2 ^ (k - d) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hy_lt : y < 2 ^ k :=
      lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hle)
    have hybit : y.testBit k = false := Nat.testBit_lt_two_pow hy_lt
    have hxydiv : (2 ^ d * q + y) / 2 ^ k = (2 ^ d * q) / 2 ^ k := by
      rw [hkpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      rw [Nat.mul_add_div (Nat.two_pow_pos d), Nat.div_eq_of_lt hy, Nat.add_zero]
      rw [Nat.mul_div_right _ (Nat.two_pow_pos d)]
    have hxybit : (2 ^ d * q + y).testBit k = (2 ^ d * q).testBit k := by
      apply testBit_eq_of_div_mod_eq
      rw [hxydiv]
    rw [hybit, hxybit, Bool.xor_false]

def packBits (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if f n then packBits f n ^^^ 2 ^ n else packBits f n

lemma packBits_lt (f : Nat → Bool) : ∀ n, packBits f n < 2 ^ n
  | 0 => by simp [packBits]
  | n + 1 => by
    have ih := packBits_lt f n
    have h1 : packBits f n < 2 ^ (n + 1) :=
      lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    simp only [packBits]
    split_ifs
    · exact Nat.xor_lt_two_pow h1 h2
    · exact h1

lemma packBits_testBit (f : Nat → Bool) :
    ∀ n t, (packBits f n).testBit t = (decide (t < n) && f t)
  | 0, t => by simp [packBits]
  | n + 1, t => by
    have ih := packBits_testBit f n t
    by_cases hlt : t < n
    · have hne : n ≠ t := by omega
      simp only [packBits]
      split_ifs
      · rw [Nat.testBit_xor, Nat.testBit_two_pow, ih]
        simp [hlt, hne, show t < n + 1 by omega]
      · rw [ih]
        simp [hlt, show t < n + 1 by omega]
    · by_cases heq : t = n
      · subst heq
        have h0 : (packBits f t).testBit t = false := Nat.testBit_lt_two_pow (packBits_lt f t)
        simp only [packBits]
        split_ifs with hf
        · rw [Nat.testBit_xor, Nat.testBit_two_pow, h0]
          simp [hf]
        · rw [h0]
          simp [hf]
      · have hgt : n + 1 ≤ t := by omega
        have hlt2 : packBits f (n + 1) < 2 ^ t :=
          lt_of_lt_of_le (packBits_lt f (n + 1)) (Nat.pow_le_pow_right (by decide) hgt)
        rw [Nat.testBit_lt_two_pow hlt2]
        have hnot : ¬ (t < n + 1) := by omega
        simp [hnot]

lemma packBits_testBit_of_lt {f : Nat → Bool} {n t : Nat} (ht : t < n) :
    (packBits f n).testBit t = f t := by
  rw [packBits_testBit, decide_eq_true ht, Bool.true_and]

lemma eq_of_testBit_lt {n z z' : Nat} (hz : z < 2 ^ n) (hz' : z' < 2 ^ n)
    (h : ∀ t < n, z.testBit t = z'.testBit t) : z = z' := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < n
  · exact h t ht
  · have h1 : z.testBit t = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide) (by omega)))
    have h2 : z'.testBit t = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hz' (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [h1, h2]

lemma sum_ite_two_pow_eq_packBits (f : Nat → Bool) :
    ∀ n, (∑ j ∈ Finset.range n, if f j then 2 ^ j else 0) = packBits f n
  | 0 => by simp [packBits]
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_ite_two_pow_eq_packBits f n]
    simp only [packBits]
    split_ifs
    · rw [Nat.add_comm, nat_add_eq_xor_of_dvd_two_pow (dvd_refl _) (packBits_lt f n), Nat.xor_comm]
    · simp

def maskFn (top r : Nat) : Nat := ∑ i ∈ Finset.range (r + 1), 2 ^ (top - 2 * i)

lemma two_pow_dvd_maskFn (top : Nat) : ∀ r, 2 ^ (top - 2 * r) ∣ maskFn top r
  | 0 => by simp [maskFn]
  | r + 1 => by
    unfold maskFn
    rw [Finset.sum_range_succ]
    apply dvd_add
    · exact dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (two_pow_dvd_maskFn top r)
    · exact dvd_refl _

lemma maskFn_succ_eq_xor (top r : Nat) (h : 2 * (r + 1) ≤ top) :
    maskFn top (r + 1) = maskFn top r ^^^ 2 ^ (top - 2 * (r + 1)) := by
  unfold maskFn
  rw [Finset.sum_range_succ]
  exact nat_add_eq_xor_of_dvd_two_pow (two_pow_dvd_maskFn top r)
    (Nat.pow_lt_pow_right (by decide) (by omega))

lemma maskFn_lt (top : Nat) : ∀ r, 2 * r ≤ top → maskFn top r < 2 ^ (top + 1)
  | 0, _ => by
    simp only [maskFn, Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.mul_zero, Nat.sub_zero]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  | r + 1, h => by
    rw [maskFn_succ_eq_xor top r h]
    exact Nat.xor_lt_two_pow (maskFn_lt top r (by omega))
      (Nat.pow_lt_pow_right (by decide) (by omega))

lemma maskFn_testBit (top : Nat) :
    ∀ r, 2 * r ≤ top → ∀ k, (maskFn top r).testBit k = decide (∃ i ≤ r, k = top - 2 * i)
  | 0, _, k => by
    simp only [maskFn, Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.mul_zero, Nat.sub_zero,
      Nat.testBit_two_pow]
    by_cases hk : top = k
    · subst hk
      rw [decide_eq_true rfl, decide_eq_true ⟨0, le_refl 0, by omega⟩]
    · rw [decide_eq_false hk, decide_eq_false]
      rintro ⟨i, hi, heq⟩
      omega
  | r + 1, h, k => by
    rw [maskFn_succ_eq_xor top r h, Nat.testBit_xor, maskFn_testBit top r (by omega) k,
      Nat.testBit_two_pow]
    by_cases hP : ∃ i ≤ r, k = top - 2 * i
    · by_cases hQ : top - 2 * (r + 1) = k
      · obtain ⟨i, hi, heq⟩ := hP
        omega
      · rw [decide_eq_true hP, decide_eq_false hQ, Bool.xor_false, decide_eq_true]
        obtain ⟨i, hi, heq⟩ := hP
        exact ⟨i, by omega, heq⟩
    · by_cases hQ : top - 2 * (r + 1) = k
      · rw [decide_eq_false hP, decide_eq_true hQ, Bool.false_xor, decide_eq_true]
        exact ⟨r + 1, le_refl _, hQ.symm⟩
      · rw [decide_eq_false hP, decide_eq_false hQ, Bool.false_xor, decide_eq_false]
        rintro ⟨i, hi, heq⟩
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · exact hQ heq.symm
        · exact hP ⟨i, by omega, heq⟩

def sol (z : ℕ → Bool) (h : ℕ) (a b : Bool) : ℕ → Bool
  | 0 => b
  | 1 => a
  | (i + 2) => xor (z (h - 1 - i)) (!(sol z h a b (i + 1)) && sol z h a b i)

theorem sol2 (z : ℕ → Bool) (h : ℕ) (a b : Bool) (i : ℕ) :
    sol z h a b (i + 2) = xor (z (h - 1 - i)) (!(sol z h a b (i + 1)) && sol z h a b i) := by
  rw [sol]

def G (z : ℕ → Bool) (h : ℕ) (V : ℕ → Bool) : Prop :=
  ∀ i < h, V (i + 2) = xor (z (h - 1 - i)) (!(V (i + 1)) && V i)

theorem G_iff (z : ℕ → Bool) (h : ℕ) (V : ℕ → Bool) :
    G z h V ↔ ∀ i < h + 2, V i = sol z h (V 1) (V 0) i := by
  constructor
  · intro hG
    have key : ∀ n, n + 1 < h + 2 →
        V n = sol z h (V 1) (V 0) n ∧ V (n + 1) = sol z h (V 1) (V 0) (n + 1) := by
      intro n
      induction n with
      | zero => intro _; exact ⟨rfl, rfl⟩
      | succ n ih =>
        intro hn
        obtain ⟨h1, h2⟩ := ih (by omega)
        refine ⟨h2, ?_⟩
        rw [sol2, hG n (by omega), ← h1, ← h2]
    intro i hi
    rcases i with _ | i
    · rfl
    · exact (key i (by omega)).2
  · intro hs i hi
    rw [hs (i + 2) (by omega), hs (i + 1) (by omega), hs i (by omega), sol2]

theorem headSpec (P : ℕ → Bool) : ∀ n a : ℕ,
    a ≤ ((List.range' a n).filter P).headD (a + n) ∧
    ((List.range' a n).filter P).headD (a + n) ≤ a + n ∧
    (∀ t, a ≤ t → t < ((List.range' a n).filter P).headD (a + n) → P t = false) ∧
    (((List.range' a n).filter P).headD (a + n) < a + n →
      P (((List.range' a n).filter P).headD (a + n)) = true) := by
  intro n
  induction n with
  | zero =>
    intro a
    simp only [List.range'_zero, List.filter_nil, List.headD_nil]
    exact ⟨by omega, by omega, fun t h1 h2 => by omega, fun h => by omega⟩
  | succ n ih =>
    intro a
    rw [List.range'_succ]
    by_cases hp : P a = true
    · rw [List.filter_cons_of_pos hp]
      simp only [List.headD_cons]
      refine ⟨le_refl _, by omega, fun t h1 h2 => by omega, fun _ => hp⟩
    · rw [List.filter_cons_of_neg hp]
      obtain ⟨i1, i2, i3, i4⟩ := ih (a + 1)
      rw [show a + 1 + n = a + (n + 1) by omega] at i1 i2 i3 i4
      refine ⟨by omega, i2, ?_, i4⟩
      intro t h1 h2
      by_cases e : t = a
      · subst e; simpa using hp
      · exact i3 t (by omega) h2

def stopF (z : ℕ → Bool) (h lane : ℕ) : ℕ :=
  ((List.range ((h - lane) / 2)).filter (fun t => z (h - 1 - lane - 2 * t))).headD ((h - lane) / 2)

theorem stopSpec (z : ℕ → Bool) (h lane : ℕ) :
    stopF z h lane ≤ (h - lane) / 2 ∧
    (∀ t < stopF z h lane, z (h - 1 - lane - 2 * t) = false) ∧
    (stopF z h lane < (h - lane) / 2 → z (h - 1 - lane - 2 * stopF z h lane) = true) := by
  have := headSpec (fun t => z (h - 1 - lane - 2 * t)) ((h - lane) / 2) 0
  simp only [Nat.zero_add, ← List.range_eq_range'] at this
  obtain ⟨_, i2, i3, i4⟩ := this
  exact ⟨i2, fun t ht => i3 t (Nat.zero_le _) ht, i4⟩

theorem sol0 (z : ℕ → Bool) (h : ℕ) (a b : Bool) : sol z h a b 0 = b := rfl
theorem sol1 (z : ℕ → Bool) (h : ℕ) (a b : Bool) : sol z h a b 1 = a := rfl
theorem solTwo (z : ℕ → Bool) (h : ℕ) (a b : Bool) :
    sol z h a b 2 = xor (z (h - 1)) (!a && b) := rfl

theorem sameFrom (z : ℕ → Bool) (h : ℕ) (a b a' b' : Bool) (j : ℕ)
    (h0 : sol z h a b j = sol z h a' b' j) (h1 : sol z h a b (j + 1) = sol z h a' b' (j + 1)) :
    ∀ n, sol z h a b (j + n) = sol z h a' b' (j + n) ∧
      sol z h a b (j + n + 1) = sol z h a' b' (j + n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ n ih =>
    obtain ⟨i1, i2⟩ := ih
    refine ⟨i2, ?_⟩
    rw [show j + (n + 1) + 1 = (j + n) + 2 by omega, sol2, sol2, i1, i2]

theorem F3 (z : ℕ → Bool) (h : ℕ) (i : ℕ) (hi : 1 ≤ i) :
    sol z h true true i = sol z h true false i := by
  have := sameFrom z h true true true false 1 rfl (by rw [solTwo, solTwo]; simp) (i - 1)
  rw [show 1 + (i - 1) = i by omega] at this
  exact this.1

def Apat (s i : ℕ) : Bool := decide (i % 2 = 1 ∧ i / 2 ≤ s)
def Cpat (s i : ℕ) : Bool := decide (i % 2 = 0 ∧ 2 ≤ i ∧ i / 2 ≤ s + 1)

theorem F1 (z : ℕ → Bool) (h : ℕ) (i : ℕ) (hi : i < h + 2) :
    xor (sol z h true false i) (sol z h false false i) = Apat (stopF z h 0) i := by
  obtain ⟨sle, sfalse, strue⟩ := stopSpec z h 0
  set s := stopF z h 0 with hs
  have inv : ∀ t, t ≤ s → sol z h true false (2 * t) = false ∧ sol z h false false (2 * t) = false ∧
      sol z h true false (2 * t + 1) = !(sol z h false false (2 * t + 1)) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨rfl, rfl, rfl⟩
    | succ t ih =>
      intro ht
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      have zf : z (h - 1 - 2 * t) = false := by
        have := sfalse t (by omega); simpa using this
      have e2 : ∀ a : Bool, sol z h a false (2 * (t + 1)) = false := by
        intro a
        rw [show 2 * (t + 1) = 2 * t + 2 by ring, sol2, zf]
        cases a
        · rw [i2]; simp
        · rw [i1]; simp
      refine ⟨e2 true, e2 false, ?_⟩
      rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by ring, sol2 z h true false (2 * t + 1),
        sol2 z h false false (2 * t + 1), show 2 * t + 1 + 1 = 2 * (t + 1) by ring, e2, e2, i3]
      simp
  obtain ⟨j0, j1, j2⟩ := inv s (le_refl _)
  have m2 : sol z h true false (2 * s + 2) = sol z h false false (2 * s + 2) := by
    rw [sol2, sol2, j0, j1]; simp
  rcases Nat.lt_or_ge i (2 * s + 2) with hlt | hge
  · obtain ⟨t, ht | ht⟩ : ∃ t, i = 2 * t ∨ i = 2 * t + 1 := ⟨i / 2, by omega⟩
    · subst ht
      obtain ⟨k1, k2, _⟩ := inv t (by omega)
      rw [k1, k2, Apat, decide_eq_false (by omega)]; rfl
    · subst ht
      obtain ⟨_, _, k3⟩ := inv t (by omega)
      rw [k3, Apat, decide_eq_true (by omega)]; simp
  · rw [Apat, decide_eq_false (by omega)]
    rcases Nat.eq_or_lt_of_le hge with e | hgt
    · rw [← e, m2]; simp
    · have hsm : s < h / 2 := by omega
      have zt : z (h - 1 - 2 * s) = true := by
        have := strue hsm; simpa using this
      have m3 : sol z h true false (2 * s + 2 + 1) = sol z h false false (2 * s + 2 + 1) := by
        rw [sol2, sol2, sol2, sol2, j0, j1, zt]; simp
      have := (sameFrom z h true false false false (2 * s + 2) m2 m3 (i - (2 * s + 2))).1
      rw [show 2 * s + 2 + (i - (2 * s + 2)) = i by omega] at this
      rw [this]; simp

theorem F2 (z : ℕ → Bool) (h : ℕ) (i : ℕ) (hi : i < h + 2) :
    xor (sol z h false true i) (sol z h false false i) =
      xor (decide (i = 0)) (Cpat (stopF z h 1) i) := by
  obtain ⟨sle, sfalse, strue⟩ := stopSpec z h 1
  set s := stopF z h 1 with hs
  have inv : ∀ t, t ≤ s → sol z h false true (2 * t + 1) = false ∧
      sol z h false false (2 * t + 1) = false ∧
      sol z h false true (2 * t + 2) = !(sol z h false false (2 * t + 2)) := by
    intro t
    induction t with
    | zero => intro _; refine ⟨rfl, rfl, ?_⟩; rw [solTwo, solTwo]; simp
    | succ t ih =>
      intro ht
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      have zf : z (h - 1 - (2 * t + 1)) = false := by
        have := sfalse t (by omega)
        rw [show h - 1 - 1 - 2 * t = h - 1 - (2 * t + 1) by omega] at this; exact this
      have e2 : ∀ b : Bool, sol z h false b (2 * (t + 1) + 1) = false := by
        intro b
        rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by ring, sol2, zf]
        cases b
        · rw [i2]; simp
        · rw [i1]; simp
      refine ⟨e2 true, e2 false, ?_⟩
      rw [show 2 * (t + 1) + 2 = (2 * t + 2) + 2 by ring, sol2 z h false true (2 * t + 2),
        sol2 z h false false (2 * t + 2), show 2 * t + 2 + 1 = 2 * (t + 1) + 1 by ring, e2, e2, i3]
      simp
  obtain ⟨j0, j1, j2⟩ := inv s (le_refl _)
  have m3 : sol z h false true (2 * s + 3) = sol z h false false (2 * s + 3) := by
    rw [show 2 * s + 3 = (2 * s + 1) + 2 by ring, sol2 z h false true (2 * s + 1),
      sol2 z h false false (2 * s + 1), j0, j1]; simp
  rcases Nat.lt_or_ge i (2 * s + 3) with hlt | hge
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [sol0, sol0]; simp [Cpat]
    obtain ⟨t, ht | ht⟩ : ∃ t, i = 2 * t + 1 ∨ i = 2 * t + 2 := ⟨(i - 1) / 2, by omega⟩
    · subst ht
      obtain ⟨k1, k2, _⟩ := inv t (by omega)
      rw [k1, k2, Cpat, decide_eq_false (show ¬ (2 * t + 1 = 0) by omega),
        decide_eq_false (show ¬ ((2 * t + 1) % 2 = 0 ∧ 2 ≤ 2 * t + 1 ∧ (2 * t + 1) / 2 ≤ s + 1) by omega)]
    · subst ht
      obtain ⟨_, _, k3⟩ := inv t (by omega)
      rw [k3, Cpat, decide_eq_false (show ¬ (2 * t + 2 = 0) by omega),
        decide_eq_true (show ((2 * t + 2) % 2 = 0 ∧ 2 ≤ 2 * t + 2 ∧ (2 * t + 2) / 2 ≤ s + 1) by omega)]; simp
  · rw [Cpat, decide_eq_false (show ¬ (i = 0) by omega),
      decide_eq_false (show ¬ (i % 2 = 0 ∧ 2 ≤ i ∧ i / 2 ≤ s + 1) by omega)]
    rcases Nat.eq_or_lt_of_le hge with e | hgt
    · rw [← e, m3]; simp
    · have hsm : s < (h - 1) / 2 := by omega
      have zt : z (h - 1 - (2 * s + 1)) = true := by
        have := strue hsm
        rw [show h - 1 - 1 - 2 * s = h - 1 - (2 * s + 1) by omega] at this; exact this
      have m4 : sol z h false true (2 * s + 3 + 1) = sol z h false false (2 * s + 3 + 1) := by
        rw [show 2 * s + 3 + 1 = (2 * s + 2) + 2 by ring, sol2 z h false true (2 * s + 2),
          sol2 z h false false (2 * s + 2), show 2 * s + 2 + 1 = (2 * s + 1) + 2 by ring,
          sol2 z h false true (2 * s + 1), sol2 z h false false (2 * s + 1), j0, j1, zt]; simp
      have := (sameFrom z h false true false false (2 * s + 3) m3 m4 (i - (2 * s + 3))).1
      rw [show 2 * s + 3 + (i - (2 * s + 3)) = i by omega] at this
      rw [this]; simp

def Dpat (a b : Bool) (s0 s1 i : ℕ) : Bool :=
  xor (xor (a && Apat s0 i) (b && decide (i = 0))) (b && !a && Cpat s1 i)

theorem Dform (z : ℕ → Bool) (h : ℕ) (a b : Bool) (i : ℕ) (hi : i < h + 2) :
    xor (sol z h a b i) (sol z h false false i) = Dpat a b (stopF z h 0) (stopF z h 1) i := by
  cases a <;> cases b
  · simp [Dpat]
  · rw [F2 z h i hi]; simp [Dpat]
  · rw [F1 z h i hi]; simp [Dpat]
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; rw [sol0, sol0]; simp [Dpat, Apat]
    · rw [F3 z h i hpos, F1 z h i hi]; simp [Dpat, show i ≠ 0 by omega]

def bitFn (u j : Nat) : Bool :=
  xor (u.testBit j) (!(u.testBit (j + 1)) && u.testBit (j + 2))

def replyFn (h u : Nat) : Nat :=
  ∑ j ∈ Finset.range h, if bitFn u j then 2 ^ j else 0

def fiberFn (h z : Nat) : Finset Nat :=
  (Finset.range (2 ^ (h + 2))).filter (fun u => replyFn h u = z)

def distFn (Q : List (Nat × Nat)) (u v : Nat) : Nat :=
  (Q.filter (fun p => bitFn (u ^^^ p.1) p.2 != bitFn (v ^^^ p.1) p.2)).length

def wtFn (Q : List (Nat × Nat)) (v : Nat) : Nat :=
  (Q.filter (fun p => xor
    (v.testBit (p.2 + 1) && p.1.testBit (p.2 + 2))
    (v.testBit (p.2 + 2) && p.1.testBit (p.2 + 1)))).length

def mkElem (z h : Nat) (a b : Bool) : Nat :=
  packBits (fun k => sol (fun j => z.testBit j) h a b (h + 1 - k)) (h + 2)

lemma mkElem_lt (z h : Nat) (a b : Bool) : mkElem z h a b < 2 ^ (h + 2) :=
  packBits_lt _ (h + 2)

lemma mkElem_testBit {z h k : Nat} (a b : Bool) (hk : k < h + 2) :
    (mkElem z h a b).testBit k = sol (fun j => z.testBit j) h a b (h + 1 - k) :=
  packBits_testBit_of_lt hk

lemma mkElem_inj {z h : Nat} {a b a' b' : Bool} (heq : mkElem z h a b = mkElem z h a' b') :
    a = a' ∧ b = b' := by
  have ha := congrArg (fun x => x.testBit h) heq
  have hb := congrArg (fun x => x.testBit (h + 1)) heq
  rw [mkElem_testBit a b (by omega), mkElem_testBit a' b' (by omega),
      show h + 1 - h = 1 by omega, sol1, sol1] at ha
  rw [mkElem_testBit a b (by omega), mkElem_testBit a' b' (by omega),
      show h + 1 - (h + 1) = 0 by omega, sol0, sol0] at hb
  exact ⟨ha, hb⟩

lemma replyFn_eq_iff {h z u : Nat} (hz : z < 2 ^ h) :
    replyFn h u = z ↔ ∀ j < h, bitFn u j = z.testBit j := by
  unfold replyFn
  rw [sum_ite_two_pow_eq_packBits (bitFn u) h]
  constructor
  · intro hrep j hj
    rw [← hrep, packBits_testBit_of_lt hj]
  · intro hbit
    apply eq_of_testBit_lt (packBits_lt _ h) hz
    intro j hj
    rw [packBits_testBit_of_lt hj, hbit j hj]

lemma bool_eq_xor_of_xor_eq {x y w : Bool} (h : xor x y = w) : x = xor w y := by
  cases x <;> cases y <;> cases w <;> simp_all

lemma mem_fiberFn_iff {h z u : Nat} (hz : z < 2 ^ h) :
    u ∈ fiberFn h z ↔ ∃ a b : Bool, u = mkElem z h a b := by
  unfold fiberFn
  rw [Finset.mem_filter, Finset.mem_range, replyFn_eq_iff hz]
  constructor
  · rintro ⟨hu_lt, hbit⟩
    let V : Nat → Bool := fun i => u.testBit (h + 1 - i)
    have hG : G (fun j => z.testBit j) h V := by
      intro i hi
      have hb := hbit (h - 1 - i) (by omega)
      unfold bitFn at hb
      dsimp only [V]
      rw [show h + 1 - (i + 2) = h - 1 - i by omega,
          show h + 1 - (i + 1) = h - 1 - i + 1 by omega,
          show h + 1 - i = h - 1 - i + 2 by omega]
      exact bool_eq_xor_of_xor_eq hb
    have hsol := (G_iff (fun j => z.testBit j) h V).mp hG
    refine ⟨V 1, V 0, ?_⟩
    apply eq_of_testBit_lt hu_lt (mkElem_lt z h (V 1) (V 0))
    intro k hk
    rw [mkElem_testBit (V 1) (V 0) hk, ← hsol (h + 1 - k) (by omega)]
    dsimp only [V]
    rw [show h + 1 - (h + 1 - k) = k by omega]
  · rintro ⟨a, b, rfl⟩
    refine ⟨mkElem_lt z h a b, ?_⟩
    intro j hj
    unfold bitFn
    rw [mkElem_testBit a b (by omega), mkElem_testBit a b (by omega),
        mkElem_testBit a b (by omega)]
    have h1 : h + 1 - j = (h - 1 - j) + 2 := by omega
    have h2 : h + 1 - (j + 1) = (h - 1 - j) + 1 := by omega
    have h3 : h + 1 - (j + 2) = h - 1 - j := by omega
    rw [h1, h2, h3, sol2, show h - 1 - (h - 1 - j) = j by omega]
    cases z.testBit j <;> cases (!(sol (fun j => z.testBit j) h a b (h - 1 - j + 1)) &&
      sol (fun j => z.testBit j) h a b (h - 1 - j)) <;> rfl

lemma maskFn_testBit_eq_Apat {h r k : Nat} (hr : 2 * r ≤ h) (hk : k < h + 2) :
    (maskFn h r).testBit k = Apat r (h + 1 - k) := by
  rw [maskFn_testBit h r hr k, Apat]
  by_cases hL : ∃ i ≤ r, k = h - 2 * i
  · rw [decide_eq_true hL, decide_eq_true]
    obtain ⟨i, hi, heq⟩ := hL
    omega
  · rw [decide_eq_false hL, decide_eq_false]
    rintro ⟨hmod, hdiv⟩
    exact hL ⟨(h + 1 - k) / 2, hdiv, by omega⟩

lemma maskFn_testBit_eq_Cpat {h s k : Nat} (hh : 0 < h) (hs : 2 * s ≤ h - 1) (hk : k < h + 2) :
    (maskFn (h - 1) s).testBit k = Cpat s (h + 1 - k) := by
  rw [maskFn_testBit (h - 1) s hs k, Cpat]
  by_cases hL : ∃ i ≤ s, k = h - 1 - 2 * i
  · rw [decide_eq_true hL, decide_eq_true]
    obtain ⟨i, hi, heq⟩ := hL
    omega
  · rw [decide_eq_false hL, decide_eq_false]
    rintro ⟨hmod, hge, hdiv⟩
    exact hL ⟨(h + 1 - k) / 2 - 1, by omega, by omega⟩

lemma two_pow_testBit_eq_zero {h k : Nat} (hk : k < h + 2) :
    (2 ^ (h + 1)).testBit k = decide (h + 1 - k = 0) := by
  rw [Nat.testBit_two_pow]
  by_cases heq : h + 1 = k
  · rw [decide_eq_true heq, decide_eq_true (by omega)]
  · rw [decide_eq_false heq, decide_eq_false (by omega)]

lemma xor_cancel_right (x y w : Nat) : (x ^^^ w) ^^^ (y ^^^ w) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_xor]
  cases x.testBit k <;> cases y.testBit k <;> cases w.testBit k <;> rfl

lemma shifted_bit_diff (u0 u1 u2 v0 v1 v2 k0 k1 k2 : Bool)
    (hfib : xor u0 (!u1 && u2) = xor v0 (!v1 && v2)) :
    (xor (xor u0 k0) (!(xor u1 k1) && xor u2 k2) !=
     xor (xor v0 k0) (!(xor v1 k1) && xor v2 k2)) =
    xor (xor u1 v1 && k2) (xor u2 v2 && k1) := by
  revert u0 u1 u2 v0 v1 v2 k0 k1 k2 hfib
  decide

lemma distFn_eq_wtFn {h z u v : Nat} (hz : z < 2 ^ h)
    (hu : u ∈ fiberFn h z) (hv : v ∈ fiberFn h z)
    (Q : List (Nat × Nat)) (hQ : ∀ p ∈ Q, p.2 < h) :
    distFn Q u v = wtFn Q (u ^^^ v) := by
  unfold distFn wtFn
  congr 1
  apply List.filter_congr
  intro p hp
  have hp2 : p.2 < h := hQ p hp
  have hu_bit : bitFn u p.2 = z.testBit p.2 := by
    unfold fiberFn at hu
    rw [Finset.mem_filter, replyFn_eq_iff hz] at hu
    exact hu.2 p.2 hp2
  have hv_bit : bitFn v p.2 = z.testBit p.2 := by
    unfold fiberFn at hv
    rw [Finset.mem_filter, replyFn_eq_iff hz] at hv
    exact hv.2 p.2 hp2
  have hfib : bitFn u p.2 = bitFn v p.2 := hu_bit.trans hv_bit.symm
  unfold bitFn at hfib ⊢
  simp only [Nat.testBit_xor]
  exact shifted_bit_diff
    (u.testBit p.2) (u.testBit (p.2 + 1)) (u.testBit (p.2 + 2))
    (v.testBit p.2) (v.testBit (p.2 + 1)) (v.testBit (p.2 + 2))
    (p.1.testBit p.2) (p.1.testBit (p.2 + 1)) (p.1.testBit (p.2 + 2))
    hfib

lemma sum_four_distinct {x0 x1 x2 x3 : Nat}
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h03 : x0 ≠ x3)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (g : Nat → Nat) :
    ∑ x ∈ ({x0, x1, x2, x3} : Finset Nat), g x = g x0 + g x1 + g x2 + g x3 := by
  rw [Finset.sum_insert (by simp [h01, h02, h03]),
      Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton]
  omega

lemma list_filter_length_cons {α : Type} (p : α → Bool) (x : α) (xs : List α) :
    ((x :: xs).filter p).length = (if p x then 1 else 0) + (xs.filter p).length := by
  cases hpx : p x
  · simp [List.filter_cons_of_neg, hpx]
  · simp [List.filter_cons_of_pos, hpx]
    omega

end PEqualNP.Outside.L_meta_33688_aux

theorem PEqualNP.Outside.L_meta_33688 : (∀ h : Nat, 0 < h →
  let bit := fun (u j : Nat) =>
    xor (u.testBit j) (!(u.testBit (j+1)) && u.testBit (j+2))
  let reply := fun u : Nat =>
    ∑ j ∈ Finset.range h, if bit u j then 2^j else 0
  let fiber := fun z : Nat =>
    (Finset.range (2^(h+2))).filter (fun u => reply u = z)
  let dist := fun (Q : List (Nat × Nat)) (u v : Nat) =>
    (Q.filter (fun p => bit (u ^^^ p.1) p.2 != bit (v ^^^ p.1) p.2)).length
  let mask := fun (top r : Nat) => ∑ i ∈ Finset.range (r+1), 2^(top-2*i)
  let six := fun (r s : Nat) =>
    let a := mask h r
    let b := 2^(h+1)
    let c := mask (h-1) s
    [a, b, a ^^^ b, b ^^^ c, (a ^^^ b) ^^^ c, a ^^^ c]
  let wt := fun (Q : List (Nat × Nat)) (v : Nat) =>
    (Q.filter (fun p => xor
      (v.testBit (p.2+1) && p.1.testBit (p.2+2))
      (v.testBit (p.2+2) && p.1.testBit (p.2+1)))).length
  let stop := fun (z lane : Nat) =>
    ((List.range ((h-lane)/2)).filter (fun i => z.testBit (h-1-lane-2*i))).headD ((h-lane)/2)
  ∀ z < 2^h, ∀ (Q : List (Nat × Nat)), (∀ p ∈ Q, p.2 < h) → ∀ t : Nat,
    (((fiber z).product (fiber z)).filter
      (fun uv => uv.1 ≠ uv.2 ∧ dist Q uv.1 uv.2 = t)).card =
    2 * ((six (stop z 0) (stop z 1)).filter (fun v => wt Q v == t)).length) := by
  intro h hh bit reply fiber dist mask six wt stop z hz Q hQ t
  open PEqualNP.Outside.L_meta_33688_aux in
  let zF : Nat → Bool := fun j => z.testBit j
  let r : Nat := stopF zF h 0
  let s : Nat := stopF zF h 1
  have hr_le : r ≤ h / 2 := (stopSpec zF h 0).1
  have hs_le : s ≤ (h - 1) / 2 := (stopSpec zF h 1).1
  have h2r : 2 * r ≤ h := by omega
  have h2s : 2 * s ≤ h - 1 := by omega
  let a : Nat := maskFn h r
  let b : Nat := 2 ^ (h + 1)
  let c : Nat := maskFn (h - 1) s
  have ha_lt : a < 2 ^ (h + 2) :=
    lt_trans (maskFn_lt h r h2r) (Nat.pow_lt_pow_right (by decide) (by omega))
  have hb_lt : b < 2 ^ (h + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hc_lt : c < 2 ^ (h + 2) :=
    lt_of_lt_of_le (maskFn_lt (h - 1) s h2s) (Nat.pow_le_pow_right (by decide) (by omega))
  let u00 : Nat := mkElem z h false false
  let u10 : Nat := mkElem z h true false
  let u01 : Nat := mkElem z h false true
  let u11 : Nat := mkElem z h true true
  have h00_10 : u00 ≠ u10 := fun e => by have := (mkElem_inj e).1; contradiction
  have h00_01 : u00 ≠ u01 := fun e => by have := (mkElem_inj e).2; contradiction
  have h00_11 : u00 ≠ u11 := fun e => by have := (mkElem_inj e).1; contradiction
  have h10_01 : u10 ≠ u01 := fun e => by have := (mkElem_inj e).1; contradiction
  have h10_11 : u10 ≠ u11 := fun e => by have := (mkElem_inj e).2; contradiction
  have h01_11 : u01 ≠ u11 := fun e => by have := (mkElem_inj e).1; contradiction
  have hfib_eq : fiber z = ({u00, u10, u01, u11} : Finset Nat) := by
    change fiberFn h z = {u00, u10, u01, u11}
    ext u
    rw [mem_fiberFn_iff hz]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨x, y, rfl⟩
      cases x <;> cases y
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨false, false, rfl⟩
      · exact ⟨true, false, rfl⟩
      · exact ⟨false, true, rfl⟩
      · exact ⟨true, true, rfl⟩
  have hmem00 : u00 ∈ fiberFn h z := (mem_fiberFn_iff hz).mpr ⟨false, false, rfl⟩
  have hmem10 : u10 ∈ fiberFn h z := (mem_fiberFn_iff hz).mpr ⟨true, false, rfl⟩
  have hmem01 : u01 ∈ fiberFn h z := (mem_fiberFn_iff hz).mpr ⟨false, true, rfl⟩
  have hmem11 : u11 ∈ fiberFn h z := (mem_fiberFn_iff hz).mpr ⟨true, true, rfl⟩
  have h10_00 : u10 ^^^ u00 = a := by
    apply eq_of_testBit_lt (Nat.xor_lt_two_pow (mkElem_lt z h true false) (mkElem_lt z h false false)) ha_lt
    intro k hk
    rw [Nat.testBit_xor, mkElem_testBit true false hk, mkElem_testBit false false hk,
        Dform zF h true false (h + 1 - k) (by omega)]
    simp only [Dpat, Bool.true_and, Bool.false_and, Bool.xor_false]
    exact (maskFn_testBit_eq_Apat h2r hk).symm
  have h01_00 : u01 ^^^ u00 = b ^^^ c := by
    apply eq_of_testBit_lt (Nat.xor_lt_two_pow (mkElem_lt z h false true) (mkElem_lt z h false false))
      (Nat.xor_lt_two_pow hb_lt hc_lt)
    intro k hk
    rw [Nat.testBit_xor, Nat.testBit_xor, mkElem_testBit false true hk, mkElem_testBit false false hk,
        Dform zF h false true (h + 1 - k) (by omega)]
    simp only [Dpat, Bool.false_and, Bool.true_and, Bool.not_false, Bool.false_xor]
    rw [two_pow_testBit_eq_zero hk, maskFn_testBit_eq_Cpat hh h2s hk]
  have h11_00 : u11 ^^^ u00 = a ^^^ b := by
    apply eq_of_testBit_lt (Nat.xor_lt_two_pow (mkElem_lt z h true true) (mkElem_lt z h false false))
      (Nat.xor_lt_two_pow ha_lt hb_lt)
    intro k hk
    rw [Nat.testBit_xor, Nat.testBit_xor, mkElem_testBit true true hk, mkElem_testBit false false hk,
        Dform zF h true true (h + 1 - k) (by omega)]
    simp only [Dpat, Bool.true_and, Bool.not_true, Bool.and_false, Bool.false_and, Bool.xor_false]
    rw [maskFn_testBit_eq_Apat h2r hk, two_pow_testBit_eq_zero hk]
  have h00_10_x : u00 ^^^ u10 = a := by rw [Nat.xor_comm, h10_00]
  have h00_01_x : u00 ^^^ u01 = b ^^^ c := by rw [Nat.xor_comm, h01_00]
  have h00_11_x : u00 ^^^ u11 = a ^^^ b := by rw [Nat.xor_comm, h11_00]
  have h10_11_x : u10 ^^^ u11 = b := by
    rw [← xor_cancel_right u10 u11 u00, h10_00, h11_00, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have h11_10_x : u11 ^^^ u10 = b := by rw [Nat.xor_comm, h10_11_x]
  have h10_01_x : u10 ^^^ u01 = (a ^^^ b) ^^^ c := by
    rw [← xor_cancel_right u10 u01 u00, h10_00, h01_00, Nat.xor_assoc]
  have h01_10_x : u01 ^^^ u10 = (a ^^^ b) ^^^ c := by rw [Nat.xor_comm, h10_01_x]
  have h11_01_x : u11 ^^^ u01 = a ^^^ c := by
    rw [← xor_cancel_right u11 u01 u00, h11_00, h01_00, Nat.xor_assoc,
        ← Nat.xor_assoc b b c, Nat.xor_self, Nat.zero_xor]
  have h01_11_x : u01 ^^^ u11 = a ^^^ c := by rw [Nat.xor_comm, h11_01_x]
  have hd : ∀ x ∈ fiberFn h z, ∀ y ∈ fiberFn h z, dist Q x y = wt Q (x ^^^ y) :=
    fun x hx y hy => distFn_eq_wtFn hz hx hy Q hQ
  rw [hfib_eq, Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
  rw [sum_four_distinct h00_10 h00_01 h00_11 h10_01 h10_11 h01_11]
  rw [sum_four_distinct h00_10 h00_01 h00_11 h10_01 h10_11 h01_11,
      sum_four_distinct h00_10 h00_01 h00_11 h10_01 h10_11 h01_11,
      sum_four_distinct h00_10 h00_01 h00_11 h10_01 h10_11 h01_11,
      sum_four_distinct h00_10 h00_01 h00_11 h10_01 h10_11 h01_11]
  have hd0010 := hd u00 hmem00 u10 hmem10
  have hd1000 := hd u10 hmem10 u00 hmem00
  have hd0001 := hd u00 hmem00 u01 hmem01
  have hd0100 := hd u01 hmem01 u00 hmem00
  have hd0011 := hd u00 hmem00 u11 hmem11
  have hd1100 := hd u11 hmem11 u00 hmem00
  have hd1001 := hd u10 hmem10 u01 hmem01
  have hd0110 := hd u01 hmem01 u10 hmem10
  have hd1011 := hd u10 hmem10 u11 hmem11
  have hd1110 := hd u11 hmem11 u10 hmem10
  have hd0111 := hd u01 hmem01 u11 hmem11
  have hd1101 := hd u11 hmem11 u01 hmem01
  rw [h00_10_x] at hd0010
  rw [h10_00] at hd1000
  rw [h00_01_x] at hd0001
  rw [h01_00] at hd0100
  rw [h00_11_x] at hd0011
  rw [h11_00] at hd1100
  rw [h10_01_x] at hd1001
  rw [h01_10_x] at hd0110
  rw [h10_11_x] at hd1011
  rw [h11_10_x] at hd1110
  rw [h01_11_x] at hd0111
  rw [h11_01_x] at hd1101
  change ((if u00 ≠ u00 ∧ dist Q u00 u00 = t then 1 else 0) +
      (if u00 ≠ u10 ∧ dist Q u00 u10 = t then 1 else 0) +
      (if u00 ≠ u01 ∧ dist Q u00 u01 = t then 1 else 0) +
      (if u00 ≠ u11 ∧ dist Q u00 u11 = t then 1 else 0)) +
    ((if u10 ≠ u00 ∧ dist Q u10 u00 = t then 1 else 0) +
      (if u10 ≠ u10 ∧ dist Q u10 u10 = t then 1 else 0) +
      (if u10 ≠ u01 ∧ dist Q u10 u01 = t then 1 else 0) +
      (if u10 ≠ u11 ∧ dist Q u10 u11 = t then 1 else 0)) +
    ((if u01 ≠ u00 ∧ dist Q u01 u00 = t then 1 else 0) +
      (if u01 ≠ u10 ∧ dist Q u01 u10 = t then 1 else 0) +
      (if u01 ≠ u01 ∧ dist Q u01 u01 = t then 1 else 0) +
      (if u01 ≠ u11 ∧ dist Q u01 u11 = t then 1 else 0)) +
    ((if u11 ≠ u00 ∧ dist Q u11 u00 = t then 1 else 0) +
      (if u11 ≠ u10 ∧ dist Q u11 u10 = t then 1 else 0) +
      (if u11 ≠ u01 ∧ dist Q u11 u01 = t then 1 else 0) +
      (if u11 ≠ u11 ∧ dist Q u11 u11 = t then 1 else 0)) =
    2 * (([a, b, a ^^^ b, b ^^^ c, (a ^^^ b) ^^^ c, a ^^^ c]).filter (fun v => wt Q v == t)).length
  rw [hd0010, hd1000, hd0001, hd0100, hd0011, hd1100,
      hd1001, hd0110, hd1011, hd1110, hd0111, hd1101]
  simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte,
    h00_10, h00_01, h00_11, h10_01, h10_11, h01_11,
    h00_10.symm, h00_01.symm, h00_11.symm, h10_01.symm, h10_11.symm, h01_11.symm,
    not_false_eq_true, true_and]
  simp only [list_filter_length_cons, List.filter_nil, List.length_nil, beq_iff_eq]
  omega
