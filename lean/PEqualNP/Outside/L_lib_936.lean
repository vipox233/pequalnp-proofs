import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_936

open Finset

theorem ind_eq (a b : Bool) :
    (if a ≠ b then (1 : ℚ) else 0) =
      (1 - (if a then (-1 : ℚ) else 1) * (if b then (-1 : ℚ) else 1)) / 2 := by
  cases a <;> cases b <;> norm_num

theorem sgn_sq (a : Bool) : (if a then (-1 : ℚ) else 1) * (if a then (-1 : ℚ) else 1) = 1 := by
  cases a <;> norm_num

theorem abs_sgn (a : Bool) : |(if a then (-1 : ℚ) else 1)| = 1 := by
  cases a <;> norm_num

theorem ind_abs (a b : Bool) (x : ℚ) :
    |(if a ≠ b then (1 : ℚ) else 0) * x| = (if a ≠ b then (1 : ℚ) else 0) * |x| := by
  by_cases h : a ≠ b <;> simp [h]

theorem swap_term (a b : Bool) (D : ℚ) :
    (if a ≠ b then 1 / D else 0) * (if a then (-1 : ℚ) else 1) =
      -((if b ≠ a then 1 / D else 0) * (if b then (-1 : ℚ) else 1)) := by
  cases a <;> cases b <;> simp

theorem card_eq {k : ℕ} (g h : Fin k → Bool) :
    ((((Finset.univ : Finset (Fin k)).filter (fun y => g y ≠ h y)).card : ℕ) : ℚ) =
      ∑ y : Fin k, (if g y ≠ h y then (1 : ℚ) else 0) := by
  rw [Finset.natCast_card_filter]

theorem corr_eq {k : ℕ} (g h : Fin k → Bool) :
    ∑ y : Fin k, (if g y then (-1 : ℚ) else 1) * (if h y then (-1 : ℚ) else 1) =
      (k : ℚ) - 2 * ∑ y : Fin k, (if g y ≠ h y then (1 : ℚ) else 0) := by
  rw [Finset.mul_sum]
  have : ∀ y, (if g y then (-1 : ℚ) else 1) * (if h y then (-1 : ℚ) else 1) =
      1 - 2 * (if g y ≠ h y then (1 : ℚ) else 0) := by
    intro y; rw [ind_eq]; ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem key {k : ℕ} (hk : 0 < k) (g h : Fin k → Bool) :
    ∑ y : Fin k, |(if g y ≠ h y then 1 / (((Finset.univ : Finset (Fin k)).filter
        (fun y => g y ≠ h y)).card : ℚ) else 0) - 2 * (if g y ≠ h y then (1 : ℚ) else 0) / k| ≤
      |(∑ y : Fin k, (if g y then (-1 : ℚ) else 1) * (if h y then (-1 : ℚ) else 1)) / k| := by
  set D : ℚ := (((Finset.univ : Finset (Fin k)).filter (fun y => g y ≠ h y)).card : ℚ) with hD
  have hDs : D = ∑ y : Fin k, (if g y ≠ h y then (1 : ℚ) else 0) := card_eq g h
  have hpt : ∀ y, (if g y ≠ h y then 1 / D else 0) - 2 * (if g y ≠ h y then (1 : ℚ) else 0) / k =
      (if g y ≠ h y then (1 : ℚ) else 0) * (1 / D - 2 / k) := by
    intro y; by_cases hy : g y ≠ h y <;> simp [hy]
  simp only [hpt, ind_abs]
  rw [← Finset.sum_mul, ← hDs, corr_eq, ← hDs]
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  by_cases h0 : D = 0
  · rw [h0]; simp
  · have hD0 : 0 ≤ D := by rw [hD]; positivity
    rw [show D * |1 / D - 2 / k| = |D * (1 / D - 2 / k)| by rw [abs_mul, abs_of_nonneg hD0]]
    apply le_of_eq; congr 1; field_simp

end PEqualNP.Outside.L_lib_936

open PEqualNP.Outside.L_lib_936 in
theorem PEqualNP.Outside.L_lib_936 : ∀ (n k : Nat), 2 ≤ n → 0 < k → ∀ f : Fin n → Fin k → Bool,
  (∀ i j, i ≠ j → ∃ y, f i y ≠ f j y) →
  let sign := fun (i : Fin n) (y : Fin k) => if f i y then (-1 : ℚ) else 1
  let diff := fun (i j : Fin n) =>
    ((Finset.univ : Finset (Fin k)).filter (fun y => f i y ≠ f j y)).card
  let P := fun (i : Fin n) (y : Fin k) =>
    (∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) / ((n : ℚ)-1)
  let corr := fun (i j : Fin n) => (∑ y : Fin k, sign i y * sign j y) / (k : ℚ)
  let silent := (∑ y : Fin k, |(∑ j : Fin n, sign j y) / (n : ℚ)|) / (k : ℚ)
  (∀ i y, 0 ≤ P i y) ∧ (∀ i, (∑ y : Fin k, P i y) = 1) ∧
  (∀ y, (∑ i : Fin n, P i y * sign i y) = 0) ∧
  ∀ i, ((n : ℚ)-1) * (∑ y : Fin k, |P i y - 1/(k : ℚ)|) ≤
    (n : ℚ)*silent + ∑ j : Fin n, |corr i j| := by
  intro n k hn hk f hf sign diff P corr silent
  have hsg : ∀ j y, sign j y = if f j y then -1 else 1 := fun _ _ => rfl
  have hP : ∀ i y, P i y = (∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) /
      ((n : ℚ) - 1) := fun _ _ => rfl
  have hn2 : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hdsym : ∀ i j, diff i j = diff j i := by
    intro i j
    show (Finset.univ.filter (fun y => f i y ≠ f j y)).card =
      (Finset.univ.filter (fun y => f j y ≠ f i y)).card
    congr 1; apply Finset.filter_congr; intro y _; exact ne_comm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i y
    rw [hP]
    apply div_nonneg _ hn1.le
    apply Finset.sum_nonneg; intro j _; split_ifs <;> positivity
  · intro i
    have hsum : ∀ j, ∑ y : Fin k, (if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) =
        if j = i then 0 else 1 := by
      intro j
      by_cases hj : j = i
      · subst hj; simp
      · obtain ⟨y0, hy0⟩ := hf i j (Ne.symm hj)
        have hc : ((diff i j : ℕ) : ℚ) ≠ 0 := by
          have : 0 < diff i j := Finset.card_pos.mpr ⟨y0, by simp [hy0]⟩
          exact_mod_cast this.ne'
        have ht : ∀ y, (if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) =
            (if f i y ≠ f j y then (1 : ℚ) else 0) / diff i j := by
          intro y; split_ifs <;> simp
        simp only [ht, ← Finset.sum_div, hj, ite_false]
        rw [show ((diff i j : ℕ) : ℚ) = ∑ y : Fin k, (if f i y ≠ f j y then (1 : ℚ) else 0)
          from card_eq (f i) (f j)] at hc ⊢
        exact div_self hc
    simp only [hP, ← Finset.sum_div]
    rw [Finset.sum_comm]
    simp only [hsum]
    have : ∑ j : Fin n, (if j = i then (0 : ℚ) else 1) = (n : ℚ) - 1 := by
      calc ∑ j : Fin n, (if j = i then (0 : ℚ) else 1)
          = ∑ j : Fin n, (1 - if j = i then (1 : ℚ) else 0) := by
            apply Finset.sum_congr rfl; intro j _; split_ifs <;> norm_num
        _ = (n : ℚ) - 1 := by simp [Finset.sum_sub_distrib]
    rw [this, div_self hn1.ne']
  · intro y
    have hS : ∑ i : Fin n, ∑ j : Fin n,
        (if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) * sign i y = 0 := by
      have h1 : ∑ i : Fin n, ∑ j : Fin n,
          (if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) * sign i y =
          ∑ i : Fin n, ∑ j : Fin n,
            -((if f j y ≠ f i y then (1 : ℚ) / diff j i else 0) * sign j y) := by
        apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
        rw [hdsym i j, hsg, hsg]
        exact swap_term (f i y) (f j y) _
      conv_rhs at h1 => rw [Finset.sum_comm]
      simp only [Finset.sum_neg_distrib] at h1
      linarith
    simp only [hP, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul, hS, zero_div]
  · intro i
    have hpt : ∀ y, ((n : ℚ) - 1) * |P i y - 1 / (k : ℚ)| ≤
        (∑ j : Fin n, |(if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) -
          2 * (if f i y ≠ f j y then (1 : ℚ) else 0) / k|) +
          (1 + |∑ j : Fin n, sign j y|) / k := by
      intro y
      rw [hP]
      set X := ∑ j : Fin n, if f i y ≠ f j y then (1 : ℚ) / diff i j else 0 with hX
      have h2 : ∑ j : Fin n, 2 * (if f i y ≠ f j y then (1 : ℚ) else 0) / k =
          ((n : ℚ) - sign i y * ∑ j, sign j y) / k := by
        rw [← Finset.sum_div]; congr 1
        have : ∀ j, 2 * (if f i y ≠ f j y then (1 : ℚ) else 0) = 1 - sign i y * sign j y := by
          intro j; rw [ind_eq, hsg, hsg]; ring
        simp only [this, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      have hsplit : ((n : ℚ) - 1) * (X / ((n : ℚ) - 1) - 1 / k) =
          (∑ j : Fin n, ((if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) -
            2 * (if f i y ≠ f j y then (1 : ℚ) else 0) / k)) +
          (1 - sign i y * ∑ j, sign j y) / k := by
        rw [Finset.sum_sub_distrib, ← hX, h2]
        field_simp
        ring
      rw [show ((n : ℚ) - 1) * |X / ((n : ℚ) - 1) - 1 / k| =
        |((n : ℚ) - 1) * (X / ((n : ℚ) - 1) - 1 / k)| by rw [abs_mul, abs_of_pos hn1], hsplit]
      refine (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_)
      rw [abs_div, abs_of_pos hkq]
      apply div_le_div_of_nonneg_right _ hkq.le
      refine (abs_sub _ _).trans ?_
      rw [abs_one, abs_mul, hsg, abs_sgn, one_mul]
    have hj : ∀ j : Fin n, (∑ y : Fin k, |(if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) -
          2 * (if f i y ≠ f j y then (1 : ℚ) else 0) / k|) + (if j = i then 1 else 0) ≤
          |corr i j| := by
      intro j
      by_cases hji : j = i
      · subst hji
        have hc : corr j j = 1 := by
          show (∑ y : Fin k, sign j y * sign j y) / (k : ℚ) = 1
          simp only [hsg, sgn_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one]
          exact div_self hkq.ne'
        rw [hc]; simp
      · rw [if_neg hji, add_zero]
        exact key hk (f i) (f j)
    have hsil : (n : ℚ) * silent = (∑ y : Fin k, |∑ j : Fin n, sign j y|) / k := by
      show (n : ℚ) * ((∑ y : Fin k, |(∑ j : Fin n, sign j y) / (n : ℚ)|) / (k : ℚ)) = _
      have hn0 : (0 : ℚ) < n := by linarith
      simp only [abs_div, abs_of_pos hn0, ← Finset.sum_div]
      field_simp
    have hrest : ∑ y : Fin k, (1 + |∑ j : Fin n, sign j y|) / (k : ℚ) =
        1 + (∑ y : Fin k, |∑ j : Fin n, sign j y|) / k := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, add_div]
      simp [hkq.ne']
    calc ((n : ℚ) - 1) * ∑ y : Fin k, |P i y - 1 / (k : ℚ)|
        = ∑ y : Fin k, ((n : ℚ) - 1) * |P i y - 1 / (k : ℚ)| := by rw [Finset.mul_sum]
      _ ≤ ∑ y : Fin k, ((∑ j : Fin n, |(if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) -
          2 * (if f i y ≠ f j y then (1 : ℚ) else 0) / k|) +
          (1 + |∑ j : Fin n, sign j y|) / k) := Finset.sum_le_sum (fun y _ => hpt y)
      _ = (∑ j : Fin n, ((∑ y : Fin k, |(if f i y ≠ f j y then (1 : ℚ) / diff i j else 0) -
          2 * (if f i y ≠ f j y then (1 : ℚ) else 0) / k|) + (if j = i then 1 else 0))) +
          (n : ℚ) * silent := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, hrest, Finset.sum_add_distrib, hsil,
          Finset.sum_ite_eq' Finset.univ i (fun _ => (1 : ℚ)), if_pos (Finset.mem_univ _)]
        ring
      _ ≤ (∑ j : Fin n, |corr i j|) + (n : ℚ) * silent := by
        gcongr with j _; exact hj j
      _ = (n : ℚ) * silent + ∑ j : Fin n, |corr i j| := by ring
