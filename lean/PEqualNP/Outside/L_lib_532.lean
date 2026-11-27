import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem PEqualNP.Outside.L_lib_532 :
∀ (m h : ℕ) (p : Fin h → Fin m → ℝ) (dec : Fin h → Fin m),
  2 ≤ m → (∀ y i, 0 ≤ p y i) → (∑ y, ∑ i, p y i) = 1 →
  let mass := fun y => ∑ i, p y i
  let e := ∑ y, ∑ i, if dec y = i then (0:ℝ) else p y i
  let H := ∑ y, ∑ i, -(p y i) * Real.log (p y i / mass y)
  H ≤ -e*Real.log e - (1-e)*Real.log (1-e) + e*Real.log ((m:ℝ)-1) := by
  intro m h p dec hm hp hsum mass e H
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have h1 : (1 : ℝ) < (m : ℝ) := by
      rw [← Nat.cast_one]
      exact Nat.cast_lt.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hm)
    exact sub_pos.mpr h1
  have hmass_nonneg : ∀ y, 0 ≤ mass y :=
    fun y => Finset.sum_nonneg fun i _ => hp y i
  have he_nonneg : 0 ≤ e := by
    refine Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun i _ => ?_
    by_cases hdi : dec y = i
    · simp [hdi]
    · simp [hdi, hp y i]
  have hc_add_e : (∑ y, ∑ i, if dec y = i then p y i else (0 : ℝ)) + e = 1 := by
    rw [← Finset.sum_add_distrib, ← hsum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hdi : dec y = i <;> simp [hdi]
  have hc_eq : (∑ y, ∑ i, if dec y = i then p y i else (0 : ℝ)) = 1 - e :=
    eq_sub_of_add_eq hc_add_e
  have h1e_nonneg : 0 ≤ 1 - e := by
    rw [← hc_eq]
    refine Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun i _ => ?_
    by_cases hdi : dec y = i
    · simp [hdi, hp y i]
    · simp [hdi]
  let q : Fin h → Fin m → ℝ := fun y i =>
    if dec y = i then (1 - e) * mass y else (e / ((m : ℝ) - 1)) * mass y
  have hq_row : ∀ y, (∑ i : Fin m, q y i) = mass y := by
    intro y
    set c := (e / ((m : ℝ) - 1)) * mass y
    have hsplit : ∀ i : Fin m, q y i = c + if dec y = i then (1 - e) * mass y - c else 0 := by
      intro i
      dsimp only [q]
      by_cases hdi : dec y = i <;> simp [hdi, c]
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ↓reduceIte]
    calc
      (m : ℝ) * c + ((1 - e) * mass y - c)
          = ((m : ℝ) - 1) * c + (1 - e) * mass y := by
            rw [← add_sub_assoc, ← sub_add_eq_add_sub, sub_mul (m : ℝ) 1 c, one_mul]
      _ = e * mass y + (1 - e) * mass y := by
            rw [show ((m : ℝ) - 1) * c = e * mass y by
              dsimp only [c]
              rw [← mul_assoc, mul_div_cancel₀ e hm1_pos.ne']]
      _ = mass y := by
            rw [← add_mul, add_comm e (1 - e), sub_add_cancel, one_mul]
  have hq_sum : (∑ y, ∑ i, q y i) = 1 := by
    calc
      (∑ y, ∑ i, q y i) = ∑ y, mass y := Finset.sum_congr rfl fun y _ => hq_row y
      _ = 1 := hsum
  let rhsTerm : Fin h → Fin m → ℝ := fun y i =>
    if dec y = i then -(p y i) * Real.log (1 - e)
    else -(p y i) * Real.log e + (p y i) * Real.log ((m : ℝ) - 1)
  have hrhs_sum :
      (∑ y, ∑ i, rhsTerm y i) =
        -e * Real.log e - (1 - e) * Real.log (1 - e) + e * Real.log ((m : ℝ) - 1) := by
    have hsplit : ∀ y i, rhsTerm y i =
        (if dec y = i then p y i else (0 : ℝ)) * (-Real.log (1 - e)) +
        (if dec y = i then (0 : ℝ) else p y i) * (-Real.log e + Real.log ((m : ℝ) - 1)) := by
      intro y i
      dsimp only [rhsTerm]
      by_cases hdi : dec y = i
      · simp only [hdi, ↓reduceIte, zero_mul, add_zero, mul_neg, neg_mul]
      · simp only [hdi, ↓reduceIte, zero_mul, neg_zero, zero_add, mul_add, mul_neg, neg_mul]
    calc
      (∑ y, ∑ i, rhsTerm y i)
          = ∑ y, ∑ i,
              ((if dec y = i then p y i else (0 : ℝ)) * (-Real.log (1 - e)) +
               (if dec y = i then (0 : ℝ) else p y i) * (-Real.log e + Real.log ((m : ℝ) - 1))) :=
            Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => hsplit y i
      _ = (∑ y, ∑ i, (if dec y = i then p y i else (0 : ℝ)) * (-Real.log (1 - e))) +
          (∑ y, ∑ i, (if dec y = i then (0 : ℝ) else p y i) * (-Real.log e + Real.log ((m : ℝ) - 1))) := by
            simp only [Finset.sum_add_distrib]
      _ = (∑ y, ∑ i, if dec y = i then p y i else (0 : ℝ)) * (-Real.log (1 - e)) +
          e * (-Real.log e + Real.log ((m : ℝ) - 1)) := by
            simp only [← Finset.sum_mul]
            rfl
      _ = (1 - e) * (-Real.log (1 - e)) + e * (-Real.log e + Real.log ((m : ℝ) - 1)) := by
            rw [hc_eq]
      _ = -e * Real.log e - (1 - e) * Real.log (1 - e) + e * Real.log ((m : ℝ) - 1) := by
            rw [mul_neg, mul_add, mul_neg, ← neg_mul e (Real.log e),
              ← add_assoc, add_comm (-((1 - e) * Real.log (1 - e))) (-e * Real.log e),
              ← sub_eq_add_neg]
  have hpt : ∀ y i, -(p y i) * Real.log (p y i / mass y) - rhsTerm y i ≤ q y i - p y i := by
    intro y i
    by_cases hp0 : p y i = 0
    · dsimp only [rhsTerm, q]
      by_cases hdi : dec y = i
      · simp only [hdi, ↓reduceIte, hp0, neg_zero, zero_mul, sub_self, sub_zero]
        exact mul_nonneg h1e_nonneg (hmass_nonneg y)
      · simp only [hdi, ↓reduceIte, hp0, neg_zero, zero_mul, add_zero, sub_self, sub_zero]
        exact mul_nonneg (div_nonneg he_nonneg hm1_pos.le) (hmass_nonneg y)
    · have hp_pos : 0 < p y i := lt_of_le_of_ne (hp y i) (Ne.symm hp0)
      have hmass_pos : 0 < mass y :=
        lt_of_lt_of_le hp_pos (Finset.single_le_sum (fun j _ => hp y j) (Finset.mem_univ i))
      have hpm_pos : 0 < p y i / mass y := div_pos hp_pos hmass_pos
      by_cases hdi : dec y = i
      · have h1e_pos : 0 < 1 - e := by
          have h1 : p y i ≤ ∑ j, if dec y = j then p y j else (0 : ℝ) := by
            simp [hdi]
          have h2 : (∑ j, if dec y = j then p y j else (0 : ℝ)) ≤
              ∑ y', ∑ j, if dec y' = j then p y' j else (0 : ℝ) :=
            Finset.single_le_sum
              (f := fun y' => ∑ j, if dec y' = j then p y' j else (0 : ℝ))
              (fun y' _ => Finset.sum_nonneg fun j _ => by
                by_cases h : dec y' = j <;> simp [h, hp y' j])
              (Finset.mem_univ y)
          rw [hc_eq] at h2
          exact lt_of_lt_of_le hp_pos (le_trans h1 h2)
        dsimp only [rhsTerm, q]
        simp only [hdi, ↓reduceIte]
        have hq_pos : 0 < (1 - e) * mass y := mul_pos h1e_pos hmass_pos
        have hlog : Real.log (1 - e) - Real.log (p y i / mass y) =
            Real.log (((1 - e) * mass y) / p y i) := by
          rw [← Real.log_div h1e_pos.ne' hpm_pos.ne', div_div_eq_mul_div]
        have hle := mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos hq_pos hp_pos)) hp_pos.le
        calc
          -(p y i) * Real.log (p y i / mass y) - -(p y i) * Real.log (1 - e)
              = p y i * (Real.log (1 - e) - Real.log (p y i / mass y)) := by
                rw [mul_sub, neg_mul, neg_mul, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
          _ = p y i * Real.log (((1 - e) * mass y) / p y i) := by rw [hlog]
          _ ≤ p y i * (((1 - e) * mass y) / p y i - 1) := hle
          _ = (1 - e) * mass y - p y i := by
                rw [mul_sub, mul_one, mul_div_cancel₀ _ hp_pos.ne']
      · have he_pos : 0 < e := by
          have h1 : p y i ≤ ∑ j, if dec y = j then (0 : ℝ) else p y j := by
            have hle := Finset.single_le_sum
              (f := fun j => if dec y = j then (0 : ℝ) else p y j)
              (fun j _ => by by_cases h : dec y = j <;> simp [h, hp y j]) (Finset.mem_univ i)
            simpa [hdi] using hle
          have h2 : (∑ j, if dec y = j then (0 : ℝ) else p y j) ≤ e :=
            Finset.single_le_sum
              (f := fun y' => ∑ j, if dec y' = j then (0 : ℝ) else p y' j)
              (fun y' _ => Finset.sum_nonneg fun j _ => by
                by_cases h : dec y' = j <;> simp [h, hp y' j])
              (Finset.mem_univ y)
          exact lt_of_lt_of_le hp_pos (le_trans h1 h2)
        dsimp only [rhsTerm, q]
        simp only [hdi, ↓reduceIte]
        have hfac_pos : 0 < e / ((m : ℝ) - 1) := div_pos he_pos hm1_pos
        have hq_pos : 0 < (e / ((m : ℝ) - 1)) * mass y := mul_pos hfac_pos hmass_pos
        have hlog : Real.log e - Real.log ((m : ℝ) - 1) - Real.log (p y i / mass y) =
            Real.log (((e / ((m : ℝ) - 1)) * mass y) / p y i) := by
          rw [← Real.log_div he_pos.ne' hm1_pos.ne', ← Real.log_div hfac_pos.ne' hpm_pos.ne',
            div_div_eq_mul_div]
        have hle := mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos hq_pos hp_pos)) hp_pos.le
        calc
          -(p y i) * Real.log (p y i / mass y) -
              (-(p y i) * Real.log e + p y i * Real.log ((m : ℝ) - 1))
              = p y i * (Real.log e - Real.log ((m : ℝ) - 1) - Real.log (p y i / mass y)) := by
                rw [mul_sub, mul_sub, neg_mul, neg_mul, sub_add_eq_sub_sub,
                  sub_neg_eq_add, add_comm (-(p y i * Real.log (p y i / mass y))),
                  ← sub_eq_add_neg, sub_right_comm]
          _ = p y i * Real.log (((e / ((m : ℝ) - 1)) * mass y) / p y i) := by rw [hlog]
          _ ≤ p y i * (((e / ((m : ℝ) - 1)) * mass y) / p y i - 1) := hle
          _ = (e / ((m : ℝ) - 1)) * mass y - p y i := by
                rw [mul_sub, mul_one, mul_div_cancel₀ _ hp_pos.ne']
  have htot :
      (∑ y, ∑ i, (-(p y i) * Real.log (p y i / mass y) - rhsTerm y i)) ≤
        ∑ y, ∑ i, (q y i - p y i) :=
    Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun i _ => hpt y i
  simp only [Finset.sum_sub_distrib] at htot
  rw [hq_sum, hsum, sub_self, hrhs_sum] at htot
  exact sub_nonpos.mp htot
