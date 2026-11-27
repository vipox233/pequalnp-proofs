import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_510_aux

private def hdist {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card

private lemma hdist_self {n : ℕ} (x : Fin n → Bool) : hdist x x = 0 := by
  simp [hdist]

private lemma hdist_comm {n : ℕ} (x y : Fin n → Bool) : hdist x y = hdist y x := by
  unfold hdist
  congr 1
  ext i
  simp [ne_comm]

private def xorPt {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool :=
  fun i => xor (x i) (y i)

private lemma hdist_xor_eq {n : ℕ} (c y : Fin n → Bool) :
    hdist c y = ((Finset.univ : Finset (Fin n)).filter (fun i => xorPt c y i = true)).card := by
  unfold hdist xorPt
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases c i <;> cases y i <;> decide

private def ball {n : ℕ} (c : Fin n → Bool) (r : ℕ) : Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).filter (fun y => hdist c y ≤ r)

private lemma ball_card_eq_zero {n : ℕ} (c : Fin n → Bool) (r : ℕ) :
    (ball c r).card = (ball (fun _ : Fin n => false) r).card := by
  refine Finset.card_bij (fun y _ => xorPt c y) ?_ ?_ ?_
  · intro y hy
    have hle := (Finset.mem_filter.mp hy).2
    simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hdist_xor_eq] at hle
    have hEq : hdist (fun _ => false) (xorPt c y) =
        ((Finset.univ : Finset (Fin n)).filter (fun i => xorPt c y i = true)).card := by
      unfold hdist
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases xorPt c y i <;> decide
    rwa [hEq]
  · intro y1 _ y2 _ heq
    funext i
    have hi := congrFun heq i
    dsimp [xorPt] at hi
    cases hc : c i <;> cases h1 : y1 i <;> cases h2 : y2 i <;> simp_all
  · intro z hz
    refine ⟨xorPt c z, ?_, ?_⟩
    · have hle := (Finset.mem_filter.mp hz).2
      simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
      have hEq1 : hdist (fun _ => false) z =
          ((Finset.univ : Finset (Fin n)).filter (fun i => z i = true)).card := by
        unfold hdist
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        cases z i <;> decide
      have hEq2 : xorPt c (xorPt c z) = z := by
        funext i
        dsimp [xorPt]
        cases c i <;> cases z i <;> decide
      rw [hdist_xor_eq, hEq2, ← hEq1]
      exact hle
    · funext i
      dsimp [xorPt]
      cases c i <;> cases z i <;> decide

private lemma choose_le_ball_card {n r : ℕ} :
    n.choose r ≤ (ball (fun _ : Fin n => false) r).card := by
  have hcard_pow : ((Finset.univ : Finset (Fin n)).powersetCard r).card = n.choose r := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hcard_pow]
  refine Finset.card_le_card_of_injOn (fun S (i : Fin n) => decide (i ∈ S)) ?_ ?_
  · intro S hS
    have hScard : S.card = r := (Finset.mem_powersetCard.mp hS).2
    simp only [ball, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfilt : ((Finset.univ : Finset (Fin n)).filter (fun i => (false : Bool) ≠ decide (i ∈ S))) = S := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi : i ∈ S <;> simp [hi]
    unfold hdist
    rw [hfilt, hScard]
  · intro S1 _ S2 _ hEq
    ext i
    have hi := congrFun hEq i
    by_cases h1 : i ∈ S1 <;> by_cases h2 : i ∈ S2 <;> simp_all

private lemma exists_good_step {n r : ℕ} (U : Finset (Fin n → Bool)) :
    let V := (ball (fun _ : Fin n => false) r).card
    ∃ c : Fin n → Bool,
      U.card * V ≤ 2 ^ n * (U ∩ ball c r).card := by
  intro V
  have hsum :
      (∑ c : Fin n → Bool, (U ∩ ball c r).card) = U.card * V := by
    have h1 : ∀ c : Fin n → Bool,
        (U ∩ ball c r).card = ∑ y ∈ U, if hdist c y ≤ r then 1 else 0 := by
      intro c
      rw [← Finset.card_filter]
      congr 1
      ext y
      simp [ball]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ y ∈ U, (∑ c : Fin n → Bool, if hdist c y ≤ r then 1 else 0) = V := by
      intro y _
      rw [← Finset.card_filter]
      have hfilt : (Finset.univ.filter (fun c : Fin n → Bool => hdist c y ≤ r)) = ball y r := by
        ext c
        simp [ball, hdist_comm]
      rw [hfilt]
      exact ball_card_eq_zero y r
    rw [Finset.sum_congr rfl h2]
    simp
  have hcard_univ : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp
  by_contra h
  push Not at h
  have hlt : ∑ c : Fin n → Bool, 2 ^ n * (U ∩ ball c r).card <
      ∑ _c : Fin n → Bool, U.card * V := by
    refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) ?_
    intro c _
    exact h c
  rw [← Finset.mul_sum, hsum, Finset.sum_const, hcard_univ, smul_eq_mul] at hlt
  omega

private lemma greedy_cover_step {n r : ℕ} (t : ℕ) :
    let V := (ball (fun _ : Fin n => false) r).card
    ∃ C : Finset (Fin n → Bool),
      C.card ≤ t ∧
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun y => ∀ c ∈ C, ¬ hdist c y ≤ r)).card : ℝ) ≤
        (2 : ℝ) ^ n * (1 - (V : ℝ) / (2 : ℝ) ^ n) ^ t := by
  intro V
  induction t with
  | zero =>
    refine ⟨∅, le_rfl, ?_⟩
    simp
  | succ t ih =>
    rcases ih with ⟨C, hCcard, hUbound⟩
    let U : Finset (Fin n → Bool) :=
      (Finset.univ : Finset (Fin n → Bool)).filter (fun y => ∀ c ∈ C, ¬ hdist c y ≤ r)
    rcases exists_good_step (r := r) U with ⟨c0, hc0⟩
    refine ⟨insert c0 C, le_trans (Finset.card_insert_le c0 C) (Nat.succ_le_succ hCcard), ?_⟩
    let U' : Finset (Fin n → Bool) :=
      (Finset.univ : Finset (Fin n → Bool)).filter (fun y => ∀ c ∈ insert c0 C, ¬ hdist c y ≤ r)
    have hU'_eq : U' = U \ (U ∩ ball c0 r) := by
      ext y
      simp only [U', U, ball, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_insert, forall_eq_or_imp, not_and]
      tauto
    have hU'_card : U'.card + (U ∩ ball c0 r).card = U.card := by
      rw [hU'_eq]
      exact Finset.card_sdiff_add_card_eq_card Finset.inter_subset_left
    have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hV_le : V ≤ 2 ^ n := by
      calc
        V = (ball (fun _ : Fin n => false) r).card := rfl
        _ ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_le_univ _
        _ = 2 ^ n := by simp
    have hfactor_nonneg : (0 : ℝ) ≤ 1 - (V : ℝ) / (2 : ℝ) ^ n := by
      have hVR : (V : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hV_le
      rw [sub_nonneg, div_le_one h2n_pos]
      exact hVR
    have hstep_nat : 2 ^ n * U'.card + U.card * V ≤ 2 ^ n * U.card := by
      have hc0' : U.card * V ≤ 2 ^ n * (U ∩ ball c0 r).card := hc0
      have : 2 ^ n * U'.card + 2 ^ n * (U ∩ ball c0 r).card = 2 ^ n * U.card := by
        rw [← Nat.mul_add, hU'_card]
      omega
    have hstep_real : (U'.card : ℝ) ≤ (U.card : ℝ) * (1 - (V : ℝ) / (2 : ℝ) ^ n) := by
      have h1 : (2 : ℝ) ^ n * (U'.card : ℝ) + (U.card : ℝ) * (V : ℝ) ≤ (2 : ℝ) ^ n * (U.card : ℝ) := by
        exact_mod_cast hstep_nat
      have h2 : (2 : ℝ) ^ n * (U'.card : ℝ) ≤ (2 : ℝ) ^ n * ((U.card : ℝ) * (1 - (V : ℝ) / (2 : ℝ) ^ n)) := by
        have hrew : (2 : ℝ) ^ n * ((U.card : ℝ) * (1 - (V : ℝ) / (2 : ℝ) ^ n)) =
            (2 : ℝ) ^ n * (U.card : ℝ) - (U.card : ℝ) * (V : ℝ) := by
          field_simp [ne_of_gt h2n_pos]
        linarith
      exact le_of_mul_le_mul_left h2 h2n_pos
    calc
      (U'.card : ℝ) ≤ (U.card : ℝ) * (1 - (V : ℝ) / (2 : ℝ) ^ n) := hstep_real
      _ ≤ ((2 : ℝ) ^ n * (1 - (V : ℝ) / (2 : ℝ) ^ n) ^ t) * (1 - (V : ℝ) / (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_right hUbound hfactor_nonneg
      _ = (2 : ℝ) ^ n * (1 - (V : ℝ) / (2 : ℝ) ^ n) ^ (t + 1) := by
        rw [pow_succ]
        ring

private lemma exists_cover_size {n r : ℕ} (hr : r ≤ n) :
    let V := (ball (fun _ : Fin n => false) r).card
    ∃ C : Finset (Fin n → Bool),
      (∀ y : Fin n → Bool, ∃ c ∈ C, hdist c y ≤ r) ∧
      C.card * V ≤ (n + 2) * 2 ^ n := by
  intro V
  have hVpos : 0 < V := by
    have h1 : 0 < n.choose r := Nat.choose_pos hr
    have h2 := choose_le_ball_card (n := n) (r := r)
    omega
  have hV_le : V ≤ 2 ^ n := by
    calc
      V ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_le_univ _
      _ = 2 ^ n := by simp
  let t : ℕ := (n * 2 ^ n + V - 1) / V
  have ht_ge : n * 2 ^ n ≤ t * V := by
    have h1 : V * t + (n * 2 ^ n + V - 1) % V = n * 2 ^ n + V - 1 :=
      Nat.div_add_mod (n * 2 ^ n + V - 1) V
    have h2 : (n * 2 ^ n + V - 1) % V < V := Nat.mod_lt _ hVpos
    have h3 : V * t = t * V := Nat.mul_comm V t
    omega
  have ht_le : t * V ≤ n * 2 ^ n + V - 1 := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_le (n * 2 ^ n + V - 1) V
  rcases greedy_cover_step (n := n) (r := r) t with ⟨C0, hC0card, hUbound⟩
  let U : Finset (Fin n → Bool) :=
    (Finset.univ : Finset (Fin n → Bool)).filter (fun y => ∀ c ∈ C0, ¬ hdist c y ≤ r)
  have hU_le_one : U.card ≤ 1 := by
    have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hfactor_nonneg : (0 : ℝ) ≤ 1 - (V : ℝ) / (2 : ℝ) ^ n := by
      have hVR : (V : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hV_le
      rw [sub_nonneg, div_le_one h2n_pos]
      exact hVR
    have hexp1 : 1 - (V : ℝ) / (2 : ℝ) ^ n ≤ Real.exp (-(V : ℝ) / (2 : ℝ) ^ n) := by
      have h := Real.add_one_le_exp (-(V : ℝ) / (2 : ℝ) ^ n)
      have h1 : 1 - (V : ℝ) / (2 : ℝ) ^ n = -(V : ℝ) / (2 : ℝ) ^ n + 1 := by ring
      rw [h1]
      exact h
    have hpow_le : (1 - (V : ℝ) / (2 : ℝ) ^ n) ^ t ≤
        Real.exp (-(t : ℝ) * (V : ℝ) / (2 : ℝ) ^ n) := by
      have h1 := pow_le_pow_left₀ hfactor_nonneg hexp1 t
      rw [← Real.exp_nat_mul] at h1
      have heq : (t : ℝ) * (-(V : ℝ) / (2 : ℝ) ^ n) = -(t : ℝ) * (V : ℝ) / (2 : ℝ) ^ n := by ring
      rwa [heq] at h1
    have hexp_n : Real.exp (-(t : ℝ) * (V : ℝ) / (2 : ℝ) ^ n) ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have htR : (n : ℝ) * (2 : ℝ) ^ n ≤ (t : ℝ) * (V : ℝ) := by exact_mod_cast ht_ge
      rw [div_le_iff₀ h2n_pos]
      linarith
    have h2e : (2 : ℝ) ^ n * Real.exp (-(n : ℝ)) ≤ 1 := by
      have h2lt : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hpow2 : (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h2lt n
      rw [← Real.exp_nat_mul, mul_one] at hpow2
      have hmul := mul_le_mul_of_nonneg_right hpow2 (le_of_lt (Real.exp_pos (-(n : ℝ))))
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
      exact hmul
    have hU_real : (U.card : ℝ) ≤ 1 := by
      calc
        (U.card : ℝ) ≤ (2 : ℝ) ^ n * (1 - (V : ℝ) / (2 : ℝ) ^ n) ^ t := hUbound
        _ ≤ (2 : ℝ) ^ n * Real.exp (-(t : ℝ) * (V : ℝ) / (2 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hpow_le (le_of_lt h2n_pos)
        _ ≤ (2 : ℝ) ^ n * Real.exp (-(n : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp_n (le_of_lt h2n_pos)
        _ ≤ 1 := h2e
    exact_mod_cast hU_real
  refine ⟨C0 ∪ U, ?_, ?_⟩
  · intro y
    by_cases hy : ∃ c ∈ C0, hdist c y ≤ r
    · rcases hy with ⟨c, hc, hle⟩
      exact ⟨c, Finset.mem_union_left U hc, hle⟩
    · push Not at hy
      have hyU : y ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ y, fun c hc => not_le.mpr (hy c hc)⟩
      refine ⟨y, Finset.mem_union_right C0 hyU, ?_⟩
      rw [hdist_self]
      exact Nat.zero_le r
  · have hcard : (C0 ∪ U).card ≤ t + 1 := by
      have := Finset.card_union_le C0 U
      omega
    have hmul := Nat.mul_le_mul_right V hcard
    calc
      (C0 ∪ U).card * V ≤ (t + 1) * V := hmul
      _ = t * V + V := by ring
      _ ≤ (n * 2 ^ n + V - 1) + V := by omega
      _ ≤ n * 2 ^ n + 2 * 2 ^ n := by omega
      _ = (n + 2) * 2 ^ n := by ring

end PEqualNP.Outside.L_lib_510_aux

theorem PEqualNP.Outside.L_lib_510 : (∀ (n a : Nat), 0 < a →
  let Point := Fin n → Bool
  let dist := fun (x y : Point) =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card
  ∃ (r : Nat) (C : Finset Point), r ≤ n ∧ (∀ y : Point, ∃ c ∈ C, dist c y ≤ r) ∧
    C.card * a^r * (a+1)^n ≤ (n+2)*(n+1)*(2*a)^n) := by
  intro n a ha Point dist
  have hbinom : (a + 1) ^ n = ∑ k ∈ Finset.range (n + 1), n.choose k * a ^ (n - k) := by
    have h := add_pow 1 a n
    rw [add_comm] at h
    rw [h]
    refine Finset.sum_congr rfl ?_
    intro k _
    simp [mul_comm]
  have hne : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
  rcases Finset.exists_max_image (Finset.range (n + 1)) (fun k => n.choose k * a ^ (n - k)) hne with
    ⟨r, hr_mem, hr_max⟩
  have hr_le : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr_mem)
  have hpow_le : (a + 1) ^ n ≤ (n + 1) * (n.choose r * a ^ (n - r)) := by
    rw [hbinom]
    calc
      ∑ k ∈ Finset.range (n + 1), n.choose k * a ^ (n - k)
          ≤ ∑ _k ∈ Finset.range (n + 1), n.choose r * a ^ (n - r) := Finset.sum_le_sum hr_max
      _ = (n + 1) * (n.choose r * a ^ (n - r)) := by simp
  let V := (PEqualNP.Outside.L_lib_510_aux.ball (fun _ : Fin n => false) r).card
  have hVpos : 0 < V := by
    have h1 : 0 < n.choose r := Nat.choose_pos hr_le
    have h2 := PEqualNP.Outside.L_lib_510_aux.choose_le_ball_card (n := n) (r := r)
    omega
  have hstep1 : a ^ r * (a + 1) ^ n ≤ (n + 1) * V * a ^ n := by
    have hmul := Nat.mul_le_mul_left (a ^ r) hpow_le
    have hpow_combine : a ^ r * a ^ (n - r) = a ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hr_le]
    have hchoose_le : n.choose r ≤ V := PEqualNP.Outside.L_lib_510_aux.choose_le_ball_card
    calc
      a ^ r * (a + 1) ^ n ≤ a ^ r * ((n + 1) * (n.choose r * a ^ (n - r))) := hmul
      _ = (n + 1) * n.choose r * (a ^ r * a ^ (n - r)) := by ring
      _ = (n + 1) * n.choose r * a ^ n := by rw [hpow_combine]
      _ ≤ (n + 1) * V * a ^ n := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hchoose_le)
  rcases PEqualNP.Outside.L_lib_510_aux.exists_cover_size (n := n) (r := r) hr_le with ⟨C, hcov, hCsize⟩
  refine ⟨r, C, hr_le, hcov, ?_⟩
  have hcomb : (C.card * a ^ r * (a + 1) ^ n) * V ≤ ((n + 2) * (n + 1) * (2 * a) ^ n) * V := by
    have h1 := Nat.mul_le_mul hCsize hstep1
    calc
      (C.card * a ^ r * (a + 1) ^ n) * V = (C.card * V) * (a ^ r * (a + 1) ^ n) := by ring
      _ ≤ ((n + 2) * 2 ^ n) * ((n + 1) * V * a ^ n) := h1
      _ = ((n + 2) * (n + 1) * (2 ^ n * a ^ n)) * V := by ring
      _ = ((n + 2) * (n + 1) * (2 * a) ^ n) * V := by rw [← mul_pow]
  exact Nat.le_of_mul_le_mul_right hcomb hVpos
