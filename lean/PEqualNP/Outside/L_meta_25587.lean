import Mathlib

open Filter Set
open scoped Topology BigOperators

namespace PEqualNP.Outside.L_meta_25587

noncomputable section Proof

private def move (keep : Bool) (mode letter : Nat) : Nat × Nat :=
  let near := letter.testBit 0
  let far := letter.testBit 1
  let hit := letter.testBit 2
  let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
    ((mode == 3) && near)
  let diagonal := keep && !hit && (((mode == 1) && !near && !far) ||
    (mode == 2) || (mode == 3))
  (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
    hit.toNat + (aligned && hit).toNat)

private def transferScan (keep : Bool) (n code : Nat) (initial : Nat × Nat) : Nat × Nat :=
  (List.range n).foldl (fun (st : Nat × Nat) j =>
    let result := move keep st.1 ((code >>> (3*j)) % 8)
    (result.1, st.2 + result.2)) initial

private def rowGain (keep : Bool) (n m w : Nat) : Nat :=
  (transferScan keep n w (m, 0)).2

private def gain (keep : Bool) (n code : Nat) : Nat := rowGain keep n 0 code

private theorem transferScan_succ (keep : Bool) (w n m h : Nat) :
    transferScan keep (n+1) w (m,h) =
      let res := move keep m (w%8)
      transferScan keep n (w/8) (res.1,h+res.2) := by
  simp only [transferScan, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  congr 2
  · funext a j
    simp only [Nat.mul_succ, Nat.shiftRight_eq_div_pow, pow_add, Nat.div_div_eq_div_mul]
    rw [show (2:Nat)^3=8 by decide, Nat.mul_comm (2^(3*j)) 8]

private theorem transferScan_add (keep : Bool) (n w m h : Nat) :
    (transferScan keep n w (m,h)).2 = h + (transferScan keep n w (m,0)).2 := by
  induction n generalizing w m h with
  | zero => simp [transferScan]
  | succ n ih =>
    simp only [transferScan_succ, Nat.zero_add]
    rw [ih (w/8) (move keep m (w%8)).1 (h + (move keep m (w%8)).2),
      ih (w/8) (move keep m (w%8)).1 (move keep m (w%8)).2, Nat.add_assoc]

private theorem rowGain_succ (keep : Bool) (n m w : Nat) :
    rowGain keep (n+1) m w =
      (move keep m (w%8)).2 + rowGain keep n (move keep m (w%8)).1 (w/8) := by
  simp only [rowGain, transferScan_succ, Nat.zero_add]
  exact transferScan_add keep n _ _ _

private theorem rowGain_bound (keep : Bool) (n m w : Nat) : rowGain keep n m w ≤ 2*n := by
  induction n generalizing m w with
  | zero => simp [rowGain, transferScan]
  | succ n ih =>
    rw [rowGain_succ]
    have hb (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
    have hm : (move keep m (w%8)).2 ≤ 2 := by
      dsimp only [move]
      exact Nat.add_le_add (hb _) (hb _)
    have hr := ih (move keep m (w%8)).1 (w/8)
    omega

private theorem gain_bound (keep : Bool) (n w : Nat) : gain keep n w ≤ 2*n :=
  rowGain_bound keep n 0 w

private noncomputable def rowMoment (keep : Bool) (n m : Nat) (z : ℝ) : ℝ :=
  (∑ w ∈ Finset.range (8^n), z ^ rowGain keep n m w) / (8:ℝ)^n

private noncomputable def moment (keep : Bool) (n : Nat) (z : ℝ) : ℝ :=
  (∑ w ∈ Finset.range (8^n), z ^ gain keep n w) / (8:ℝ)^n

private theorem rowMoment_zero (keep : Bool) (m : Nat) (z : ℝ) :
    rowMoment keep 0 m z = 1 := by
  simp [rowMoment, rowGain, transferScan]

private theorem transferBlocks {α : Type*} [AddCommMonoid α] (k : Nat) (F : Nat → α) :
    (∑ w ∈ Finset.range (8*k), F w) =
      ∑ v ∈ Finset.range k, ∑ a ∈ Finset.range 8, F (8*v+a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ _ k]

private theorem rowMoment_succ (keep : Bool) (n m : Nat) (z : ℝ) :
    rowMoment keep (n+1) m z =
      (∑ a ∈ Finset.range 8,
        z ^ (move keep m a).2 * rowMoment keep n (move keep m a).1 z) / 8 := by
  simp only [rowMoment, pow_succ (8:ℝ), div_mul_eq_div_div]
  congr 1
  rw [pow_succ, Nat.mul_comm (8^n) 8, transferBlocks, Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a < 8 := Finset.mem_range.mp ha
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [rowGain_succ, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt ha',
    Nat.mul_add_div (by decide : 0 < 8), Nat.div_eq_of_lt ha', Nat.add_zero, pow_add]

private theorem row_zero_succ (keep : Bool) (n : Nat) (z : ℝ) :
    rowMoment keep (n+1) 0 z = ((4+4*z) * rowMoment keep n 1 z) / 8 := by
  rw [rowMoment_succ]
  congr 1
  cases keep <;> norm_num [Finset.sum_range_succ, move, Nat.testBit] <;> ring

private theorem row_one_full (keep : Bool) (n : Nat) (z : ℝ) :
    rowMoment keep (n+1) 1 z =
      (z^2 * rowMoment keep n 0 z + (if keep then 2+3*z else 3+3*z) * rowMoment keep n 1 z +
        rowMoment keep n 2 z + (if keep then rowMoment keep n 3 z else 0)) / 8 := by
  rw [rowMoment_succ]
  congr 1
  cases keep <;> norm_num [Finset.sum_range_succ, move, Nat.testBit] <;> ring

private theorem row_two_full (keep : Bool) (n : Nat) (z : ℝ) :
    rowMoment keep (n+1) 2 z =
      (2*z^2 * rowMoment keep n 0 z + (if keep then 2*z else 2+2*z) * rowMoment keep n 1 z +
        2 * rowMoment keep n 2 z + (if keep then 2 * rowMoment keep n 3 z else 0)) / 8 := by
  rw [rowMoment_succ]
  congr 1
  cases keep <;> norm_num [Finset.sum_range_succ, move, Nat.testBit] <;> ring

private theorem row_three_eq_two (keep : Bool) (n : Nat) (z : ℝ) :
    rowMoment keep n 3 z = rowMoment keep n 2 z := by
  cases n with
  | zero => rw [rowMoment_zero, rowMoment_zero]
  | succ n =>
    rw [rowMoment_succ keep n 3 z, row_two_full]
    congr 1
    cases keep <;> norm_num [Finset.sum_range_succ, move, Nat.testBit] <;> ring

private theorem row_one_succ (keep : Bool) (n : Nat) (z : ℝ) :
    rowMoment keep (n+1) 1 z =
      (z^2 * rowMoment keep n 0 z + (if keep then 2+3*z else 3+3*z) * rowMoment keep n 1 z +
        (if keep then 2 else 1) * rowMoment keep n 2 z) / 8 := by
  rw [row_one_full, row_three_eq_two]
  congr 1
  cases keep <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

private theorem row_two_succ (keep : Bool) (n : Nat) (z : ℝ) :
    rowMoment keep (n+1) 2 z =
      (2*z^2 * rowMoment keep n 0 z + (if keep then 2*z else 2+2*z) * rowMoment keep n 1 z +
        (if keep then 4 else 2) * rowMoment keep n 2 z) / 8 := by
  rw [row_two_full, row_three_eq_two]
  congr 1
  cases keep <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

private noncomputable def price (keep : Bool) (n d : Nat) : ℝ :=
  ((List.range (8^n)).map (fun word =>
    2 ^ (2*n - (gain keep n word - d)))).sum

private theorem transferListSum {α : Type*} [AddCommMonoid α] (N : Nat) (f : Nat → α) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem price_normalized (keep : Bool) (n d : Nat) :
    (price keep n d : ℝ) / (2:ℝ)^(5*n) =
      (∑ w ∈ Finset.range (8^n), (1/2:ℝ) ^ (gain keep n w - d)) / (8:ℝ)^n := by
  simp only [price, transferListSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  have hle : gain keep n w - d ≤ 2*n :=
    (Nat.sub_le ..).trans (gain_bound keep n w)
  have hd : (2:ℝ)^(5*n) = (2:ℝ)^(2*n) * (8:ℝ)^n := by
    rw [show 5*n = 2*n + 3*n by omega, pow_add, pow_mul (2:ℝ) 3 n]
    norm_num
  rw [hd, pow_sub₀ (2:ℝ) (by norm_num) hle, one_div, inv_pow]
  field_simp

private noncomputable def root (keep : Bool) (z : ℝ) : ℝ :=
  if keep then (6 + 3*z + Real.sqrt (4 + 4*z + 25*z^2 + 16*z^3))/16
  else (5 + 3*z + Real.sqrt (9 + 14*z + 25*z^2 + 16*z^3))/16

private noncomputable def cost (keep : Bool) (a z : ℝ) : ℝ :=
  Real.log (root keep z) - a * Real.log z

private noncomputable def logRoot (keep : Bool) (s : ℝ) : ℝ :=
  Real.log (root keep (Real.exp s))

private def rootRadicand (keep : Bool) (z : ℝ) : ℝ :=
  (if keep then 4 else 9) + (if keep then 4 else 14)*z + 25*z^2 + 16*z^3

private theorem rootRadicand_pos (keep : Bool) {z : ℝ} (hz : 0 < z) :
    0 < rootRadicand keep z := by
  cases keep <;> simp [rootRadicand] <;> positivity

private theorem root_pos (keep : Bool) {z : ℝ} (hz : 0 < z) : 0 < root keep z := by
  cases keep <;> simp [root] <;> positivity

private theorem root_one (keep : Bool) : root keep 1 = 1 := by
  cases keep <;> norm_num [root]

private theorem root_hasDerivAt (keep : Bool) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (root keep)
      ((3 + ((if keep then 4 else 14) + 50*z + 48*z^2) /
        (2 * Real.sqrt (rootRadicand keep z))) / 16) z := by
  let b : ℝ := if keep then 4 else 14
  let c : ℝ := if keep then 4 else 9
  let k : ℝ := if keep then 6 else 5
  have hid := hasDerivAt_id' z
  have hd : HasDerivAt (rootRadicand keep) (b + 50*z + 48*z^2) z := by
    convert ((((hid.const_mul b).const_add c).add ((hid.pow 2).const_mul 25)).add
      ((hid.pow 3).const_mul 16)) using 1
    · funext x
      rfl
    · ring
  have h := (((hid.const_mul 3).const_add k).add
    (hd.sqrt (rootRadicand_pos keep hz).ne')).div_const 16
  convert h using 1
  · funext x
    cases keep <;> rfl
  · simp [b]

private theorem logRoot_hasDerivAt (keep : Bool) (s : ℝ) :
    HasDerivAt (logRoot keep)
      ((3 + ((if keep then 4 else 14) + 50 * Real.exp s + 48 * (Real.exp s)^2) /
        (2 * Real.sqrt (rootRadicand keep (Real.exp s)))) / 16 /
        root keep (Real.exp s) * Real.exp s) s := by
  have hz := Real.exp_pos s
  exact (((root_hasDerivAt keep hz).log (root_pos keep hz).ne').comp s
    (Real.hasDerivAt_exp s))

private theorem logRoot_differentiable (keep : Bool) : Differentiable ℝ (logRoot keep) :=
  fun s => (logRoot_hasDerivAt keep s).differentiableAt

private theorem cost_minimum (keep : Bool) (a : ℝ) :
    ∃ z ∈ Icc (1/2 : ℝ) 1, IsMinOn (cost keep a) (Icc (1/2 : ℝ) 1) z := by
  apply isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num))
  intro z hz
  have hp : 0 < z := lt_of_lt_of_le (by norm_num) hz.1
  exact (((root_hasDerivAt keep hp).log (root_pos keep hp).ne').sub
    ((Real.hasDerivAt_log hp.ne').const_mul a)).continuousAt.continuousWithinAt

private theorem logRoot_true_hasDerivAt_zero : HasDerivAt (logRoot true) (9/14) 0 := by
  have hd := logRoot_hasDerivAt true 0
  norm_num [Real.exp_zero, root_one, rootRadicand] at hd ⊢
  exact hd

private theorem logRoot_true_hasDerivAt_half :
    HasDerivAt (logRoot true) ((3*Real.sqrt 57+41)/(15*Real.sqrt 57+57))
      (Real.log (1/2)) := by
  have hd := logRoot_hasDerivAt true (Real.log (1/2))
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 1/2)] at hd
  have hs : Real.sqrt (rootRadicand true (1/2)) = Real.sqrt 57 / 2 := by
    rw [show rootRadicand true (1/2) = (1/4 : ℝ) * 57 by norm_num [rootRadicand],
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1/4)]
    norm_num
    ring
  have hr : root true (1/2) = (15 + Real.sqrt 57) / 32 := by
    change (6 + 3*(1/2) + Real.sqrt (rootRadicand true (1/2)))/16 = _
    rw [hs]
    ring
  have hden : (15 + Real.sqrt 57) * Real.sqrt 57 = 15 * Real.sqrt 57 + 57 := by
    calc
      _ = 15 * Real.sqrt 57 + (Real.sqrt 57)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 57)]
  convert hd using 1
  rw [hs, hr, ← hden]
  norm_num
  field_simp (disch := positivity)
  ring

private theorem root_true_lt_false {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    root true z < root false z := by
  let A := rootRadicand true z
  let B := rootRadicand false z
  have hA : 0 ≤ A := (rootRadicand_pos true hz).le
  have hz2 : z^2 < 1 := by nlinarith [mul_pos hz (sub_pos.mpr hz1)]
  have hprod := mul_neg_of_pos_of_neg hz (sub_neg.mpr hz2)
  have hs : Real.sqrt A < 2 + 5*z := (Real.sqrt_lt' (by positivity)).2 (by
    dsimp [A, rootRadicand]
    nlinarith only [hprod])
  have hdiff : B = A + 5 + 10*z := by
    dsimp [A, B, rootRadicand]
    ring
  have hsq : (Real.sqrt A + 1)^2 < B := by
    nlinarith only [hs, hdiff, Real.sq_sqrt hA]
  have h := Real.sqrt_lt_sqrt (sq_nonneg (Real.sqrt A + 1)) hsq
  rw [Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt A + 1)] at h
  change (6 + 3*z + Real.sqrt A)/16 < (5 + 3*z + Real.sqrt B)/16
  linarith only [h]

private theorem cost_one (keep : Bool) (a : ℝ) : cost keep a 1 = 0 := by
  simp [cost, root_one]

private theorem cost_true_lt_false (a : ℝ) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    cost true a z < cost false a z :=
  sub_lt_sub_right (Real.log_lt_log (root_pos true hz) (root_true_lt_false hz hz1)) _

private theorem log_mem_costInterval {z : ℝ} (hz : z ∈ Icc (1/2 : ℝ) 1) :
    Real.log z ∈ Icc (Real.log (1/2)) 0 := by
  have hp : 0 < z := lt_of_lt_of_le (by norm_num) hz.1
  exact ⟨Real.log_le_log (by norm_num) hz.1, by simpa using Real.log_le_log hp hz.2⟩

private theorem exp_mem_costInterval {s : ℝ} (hs : s ∈ Icc (Real.log (1/2)) 0) :
    Real.exp s ∈ Icc (1/2 : ℝ) 1 := by
  constructor
  · simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 1/2)] using Real.exp_le_exp.mpr hs.1
  · simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hs.2

private theorem cost_isMinOn_log_iff {keep : Bool} {a z : ℝ}
    (hz : z ∈ Icc (1/2 : ℝ) 1) :
    IsMinOn (cost keep a) (Icc (1/2 : ℝ) 1) z ↔
      IsMinOn (fun s => logRoot keep s - a*s) (Icc (Real.log (1/2)) 0) (Real.log z) := by
  have hp : 0 < z := lt_of_lt_of_le (by norm_num) hz.1
  simp only [isMinOn_iff]
  constructor
  · intro h s hs
    simpa [logRoot, cost, Real.exp_log hp, Real.log_exp] using
      h (Real.exp s) (exp_mem_costInterval hs)
  · intro h y hy
    have hpy : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
    simpa [logRoot, cost, Real.exp_log hp, Real.exp_log hpy] using
      h (Real.log y) (log_mem_costInterval hy)

private theorem left_cost_min_iff {f : ℝ → ℝ} {l u m a : ℝ} (hlu : l < u)
    (hd : HasDerivAt f m l) (hs : ∀ t, f l + (t-l)*m ≤ f t) :
    IsMinOn (fun s => f s - a*s) (Icc l u) l ↔ a ≤ m := by
  constructor
  · intro hmin
    have hseg := (convex_Icc (𝕜 := ℝ) l u).segment_subset
      (left_mem_Icc.mpr hlu.le) (right_mem_Icc.mpr hlu.le)
    have hf := hd.sub ((hasDerivAt_id' l).const_mul a)
    have h := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
      hf.hasDerivWithinAt.hasFDerivWithinAt (sub_mem_posTangentConeAt_of_segment_subset hseg)
    have hp : 0 ≤ (u-l)*(m-a) := by
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_one] using h
    by_contra! hma
    exact (not_lt_of_ge hp) (mul_neg_of_pos_of_neg (sub_pos.mpr hlu) (sub_neg.mpr hma))
  · intro ha
    rw [isMinOn_iff]
    intro t ht
    have hp := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ha)
    linarith only [hs t, hp]

private theorem right_cost_min_iff {f : ℝ → ℝ} {l u m a : ℝ} (hlu : l < u)
    (hd : HasDerivAt f m u) (hs : ∀ t, f u + (t-u)*m ≤ f t) :
    IsMinOn (fun s => f s - a*s) (Icc l u) u ↔ m ≤ a := by
  constructor
  · intro hmin
    have hseg := (convex_Icc (𝕜 := ℝ) l u).segment_subset
      (right_mem_Icc.mpr hlu.le) (left_mem_Icc.mpr hlu.le)
    have hf := hd.sub ((hasDerivAt_id' u).const_mul a)
    have h := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
      hf.hasDerivWithinAt.hasFDerivWithinAt (sub_mem_posTangentConeAt_of_segment_subset hseg)
    have hp : 0 ≤ (l-u)*(m-a) := by
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_one] using h
    by_contra! ham
    exact (not_lt_of_ge hp) (mul_neg_of_neg_of_pos (sub_neg.mpr hlu) (sub_pos.mpr ham))
  · intro ha
    rw [isMinOn_iff]
    intro t ht
    have hp := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ht.2) (sub_nonpos.mpr ha)
    linarith only [hs t, hp]

private theorem rate_eq_cost_iff {keep : Bool} {a r x : ℝ}
    (hr : ∃ z ∈ Icc (1/2 : ℝ) 1, r = cost keep a z ∧
      ∀ y ∈ Icc (1/2 : ℝ) 1, r ≤ cost keep a y) (hx : x ∈ Icc (1/2 : ℝ) 1) :
    r = cost keep a x ↔ IsMinOn (cost keep a) (Icc (1/2 : ℝ) 1) x := by
  obtain ⟨z, hz, heq, hle⟩ := hr
  rw [isMinOn_iff]
  constructor
  · intro h y hy
    rw [← h]
    exact hle y hy
  · intro h
    refine le_antisymm (hle x hx) ?_
    rw [heq]
    exact h z hz

private theorem rate_cutoffs (a : ℝ) (rate : Bool → ℝ)
    (hSupport : ∀ s t, logRoot true s + (t-s) * deriv (logRoot true) s ≤ logRoot true t)
    (hRate : ∀ keep, ∃ z ∈ Icc (1/2 : ℝ) 1, rate keep = cost keep a z ∧
      ∀ y ∈ Icc (1/2 : ℝ) 1, rate keep ≤ cost keep a y) :
    (rate true < rate false ↔ a < 9/14) ∧
      (rate true = 0 ↔ 9/14 ≤ a) ∧
      (rate true = cost true a (1/2) ↔ a ≤ (3*Real.sqrt 57+41)/(15*Real.sqrt 57+57)) := by
  have hhalf : (1/2 : ℝ) ∈ Icc (1/2 : ℝ) 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc (1/2 : ℝ) 1 := by norm_num
  have hlog : Real.log (1/2) < 0 := by
    rw [← Real.log_one]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hright : rate true = 0 ↔ 9/14 ≤ a := by
    rw [← cost_one true a, rate_eq_cost_iff (hRate true) hone, cost_isMinOn_log_iff hone,
      Real.log_one]
    refine right_cost_min_iff hlog logRoot_true_hasDerivAt_zero ?_
    intro t
    simpa only [logRoot_true_hasDerivAt_zero.deriv] using hSupport 0 t
  have hleft : rate true = cost true a (1/2) ↔ a ≤ (3*Real.sqrt 57+41)/(15*Real.sqrt 57+57) := by
    rw [rate_eq_cost_iff (hRate true) hhalf, cost_isMinOn_log_iff hhalf]
    refine left_cost_min_iff hlog logRoot_true_hasDerivAt_half ?_
    intro t
    simpa only [logRoot_true_hasDerivAt_half.deriv] using hSupport (Real.log (1/2)) t
  obtain ⟨_, _, _, hminT⟩ := hRate true
  obtain ⟨zF, hzF, hrF, hminF⟩ := hRate false
  have htrue_le_zero : rate true ≤ 0 := by simpa only [cost_one] using hminT 1 hone
  have hcompare : rate true ≤ cost true a zF := hminT zF hzF
  have hzFpos : 0 < zF := lt_of_lt_of_le (by norm_num) hzF.1
  refine ⟨?_, hright, hleft⟩
  constructor
  · intro hlt
    by_contra! ha
    have hzero := hright.mpr ha
    have hfalse_le_zero : rate false ≤ 0 := by simpa only [cost_one] using hminF 1 hone
    rw [hzero] at hlt
    exact (not_lt_of_ge hfalse_le_zero) hlt
  · intro ha
    rcases hzF.2.lt_or_eq with hzFlt | rfl
    · rw [hrF]
      exact hcompare.trans_lt (cost_true_lt_false a hzFpos hzFlt)
    · rw [hrF, cost_one]
      exact lt_of_le_of_ne htrue_le_zero (fun heq => ha.not_ge (hright.mp heq))

private def avg (n : ℕ) (S : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ w ∈ S, f w) / (8:ℝ)^n

private def words (n : ℕ) : Finset ℕ := Finset.range (8^n)

private def cumulant (g : ℕ → ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  avg n (words n) (fun w => Real.exp (s * g n w))

private lemma words_nonempty (n : ℕ) : (words n).Nonempty := by
  exact ⟨0, Finset.mem_range.mpr (by positivity)⟩

private lemma avg_pos {n : ℕ} {S : Finset ℕ} (hS : S.Nonempty) {f : ℕ → ℝ}
    (hf : ∀ w ∈ S, 0 < f w) : 0 < avg n S f := by
  exact div_pos (Finset.sum_pos hf hS) (by positivity)

private lemma cumulant_pos (g : ℕ → ℕ → ℝ) (n : ℕ) (s : ℝ) :
    0 < cumulant g n s := by
  exact avg_pos (words_nonempty n) fun _ _ => Real.exp_pos _

private lemma avg_mono {n : ℕ} {S T : Finset ℕ} (hst : S ⊆ T)
    {f h : ℕ → ℝ} (hh : ∀ w ∈ T, 0 ≤ h w) (hfh : ∀ w ∈ S, f w ≤ h w) :
    avg n S f ≤ avg n T h := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (Finset.sum_le_sum hfh).trans (Finset.sum_le_sum_of_subset_of_nonneg hst fun w hw _ => hh w hw)

private lemma avg_scale (n : ℕ) (S : Finset ℕ) (c : ℝ) (f : ℕ → ℝ) :
    avg n S (fun w => c * f w) = c * avg n S f := by
  rw [avg, avg, ← Finset.mul_sum, mul_div_assoc]

private lemma eventually_nat_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
  eventually_gt_atTop 0

private lemma const_div_nat (c : ℝ) :
    Tendsto (fun n : ℕ => c / (n:ℝ)) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat c

private lemma quarter_of_log_gap {A B : ℕ → ℝ} {a b c : ℝ}
    (hA : ∀ n, 0 < A n) (hB : ∀ n, 0 < B n)
    (ha : Tendsto (fun n => Real.log (A n) / (n:ℝ)) atTop (𝓝 a))
    (hb : Tendsto (fun n => Real.log (B n) / (n:ℝ)) atTop (𝓝 b))
    (hc : a - b < c) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(n:ℝ)*c) * A n ≤ B n / 4 := by
  have hlim : Tendsto (fun n : ℕ =>
      (Real.log (A n) - Real.log (B n) + Real.log 4) / (n:ℝ)) atTop (𝓝 (a - b)) := by
    simpa only [add_div, sub_div, add_zero] using (ha.sub hb).add (const_div_nat (Real.log 4))
  filter_upwards [hlim.eventually_lt_const hc, eventually_nat_pos] with n hn hnp
  have hn' := (div_lt_iff₀ (Nat.cast_pos.mpr hnp : (0:ℝ) < n)).mp hn
  apply (Real.log_le_log_iff (mul_pos (Real.exp_pos _) (hA n)) (div_pos (hB n) (by norm_num))).mp
  rw [Real.log_mul (Real.exp_pos _).ne' (hA n).ne', Real.log_exp,
    Real.log_div (hB n).ne' (by norm_num : (4:ℝ) ≠ 0)]
  linarith

private lemma find_tilt_steps {F : ℝ → ℝ} {s p e : ℝ}
    (hd : HasDerivAt F p s) (he : 0 < e) :
    (∃ q > 0, F (s+q) - F s < q*(p+e)) ∧
    (∃ q < 0, F (s+q) - F s < q*(p-e)) := by
  have hp : ∀ᶠ q : ℝ in 𝓝[>] (0:ℝ), q⁻¹ * (F (s+q) - F s) < p+e :=
    hd.tendsto_slope_zero_right.eventually_lt_const (by linarith)
  have hm : ∀ᶠ q : ℝ in 𝓝[<] (0:ℝ), p-e < q⁻¹ * (F (s+q) - F s) :=
    hd.tendsto_slope_zero_left.eventually_const_lt (by linarith)
  obtain ⟨q, hq, hpq⟩ := (Filter.Eventually.and (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ)) hp).exists
  obtain ⟨r, hr, hmr⟩ := (Filter.Eventually.and (self_mem_nhdsWithin : Iio (0:ℝ) ∈ 𝓝[<] (0:ℝ)) hm).exists
  change 0 < q at hq
  change r < 0 at hr
  refine ⟨⟨q, hq, ?_⟩, ⟨r, hr, ?_⟩⟩
  · rw [← div_eq_inv_mul] at hpq
    simpa [mul_comm] using (div_lt_iff₀ hq).mp hpq
  · rw [← div_eq_inv_mul] at hmr
    simpa [mul_comm] using (lt_div_iff_of_neg hr).mp hmr

private lemma tilted_tail {g : ℕ → ℕ → ℝ} {F : ℝ → ℝ} {s q u : ℝ}
    (hM : ∀ x, Tendsto (fun n => Real.log (cumulant g n x) / (n:ℝ)) atTop (𝓝 (F x)))
    (hgap : F (s+q) - F s < q*u) :
    ∀ᶠ n : ℕ in atTop,
      avg n ((words n).filter fun w => (n:ℝ)*(q*u) < q*g n w)
        (fun w => Real.exp (s*g n w)) ≤ cumulant g n s / 4 := by
  filter_upwards [quarter_of_log_gap (fun n => cumulant_pos g n (s+q))
    (fun n => cumulant_pos g n s) (hM (s+q)) (hM s) hgap] with n hquarter
  apply le_trans _ hquarter
  unfold cumulant
  rw [← avg_scale]
  apply avg_mono (Finset.filter_subset _ _) (fun _ _ => by positivity)
  intro w hw
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := (Finset.mem_filter.mp hw).2
  linarith only [h, show (s+q)*g n w = s*g n w + q*g n w by ring]

private def band (g : ℕ → ℕ → ℝ) (p e : ℝ) (n : ℕ) : Finset ℕ :=
  by classical exact (words n).filter fun w => g n w / (n:ℝ) ∈ Icc (p-e) (p+e)

private lemma band_mass {g : ℕ → ℕ → ℝ} {F : ℝ → ℝ} {s p e : ℝ}
    (hM : ∀ x, Tendsto (fun n => Real.log (cumulant g n x) / (n:ℝ)) atTop (𝓝 (F x)))
    (hd : HasDerivAt F p s) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop,
      cumulant g n s / 2 ≤ avg n (band g p e n) (fun w => Real.exp (s*g n w)) := by
  classical
  obtain ⟨⟨q, hq, hgq⟩, ⟨r, hr, hgr⟩⟩ := find_tilt_steps hd he
  filter_upwards [tilted_tail hM hgq, tilted_tail hM hgr, eventually_nat_pos] with n hhi hlo hn
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hpart : cumulant g n s = avg n (band g p e n) (fun w => Real.exp (s*g n w)) +
      avg n ((words n).filter fun w => (n:ℝ)*(q*(p+e)) < q*g n w) (fun w => Real.exp (s*g n w)) +
      avg n ((words n).filter fun w => (n:ℝ)*(r*(p-e)) < r*g n w) (fun w => Real.exp (s*g n w)) := by
    unfold cumulant band avg
    simp only [Finset.sum_filter, ← add_div, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    have hqEq : (n:ℝ)*(q*(p+e)) < q*g n w ↔ p+e < g n w / (n:ℝ) := by
      rw [lt_div_iff₀ hn', show (n:ℝ)*(q*(p+e)) = q*((p+e)*n) by ring,
        mul_lt_mul_iff_right₀ hq]
    have hrEq : (n:ℝ)*(r*(p-e)) < r*g n w ↔ g n w / (n:ℝ) < p-e := by
      rw [div_lt_iff₀ hn', show (n:ℝ)*(r*(p-e)) = r*((p-e)*n) by ring]
      constructor
      · intro hh
        by_contra! hb
        exact (not_lt_of_ge (mul_le_mul_of_nonpos_left hb hr.le)) hh
      · intro hh
        exact mul_lt_mul_of_neg_left hh hr
    simp only [hqEq, hrEq]
    rcases lt_or_ge (g n w / (n:ℝ)) (p-e) with h | h
    · have h' : ¬ p+e < g n w / (n:ℝ) := by linarith
      simp [Set.mem_Icc, h.not_ge, h, h']
    · rcases lt_or_ge (p+e) (g n w / (n:ℝ)) with h' | h'
      · simp [Set.mem_Icc, h, h.not_gt, h', h'.not_ge]
      · simp [Set.mem_Icc, h, h', h.not_gt, h'.not_gt]
  linarith only [hhi, hlo, hpart]

private def laplace (φ : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  avg n (words n) (fun w => Real.exp (φ n w))

private lemma laplace_pos (φ : ℕ → ℕ → ℝ) (n : ℕ) : 0 < laplace φ n := by
  exact avg_pos (words_nonempty n) fun _ _ => Real.exp_pos _

private lemma tilt_lower {g φ : ℕ → ℕ → ℝ} {F : ℝ → ℝ} {s p l : ℝ}
    (hM : ∀ x, Tendsto (fun n => Real.log (cumulant g n x) / (n:ℝ)) atTop (𝓝 (F x)))
    (hd : HasDerivAt F p s)
    (hpoint : ∀ ε > 0, ∃ e > 0, ∀ᶠ n : ℕ in atTop, ∀ w ∈ band g p e n,
      s*g n w + (n:ℝ)*(l-ε) ≤ φ n w) :
    ∀ b < F s + l, ∀ᶠ n : ℕ in atTop, b < Real.log (laplace φ n) / (n:ℝ) := by
  intro b hb
  let ε : ℝ := (F s + l - b)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨e, he, hpoint⟩ := hpoint ε hε
  have hlim : Tendsto (fun n : ℕ =>
      Real.log (cumulant g n s) / (n:ℝ) - Real.log 2 / (n:ℝ) + (l-ε))
      atTop (𝓝 (F s + (l-ε))) := by
    simpa only [sub_zero] using ((hM s).sub (const_div_nat (Real.log 2))).add_const (l-ε)
  have hb' : b < F s + (l-ε) := by dsimp [ε]; linarith
  filter_upwards [hlim.eventually_const_lt hb', band_mass hM hd he, hpoint, eventually_nat_pos]
    with n hbound hmass hpn hn
  have hscale : Real.exp ((n:ℝ)*(l-ε)) * avg n (band g p e n) (fun w => Real.exp (s*g n w))
      ≤ laplace φ n := by
    rw [← avg_scale]
    unfold laplace
    apply avg_mono (Finset.filter_subset _ _) (fun _ _ => by positivity)
    intro w hw
    rw [← Real.exp_add, add_comm ((n:ℝ)*(l-ε))]
    exact Real.exp_le_exp.mpr (hpn w hw)
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) (half_pos (cumulant_pos g n s)))
    ((mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le).trans hscale)
  rw [Real.log_mul (Real.exp_pos _).ne' (half_pos (cumulant_pos g n s)).ne',
    Real.log_exp, Real.log_div (cumulant_pos g n s).ne' (by norm_num : (2:ℝ) ≠ 0)] at hlog
  apply (lt_div_iff₀ (Nat.cast_pos.mpr hn : (0:ℝ) < n)).mpr
  have hbound' : b < (Real.log (cumulant g n s) - Real.log 2 + (l-ε)*(n:ℝ)) / (n:ℝ) := by
    rw [add_div, sub_div, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
    exact hbound
  have := (lt_div_iff₀ (Nat.cast_pos.mpr hn : (0:ℝ) < n)).mp hbound'
  linarith

private lemma band_error {g : ℕ → ℕ → ℝ} {p e : ℝ} {n w : ℕ}
    (hw : w ∈ band g p e n) : |g n w / (n:ℝ) - p| ≤ e := by
  have h := (Finset.mem_filter.mp hw).2
  rw [abs_le]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private lemma scaled_error {x p k e : ℝ} (h : |x - p| ≤ e) :
    |k*x - k*p| ≤ |k| * e := by
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

private lemma supporting_from_tilt {g : ℕ → ℕ → ℝ} {F : ℝ → ℝ} {s p : ℝ}
    (hM : ∀ x, Tendsto (fun n => Real.log (cumulant g n x) / (n:ℝ)) atTop (𝓝 (F x)))
    (hd : HasDerivAt F p s) (t : ℝ) :
    F s + (t-s)*p ≤ F t := by
  apply le_of_forall_lt_imp_le_of_dense
  intro b hb
  have hl := tilt_lower (φ := fun n w => t*g n w) (l := (t-s)*p) hM hd ?_ b hb
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds (hM t) (hl.mono fun _ h => h.le)
  · intro ε hε
    let e := ε / (|t-s|+1)
    refine ⟨e, div_pos hε (by positivity), ?_⟩
    filter_upwards [eventually_nat_pos] with n hn w hw
    have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn
    have herr := (abs_le.mp (scaled_error (k := t-s) (band_error hw))).1
    have hel : |t - s| * e ≤ ε := by
      dsimp [e]
      rw [← mul_div_assoc]
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    have hscaled : (t-s)*p-ε ≤ (t-s)*(g n w / (n:ℝ)) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hscaled hnr.le
    rw [← mul_div_assoc, mul_div_cancel₀ _ hnr.ne'] at hmul
    linarith

private noncomputable def coeffA (keep : Bool) (z : ℝ) : ℝ :=
  if keep then 2+3*z else 3+3*z

private def coeffK (keep : Bool) : ℝ := if keep then 2 else 1

private noncomputable def coeffB (keep : Bool) (z : ℝ) : ℝ :=
  if keep then 2*z else 2+2*z

private noncomputable def transferOp (keep : Bool) (z : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![((4+4*z) * v 1) / 8,
    (z^2*v 0 + coeffA keep z*v 1 + coeffK keep*v 2) / 8,
    (2*z^2*v 0 + coeffB keep z*v 1 + (2*coeffK keep)*v 2) / 8]

private lemma tr_mono (keep : Bool) (z : ℝ) (hz : 0 < z) : Monotone (transferOp keep z) := by
  intro u v huv j
  have h0 := huv (0 : Fin 3)
  have h1 := huv (1 : Fin 3)
  have h2 := huv (2 : Fin 3)
  cases keep <;> fin_cases j <;> simp [transferOp, coeffA, coeffK, coeffB] <;> gcongr

private lemma tr_scale (keep : Bool) (z c : ℝ) (v : Fin 3 → ℝ) :
    transferOp keep z (c • v) = c • transferOp keep z v := by
  funext j
  fin_cases j <;> simp [transferOp, Pi.smul_apply, smul_eq_mul] <;> ring

private noncomputable def rowVec (keep : Bool) (n : ℕ) (z : ℝ) (j : Fin 3) : ℝ :=
  rowMoment keep n j.val z

private lemma rowVec_succ (keep : Bool) (n : ℕ) (z : ℝ) :
    rowVec keep (n+1) z = transferOp keep z (rowVec keep n z) := by
  funext j
  fin_cases j
  · simpa [rowVec, transferOp] using row_zero_succ keep n z
  · simpa [rowVec, transferOp, coeffA, coeffK] using row_one_succ keep n z
  · cases keep
    · simpa [rowVec, transferOp, coeffB, coeffK, Bool.false_eq_true] using row_two_succ false n z
    · norm_num [rowVec, transferOp, coeffB, coeffK] at ⊢
      simpa using row_two_succ true n z

private lemma root_quadratic (keep : Bool) (z : ℝ) (hz : 0 < z) :
    let eig := 8*root keep z
    2+2*z < eig ∧ eig^2 - (coeffA keep z + 2*coeffK keep)*eig +
      (coeffK keep-z^2)*(4+4*z) = 0 := by
  dsimp only
  cases keep
  · simp only [root, coeffA, coeffK, Bool.false_eq_true, ↓reduceIte]
    have hD : 0 ≤ 9+14*z+25*z^2+16*z^3 := by positivity
    have hs := Real.sq_sqrt hD
    have hsz : z ≤ Real.sqrt (9+14*z+25*z^2+16*z^3) := by
      by_contra! h
      have h' := sq_lt_sq' (by linarith [Real.sqrt_nonneg (9+14*z+25*z^2+16*z^3)] :
        -z < Real.sqrt (9+14*z+25*z^2+16*z^3)) h
      nlinarith [pow_nonneg hz.le 3]
    constructor <;> nlinarith
  · simp only [root, coeffA, coeffK, ↓reduceIte]
    have hD : 0 ≤ 4+4*z+25*z^2+16*z^3 := by positivity
    have hs := Real.sq_sqrt hD
    have hsz : z ≤ Real.sqrt (4+4*z+25*z^2+16*z^3) := by
      by_contra! h
      have h' := sq_lt_sq' (by linarith [Real.sqrt_nonneg (4+4*z+25*z^2+16*z^3)] :
        -z < Real.sqrt (4+4*z+25*z^2+16*z^3)) h
      nlinarith [pow_nonneg hz.le 3]
    constructor <;> nlinarith

private lemma eigen_bounds (keep : Bool) (z : ℝ) (hz : 0 < z) :
    ∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ n,
      l * (root keep z)^n ≤ moment keep n z ∧ moment keep n z ≤ u * (root keep z)^n := by
  let R := root keep z
  let eig := 8*R
  obtain ⟨hle, hquad⟩ := root_quadratic keep z hz
  change 2+2*z < eig at hle
  change eig^2 - (coeffA keep z + 2*coeffK keep)*eig + (coeffK keep-z^2)*(4+4*z) = 0 at hquad
  have heigpos : 0 < eig := by linarith
  let x := (4+4*z)/eig
  have hx : 0 < x := div_pos (by positivity) heigpos
  have hx' : x < 2 := (div_lt_iff₀ heigpos).mpr (by linarith)
  have hx0 : eig*x = 4+4*z := by dsimp only [x]; field_simp
  have he1 : z^2*x + coeffA keep z + coeffK keep*(2-x) = eig := by
    apply (mul_right_inj' heigpos.ne').mp
    dsimp [x]
    field_simp
    nlinarith only [hquad]
  have he2 : 2*z^2*x + coeffB keep z + (2*coeffK keep)*(2-x) = eig*(2-x) := by
    have hAB : coeffB keep z = 2*coeffA keep z - (4+4*z) := by
      cases keep <;> simp [coeffA, coeffB] <;> ring
    rw [hAB]
    linear_combination 2*he1 + hx0
  let v : Fin 3 → ℝ := ![x, 1, 2-x]
  have hv2 (j : Fin 3) : v j ≤ 2 := by fin_cases j <;> simp [v] <;> linarith
  have heig : transferOp keep z v = R • v := by
    funext j
    fin_cases j <;> simp [transferOp, v, Pi.smul_apply, smul_eq_mul] <;>
      dsimp only [eig] at he1 he2 hx0 <;> linarith
  let C := 1 + 1/x + 1/(2-x)
  have hy : 0 < 2-x := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hu (j : Fin 3) : 1 ≤ C*v j := by
    fin_cases j <;> simp [v]
    · calc
        1 = (1/x)*x := by field_simp
        _ ≤ C*x := by
          apply mul_le_mul_of_nonneg_right _ hx.le
          dsimp [C]
          linarith [one_div_pos.mpr hy]
    · dsimp [C]
      have := one_div_pos.mpr hx
      have := one_div_pos.mpr hy
      linarith
    · calc
        1 = (1/(2-x))*(2-x) := by field_simp
        _ ≤ C*(2-x) := by
          apply mul_le_mul_of_nonneg_right _ hy.le
          dsimp [C]
          have := one_div_pos.mpr hx
          linarith
  have hprop (n : ℕ) : ((1/2*R^n : ℝ) • v) ≤ rowVec keep n z ∧
      rowVec keep n z ≤ ((C*R^n) • v) := by
    induction n with
    | zero =>
      constructor <;> intro j <;> simp [rowVec, rowMoment_zero, Pi.smul_apply, smul_eq_mul]
      · linarith [hv2 j]
      · exact hu j
    | succ n ih =>
      have hscale (c : ℝ) : transferOp keep z ((c*R^n) • v) = (c*R^(n+1)) • v := by
        rw [tr_scale, heig]
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
        ring
      rw [rowVec_succ]
      constructor
      · rw [← hscale]; exact tr_mono keep z hz ih.1
      · rw [← hscale]; exact tr_mono keep z hz ih.2
  refine ⟨(1/2)*x, C*x, by positivity, by positivity, fun n => ⟨?_, ?_⟩⟩
  · have h := (hprop n).1 (0 : Fin 3)
    change ((1/2)*R^n)*x ≤ moment keep n z at h
    convert h using 1
    ring
  · have h := (hprop n).2 (0 : Fin 3)
    change moment keep n z ≤ (C*R^n)*x at h
    convert h using 1
    ring

private lemma cumulant_eq_moment (keep : Bool) (n : ℕ) (s : ℝ) :
    cumulant (fun n w => (gain keep n w : ℝ)) n s = moment keep n (Real.exp s) := by
  unfold cumulant avg words moment
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  change Real.exp (s * (gain keep n w : ℝ)) = Real.exp s ^ gain keep n w
  rw [mul_comm s, Real.exp_nat_mul]

private lemma logMoment_limit (keep : Bool) (s : ℝ) :
    Tendsto (fun n => Real.log (cumulant (fun n w => (gain keep n w : ℝ)) n s) / (n:ℝ))
      atTop (𝓝 (logRoot keep s)) := by
  let z := Real.exp s
  have hz : 0 < z := Real.exp_pos s
  have hρ : 0 < root keep z := by linarith [(root_quadratic keep z hz).1]
  obtain ⟨l, u, hl, hu, hlu⟩ := eigen_bounds keep z hz
  have hlim (c : ℝ) : Tendsto (fun n : ℕ => Real.log c / (n:ℝ) + Real.log (root keep z))
      atTop (𝓝 (logRoot keep s)) := by
    simpa [logRoot, z] using (const_div_nat (Real.log c)).add_const (Real.log (root keep z))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim l) (hlim u)
  · filter_upwards [eventually_nat_pos] with n hn
    rw [cumulant_eq_moment]
    have h := Real.log_le_log (mul_pos hl (pow_pos hρ n)) (hlu n).1
    rw [Real.log_mul hl.ne' (pow_ne_zero _ hρ.ne'), Real.log_pow] at h
    have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
    rw [add_div, mul_comm (n:ℝ), mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))] at hd
    exact hd
  · filter_upwards [eventually_nat_pos] with n hn
    have hpos := cumulant_pos (fun n w => (gain keep n w : ℝ)) n s
    rw [cumulant_eq_moment] at hpos ⊢
    have h := Real.log_le_log hpos (hlu n).2
    rw [Real.log_mul hu.ne' (pow_ne_zero _ hρ.ne'), Real.log_pow] at h
    have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
    rw [add_div, mul_comm (n:ℝ), mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))] at hd
    exact hd

private noncomputable def clip (d g : ℝ) : ℝ := min 0 ((d-g)*Real.log 2)

private lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

private lemma clip_upper {s : ℝ} (hs : s ∈ Icc (-Real.log 2) 0) (d g : ℝ) :
    clip d g ≤ s*(g-d) := by
  rcases le_total d g with h | h
  · have hm := mul_le_mul_of_nonneg_right hs.1 (sub_nonneg.mpr h)
    have hmin := min_le_right (0:ℝ) ((d-g)*Real.log 2)
    unfold clip
    nlinarith only [hm, hmin]
  · exact (min_le_left _ _).trans (mul_nonneg_of_nonpos_of_nonpos hs.2 (sub_nonpos.mpr h))

private lemma clip_mul (c d g : ℝ) (hc : 0 ≤ c) :
    c*clip d g = clip (c*d) (c*g) := by
  unfold clip
  rw [mul_min_of_nonneg _ _ hc, mul_zero]
  ring_nf

private lemma interval_min_signs {F : ℝ → ℝ} {l r s a p : ℝ}
    (hs : s ∈ Icc l r) (hd : HasDerivAt F p s)
    (hm : ∀ t ∈ Icc l r, F s - a*s ≤ F t - a*t) :
    (l < s → p ≤ a) ∧ (s < r → a ≤ p) := by
  have hderiv : HasDerivAt (fun t => F t - a*t) (p-a) s := by
    simpa only [mul_one] using hd.fun_sub ((hasDerivAt_id' s).const_mul a)
  obtain ⟨hleft, hright⟩ := hasDerivAt_iff_tendsto_slope_left_right.mp hderiv
  constructor
  · intro hl
    have hI : Icc l r ∈ 𝓝[<] s := Icc_mem_nhdsLT_of_mem ⟨hl, hs.2⟩
    have hn : ∀ᶠ t : ℝ in 𝓝[<] s, slope (fun t => F t - a*t) s t ≤ 0 := by
      filter_upwards [hI, (self_mem_nhdsWithin : Iio s ∈ 𝓝[<] s)] with t ht ht'
      rw [slope_def_field]
      exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hm t ht)) (sub_nonpos.mpr (le_of_lt ht'))
    have hh := le_of_tendsto hleft hn
    linarith
  · intro hr
    have hI : Icc l r ∈ 𝓝[>] s := Icc_mem_nhdsGT_of_mem ⟨hs.1, hr⟩
    have hn : ∀ᶠ t : ℝ in 𝓝[>] s, 0 ≤ slope (fun t => F t - a*t) s t := by
      filter_upwards [hI, (self_mem_nhdsWithin : Ioi s ∈ 𝓝[>] s)] with t ht ht'
      rw [slope_def_field]
      exact div_nonneg (sub_nonneg.mpr (hm t ht)) (sub_nonneg.mpr (le_of_lt ht'))
    have hh := ge_of_tendsto hright hn
    linarith

private lemma clip_at_min {F : ℝ → ℝ} {s a p : ℝ}
    (hs : s ∈ Icc (-Real.log 2) 0) (hd : HasDerivAt F p s)
    (hm : ∀ t ∈ Icc (-Real.log 2) 0, F s - a*s ≤ F t - a*t) :
    clip a p = s*(p-a) := by
  obtain ⟨hleft, hright⟩ := interval_min_signs hs hd hm
  rcases hs.1.eq_or_lt with hl | hl
  · have hp := hright (by linarith [log_two_pos])
    rw [← hl, clip, min_eq_right (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) log_two_pos.le)]
    ring
  · rcases hs.2.eq_or_lt with hr | hr
    · have hp := hleft hl
      rw [hr, clip, min_eq_left (mul_nonneg (sub_nonneg.mpr hp) log_two_pos.le), zero_mul]
    · have he : p = a := le_antisymm (hleft hl) (hright hr)
      subst p
      simp [clip]

private lemma clipped_limit {g : ℕ → ℕ → ℝ} {F : ℝ → ℝ} {s p a : ℝ} {d : ℕ → ℕ}
    (hM : ∀ x, Tendsto (fun n => Real.log (cumulant g n x) / (n:ℝ)) atTop (𝓝 (F x)))
    (hd : HasDerivAt F p s)
    (hD : Tendsto (fun n => (d n : ℝ) / (n:ℝ)) atTop (𝓝 a))
    (hs : s ∈ Icc (-Real.log 2) 0)
    (hm : ∀ t ∈ Icc (-Real.log 2) 0, F s - a*s ≤ F t - a*t) :
    Tendsto (fun n => Real.log (laplace (fun n w => clip (d n) (g n w)) n) / (n:ℝ))
      atTop (𝓝 (F s - a*s)) := by
  let φ := fun n w => clip (d n : ℝ) (g n w)
  have hclip := clip_at_min hs hd hm
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    have heq : F s + (clip a p-s*p) = F s - a*s := by rw [hclip]; ring
    have hb' : b < F s + (clip a p-s*p) := by simpa [heq] using hb
    apply tilt_lower (φ := φ) (l := clip a p-s*p) hM hd _ b hb'
    intro ε hε
    let e := ε / (2*Real.log 2 + |s| + 1)
    have he : 0 < e := by dsimp [e]; positivity
    have hε' : (2*Real.log 2 + |s|)*e ≤ ε := by
      dsimp [e]
      rw [← mul_div_assoc]
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    refine ⟨e, he, ?_⟩
    filter_upwards [hD.eventually_const_lt (show a-e < a by linarith), eventually_nat_pos]
      with n hd' hn w hw
    have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn
    have hg := band_error hw
    have hsg := (abs_le.mp (scaled_error (k := s) hg)).2
    have hgc : clip a p - 2*Real.log 2*e ≤ clip ((d n:ℝ)/(n:ℝ)) (g n w/(n:ℝ)) := by
      apply le_min
      · have h0 : clip a p ≤ 0 := min_le_left _ _
        nlinarith only [h0, mul_nonneg log_two_pos.le he.le]
      · have h0 : clip a p ≤ (a-p)*Real.log 2 := min_le_right _ _
        have h1 := (abs_le.mp hg).2
        have h2 := mul_le_mul_of_nonneg_right
          (show a-p-2*e ≤ (d n:ℝ)/(n:ℝ)-g n w/(n:ℝ) by linarith) log_two_pos.le
        nlinarith only [h0, h2]
    have hpoint : s*(g n w/(n:ℝ)) + (clip a p-s*p-ε) ≤
        clip ((d n:ℝ)/(n:ℝ)) (g n w/(n:ℝ)) := by nlinarith only [hgc, hsg, hε']
    have hmul := mul_le_mul_of_nonneg_left hpoint hnr.le
    rw [mul_add, ← mul_assoc, mul_comm (n:ℝ) s, mul_assoc,
      mul_div_cancel₀ _ hnr.ne', clip_mul _ _ _ hnr.le,
      mul_div_cancel₀ _ hnr.ne', mul_div_cancel₀ _ hnr.ne'] at hmul
    exact hmul
  · intro b hb
    have hlim : Tendsto (fun n => Real.log (cumulant g n s) / (n:ℝ) - s*((d n:ℝ)/(n:ℝ)))
          atTop (𝓝 (F s - a*s)) := by
      simpa only [mul_comm a s] using (hM s).sub (tendsto_const_nhds.mul hD :
        Tendsto (fun n => s*((d n:ℝ)/(n:ℝ))) atTop (𝓝 (s*a)))
    filter_upwards [hlim.eventually_lt_const hb, eventually_nat_pos] with n hb' hn
    have hupper : laplace φ n ≤ Real.exp (-s*(d n:ℝ)) * cumulant g n s := by
      unfold laplace cumulant
      rw [← avg_scale]
      apply avg_mono (fun _ h => h) (fun _ _ => by positivity)
      intro w _
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [φ]
      nlinarith only [clip_upper hs (d n) (g n w)]
    have hlog := Real.log_le_log (laplace_pos φ n) hupper
    rw [Real.log_mul (Real.exp_pos _).ne' (cumulant_pos g n s).ne', Real.log_exp] at hlog
    have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
    rw [add_comm, add_div, neg_mul, neg_div, mul_div_assoc, ← sub_eq_add_neg] at hdiv
    exact lt_of_le_of_lt hdiv hb'

private lemma exp_clip_nat (d g : ℕ) : Real.exp (clip d g) = (1/2:ℝ)^(g-d) := by
  by_cases h : d ≤ g
  · have h' : (d:ℝ) ≤ g := Nat.cast_le.mpr h
    rw [clip, min_eq_right (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h') log_two_pos.le)]
    have hlog : Real.log (1/2:ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    rw [← Real.exp_log (show (0:ℝ) < 1/2 by norm_num), ← Real.exp_nat_mul, Nat.cast_sub h, hlog]
    congr 1
    ring
  · have h' : (g:ℝ) ≤ d := Nat.cast_le.mpr (by omega)
    rw [clip, min_eq_left (mul_nonneg (sub_nonneg.mpr h') log_two_pos.le), Real.exp_zero,
      show g-d=0 by omega, pow_zero]

private lemma laplace_price (keep : Bool) (n d : ℕ) (D : ℕ → ℕ) (hd : D n = d) :
    laplace (fun n w => clip (D n : ℝ) (gain keep n w : ℝ)) n =
      (price keep n d : ℝ) / (2:ℝ)^(5*n) := by
  simp only [laplace, avg, words, hd, exp_clip_nat, price_normalized]

private theorem result (d : ℕ → ℕ) (a : ℝ) (_ha : 0 ≤ a)
    (hD : Tendsto (fun t : ℕ => (d t : ℝ) / (t : ℝ)) atTop (𝓝 a)) :
    ∃ rate : Bool → ℝ,
      (∀ keep : Bool, Tendsto (fun t : ℕ =>
        Real.log ((price keep t (d t) : ℝ) / (2:ℝ)^(5*t)) / (t:ℝ)) atTop (𝓝 (rate keep)) ∧
        ∃ z : ℝ, z ∈ Icc (1/2 : ℝ) 1 ∧ rate keep = cost keep a z ∧
          ∀ y ∈ Icc (1/2 : ℝ) 1, rate keep ≤ cost keep a y) ∧
      ((rate true < rate false) ↔ a < 9/14) ∧ (rate true = 0 ↔ 9/14 ≤ a) ∧
      (rate true = cost true a (1/2) ↔ a ≤ (3*Real.sqrt 57+41)/(15*Real.sqrt 57+57)) := by
  classical
  let z : Bool → ℝ := fun keep => Classical.choose (cost_minimum keep a)
  have hz (keep : Bool) : z keep ∈ Icc (1/2 : ℝ) 1 := (Classical.choose_spec (cost_minimum keep a)).1
  have hm (keep : Bool) : IsMinOn (cost keep a) (Icc (1/2 : ℝ) 1) (z keep) :=
    (Classical.choose_spec (cost_minimum keep a)).2
  let rate := fun keep => cost keep a (z keep)
  have hRate (keep : Bool) : ∃ y ∈ Icc (1/2 : ℝ) 1,
      rate keep = cost keep a y ∧ ∀ x ∈ Icc (1/2 : ℝ) 1, rate keep ≤ cost keep a x :=
    ⟨z keep, hz keep, rfl, hm keep⟩
  have hSupport (s t : ℝ) : logRoot true s + (t-s)*deriv (logRoot true) s ≤ logRoot true t :=
    supporting_from_tilt (logMoment_limit true) ((logRoot_differentiable true s).hasDerivAt) t
  refine ⟨rate, ?_, rate_cutoffs a rate hSupport hRate⟩
  intro keep
  refine ⟨?_, hRate keep⟩
  have hp : 0 < z keep := lt_of_lt_of_le (by norm_num) (hz keep).1
  have hlog : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  have hs := log_mem_costInterval (hz keep)
  have hmin := (cost_isMinOn_log_iff (hz keep)).mp (hm keep)
  rw [hlog] at hs hmin
  have hlim := clipped_limit (logMoment_limit keep)
    ((logRoot_differentiable keep (Real.log (z keep))).hasDerivAt) hD hs hmin
  have hrate : rate keep = logRoot keep (Real.log (z keep)) - a*Real.log (z keep) := by
    simp [rate, cost, logRoot, Real.exp_log hp]
  rw [hrate]
  refine hlim.congr' (Eventually.of_forall fun n => ?_)
  rw [laplace_price keep n (d n) d rfl]

end Proof

end PEqualNP.Outside.L_meta_25587

theorem PEqualNP.Outside.L_meta_25587 :
  let move := fun (keep : Bool) (mode letter : Nat) =>
    let near := letter.testBit 0
    let far := letter.testBit 1
    let hit := letter.testBit 2
    let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
      ((mode == 3) && near)
    let diagonal := keep && !hit && (((mode == 1) && !near && !far) ||
      (mode == 2) || (mode == 3))
    (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
      hit.toNat + (aligned && hit).toNat)
  let gain := fun (keep : Bool) (n code : Nat) =>
    ((List.range n).foldl (fun (st : Nat × Nat) j =>
      let result := move keep st.1 ((code >>> (3*j)) % 8)
      (result.1, st.2 + result.2)) (0, 0)).2
  let price := fun (keep : Bool) (n d : Nat) =>
    ((List.range (8^n)).map (fun word =>
      2 ^ (2*n - (gain keep n word - d)))).sum
  let root := fun (keep : Bool) (z : ℝ) =>
    if keep then (6+3*z+Real.sqrt (4+4*z+25*z^2+16*z^3))/16
    else (5+3*z+Real.sqrt (9+14*z+25*z^2+16*z^3))/16
  let cost := fun (keep : Bool) (a z : ℝ) => Real.log (root keep z) - a*Real.log z
  ∀ (d : Nat → Nat) (a : ℝ), 0 ≤ a →
    Filter.Tendsto (fun time : Nat => (d time : ℝ) / (time : ℝ)) Filter.atTop (nhds a) →
    ∃ rate : Bool → ℝ,
      (∀ keep : Bool,
        Filter.Tendsto (fun t : Nat =>
          Real.log ((price keep t (d t) : ℝ) / (2 : ℝ)^(5*t)) / (t : ℝ))
          Filter.atTop (nhds (rate keep)) ∧
        ∃ z : ℝ, z ∈ Set.Icc (1/2 : ℝ) 1 ∧ rate keep = cost keep a z ∧
          ∀ y ∈ Set.Icc (1/2 : ℝ) 1, rate keep ≤ cost keep a y) ∧
      ((rate true < rate false) ↔ a < 9/14) ∧
      (rate true = 0 ↔ 9/14 ≤ a) ∧
      (rate true = cost true a (1/2) ↔
        a ≤ (3*Real.sqrt 57+41)/(15*Real.sqrt 57+57)) := by
  exact PEqualNP.Outside.L_meta_25587.result
