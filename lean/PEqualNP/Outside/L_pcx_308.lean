import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_308_aux

open PEqualNP.ProofComplexity

/-! ## Section 1: `Nat.clog 2`, `balanced`, and Branch Dominance -/

section Balanced

private def bal (base m : ℕ) : ℕ :=
  let d := Nat.clog 2 m
  (2 ^ d - m) * base ^ (d - 1) + (2 * m - 2 ^ d) * base ^ d

private lemma pow_pred_lt_of_clog {m : ℕ} (hm : 2 ≤ m) :
    2 ^ (Nat.clog 2 m - 1) < m := by
  have hd : 0 < Nat.clog 2 m := Nat.clog_pos (by decide) (by omega)
  have hlt : Nat.clog 2 m - 1 < Nat.clog 2 m := by omega
  have hle : ¬ m ≤ 2 ^ (Nat.clog 2 m - 1) := by
    intro h
    have := Nat.clog_le_of_le_pow h
    omega
  omega

private lemma le_pow_clog (m : ℕ) : m ≤ 2 ^ Nat.clog 2 m :=
  Nat.le_pow_clog (by decide) m

private lemma clog_add_le {a c : ℕ} (_ha : 1 ≤ a) (_hc : 1 ≤ c) :
    Nat.clog 2 (a + c) ≤ 1 + max (Nat.clog 2 a) (Nat.clog 2 c) := by
  apply Nat.clog_le_of_le_pow
  have h1 : a ≤ 2 ^ Nat.clog 2 a := le_pow_clog a
  have h2 : c ≤ 2 ^ Nat.clog 2 c := le_pow_clog c
  have h3 : 2 ^ Nat.clog 2 a ≤ 2 ^ max (Nat.clog 2 a) (Nat.clog 2 c) :=
    Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  have h4 : 2 ^ Nat.clog 2 c ≤ 2 ^ max (Nat.clog 2 a) (Nat.clog 2 c) :=
    Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  rw [Nat.add_comm 1, pow_succ]
  omega

private lemma bal_one (base : ℕ) : bal base 1 = 1 := by
  simp [bal, Nat.clog_one_right]

private lemma bal_two (base : ℕ) : bal base 2 = 2 * base := by
  have h : Nat.clog 2 2 = 1 := by decide
  simp [bal, h]

private lemma bal_eq_int_of_bounds {base m t : ℕ} (ht : 1 ≤ t)
    (hlo : 2 ^ (t - 1) ≤ m) (hhi : m ≤ 2 ^ t) :
    (bal base m : ℤ) =
      (2 * (base : ℤ) - 1) * (m : ℤ) * (base : ℤ) ^ (t - 1) -
      ((base : ℤ) - 1) * (2 : ℤ) ^ t * (base : ℤ) ^ (t - 1) := by
  by_cases h1 : m = 2 ^ (t - 1)
  · subst h1
    have hclog : Nat.clog 2 (2 ^ (t - 1)) = t - 1 := Nat.clog_pow 2 (t - 1) (by decide)
    unfold bal
    dsimp only
    rw [hclog, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
    have h2m : 2 * 2 ^ (t - 1) - 2 ^ (t - 1) = 2 ^ (t - 1) := by omega
    rw [h2m]
    have h2t : (2 : ℤ) ^ t = 2 * (2 : ℤ) ^ (t - 1) := by
      have : t = (t - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    push_cast
    rw [h2t]
    ring
  · have hlt : 2 ^ (t - 1) < m := by omega
    have hclog : Nat.clog 2 m = t := by
      apply le_antisymm
      · exact Nat.clog_le_of_le_pow hhi
      · by_contra hlt2
        push Not at hlt2
        have hle1 : Nat.clog 2 m ≤ t - 1 := by omega
        have := le_trans (le_pow_clog m) (Nat.pow_le_pow_right (by decide : 0 < 2) hle1)
        omega
    unfold bal
    dsimp only
    rw [hclog]
    have h2t_le : 2 ^ t ≤ 2 * m := by
      have : 2 ^ t = 2 * 2 ^ (t - 1) := by
        have ht1 : t = (t - 1) + 1 := by omega
        conv_lhs => rw [ht1, pow_succ]
        ring
      omega
    have hbp : (base : ℤ) ^ t = (base : ℤ) ^ (t - 1) * (base : ℤ) := by
      have ht1 : t = (t - 1) + 1 := by omega
      conv_lhs => rw [ht1, pow_succ]
    push_cast [hhi, h2t_le]
    rw [hbp]
    ring

private lemma bal_ge_lin {base m t : ℕ} (hbase : 1 ≤ base) (hm : 1 ≤ m) (ht : 1 ≤ t) :
    (2 * (base : ℤ) - 1) * (m : ℤ) * (base : ℤ) ^ (t - 1) -
      ((base : ℤ) - 1) * (2 : ℤ) ^ t * (base : ℤ) ^ (t - 1) ≤ (bal base m : ℤ) := by
  let g : ℕ → ℤ := fun u =>
    (2 * (base : ℤ) - 1) * (m : ℤ) * (base : ℤ) ^ (u - 1) -
    ((base : ℤ) - 1) * (2 : ℤ) ^ u * (base : ℤ) ^ (u - 1)
  change g t ≤ (bal base m : ℤ)
  have hstep : ∀ u : ℕ, 1 ≤ u →
      g (u + 1) - g u =
        ((base : ℤ) - 1) * (2 * (base : ℤ) - 1) * (base : ℤ) ^ (u - 1) * ((m : ℤ) - (2 : ℤ) ^ u) := by
    intro u hu
    dsimp only [g]
    have hu1 : u + 1 - 1 = u := by omega
    rw [hu1]
    have hbu : (base : ℤ) ^ u = (base : ℤ) ^ (u - 1) * (base : ℤ) := by
      have : u = (u - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
    rw [hbu, pow_succ (2 : ℤ) u]
    ring
  have hnonneg : 0 ≤ ((base : ℤ) - 1) * (2 * (base : ℤ) - 1) := by
    have : (1 : ℤ) ≤ (base : ℤ) := by omega
    nlinarith
  let s := max 1 (Nat.clog 2 m)
  have hs1 : 1 ≤ s := le_max_left _ _
  have hs_lo : 2 ^ (s - 1) ≤ m := by
    by_cases hm1 : m = 1
    · subst hm1; simp [s, Nat.clog_one_right]
    · have hclog1 : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by decide) (by omega)
      have hs_eq : s = Nat.clog 2 m := max_eq_right hclog1
      rw [hs_eq]
      exact le_of_lt (pow_pred_lt_of_clog (by omega))
  have hs_hi : m ≤ 2 ^ s := by
    calc m ≤ 2 ^ Nat.clog 2 m := le_pow_clog m
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  have hgs : g s = (bal base m : ℤ) := (bal_eq_int_of_bounds hs1 hs_lo hs_hi).symm
  rw [← hgs]
  by_cases hts : t ≤ s
  · -- Induct upward from t to s
    have hup : ∀ k : ℕ, t + k ≤ s → g t ≤ g (t + k) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hlt_s : t + k < s := by omega
        have h2le : 2 ^ (t + k) ≤ m := by
          have : t + k ≤ s - 1 := by omega
          exact le_trans (Nat.pow_le_pow_right (by decide) this) hs_lo
        have hdiff : 0 ≤ g (t + k + 1) - g (t + k) := by
          rw [hstep (t + k) (by omega)]
          have hpow : (0 : ℤ) ≤ (base : ℤ) ^ (t + k - 1) := by positivity
          have hm2 : (0 : ℤ) ≤ (m : ℤ) - (2 : ℤ) ^ (t + k) := by
            have : ((2 ^ (t + k) : ℕ) : ℤ) ≤ (m : ℤ) := Nat.cast_le.mpr h2le
            simpa using sub_nonneg.mpr this
          exact mul_nonneg (mul_nonneg hnonneg hpow) hm2
        have hprev := ih (by omega)
        rw [← Nat.add_assoc]
        linarith
    have := hup (s - t) (by omega)
    rwa [show t + (s - t) = s by omega] at this
  · -- Induct downward from t to s
    have hdown : ∀ k : ℕ, g (s + k) ≤ g s := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hmle : m ≤ 2 ^ (s + k) :=
          le_trans hs_hi (Nat.pow_le_pow_right (by decide) (by omega))
        have hdiff : g (s + k + 1) - g (s + k) ≤ 0 := by
          rw [hstep (s + k) (by omega)]
          have hpow : (0 : ℤ) ≤ (base : ℤ) ^ (s + k - 1) := by positivity
          have hm2 : (m : ℤ) - (2 : ℤ) ^ (s + k) ≤ 0 := by
            have : (m : ℤ) ≤ ((2 ^ (s + k) : ℕ) : ℤ) := Nat.cast_le.mpr hmle
            simpa using sub_nonpos.mpr this
          exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hnonneg hpow) hm2
        rw [← Nat.add_assoc]
        linarith
    have := hdown (t - s)
    rwa [show s + (t - s) = t by omega] at this

private lemma bal_convex {base a c : ℕ} (hbase : 1 ≤ base) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    bal base (a + c) ≤ base * (bal base a + bal base c) := by
  let m := a + c
  have hm2 : 2 ≤ m := by omega
  let d := Nat.clog 2 m
  have hd1 : 1 ≤ d := Nat.clog_pos (by decide) (by omega)
  by_cases hdeq1 : d = 1
  · have hmle2 : m ≤ 2 := by
      have := le_pow_clog m
      rw [show Nat.clog 2 m = 1 from hdeq1] at this
      simpa using this
    have ha1 : a = 1 := by omega
    have hc1 : c = 1 := by omega
    subst ha1; subst hc1
    rw [bal_one, bal_two]
    omega
  · have hd2 : 2 ≤ d := by omega
    have h1 := bal_ge_lin (base := base) (m := a) (t := d - 1) hbase ha (by omega)
    have h2 := bal_ge_lin (base := base) (m := c) (t := d - 1) hbase hc (by omega)
    have hsum : (bal base m : ℤ) =
        (2 * (base : ℤ) - 1) * (m : ℤ) * (base : ℤ) ^ (d - 1) -
        ((base : ℤ) - 1) * (2 : ℤ) ^ d * (base : ℤ) ^ (d - 1) :=
      bal_eq_int_of_bounds hd1 (le_of_lt (pow_pred_lt_of_clog hm2)) (le_pow_clog m)
    have hbd : (base : ℤ) ^ (d - 1) = (base : ℤ) * (base : ℤ) ^ (d - 1 - 1) := by
      have : d - 1 = (d - 1 - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    have h2d : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
      have : d = (d - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    have hZ : (bal base m : ℤ) ≤ (base : ℤ) * ((bal base a : ℤ) + (bal base c : ℤ)) := by
      have hcomb : (base : ℤ) *
          (((2 * (base : ℤ) - 1) * (a : ℤ) * (base : ℤ) ^ (d - 1 - 1) -
            ((base : ℤ) - 1) * (2 : ℤ) ^ (d - 1) * (base : ℤ) ^ (d - 1 - 1)) +
           ((2 * (base : ℤ) - 1) * (c : ℤ) * (base : ℤ) ^ (d - 1 - 1) -
            ((base : ℤ) - 1) * (2 : ℤ) ^ (d - 1) * (base : ℤ) ^ (d - 1 - 1))) ≤
          (base : ℤ) * ((bal base a : ℤ) + (bal base c : ℤ)) := by
        have hb0 : (0 : ℤ) ≤ (base : ℤ) := by omega
        nlinarith
      have heq : (bal base m : ℤ) = (base : ℤ) *
          (((2 * (base : ℤ) - 1) * (a : ℤ) * (base : ℤ) ^ (d - 1 - 1) -
            ((base : ℤ) - 1) * (2 : ℤ) ^ (d - 1) * (base : ℤ) ^ (d - 1 - 1)) +
           ((2 * (base : ℤ) - 1) * (c : ℤ) * (base : ℤ) ^ (d - 1 - 1) -
            ((base : ℤ) - 1) * (2 : ℤ) ^ (d - 1) * (base : ℤ) ^ (d - 1 - 1))) := by
        rw [hsum, hbd, h2d]
        have hmZ : (m : ℤ) = (a : ℤ) + (c : ℤ) := Nat.cast_add a c
        rw [hmZ]
        ring
      linarith
    exact_mod_cast hZ

private lemma bal_split_eq {base m a c : ℕ} (hm : 2 ≤ m) (hsum : a + c = m)
    (ha_lo : 2 ^ (Nat.clog 2 m - 2) ≤ a) (ha_hi : a ≤ 2 ^ (Nat.clog 2 m - 1))
    (hc_lo : 2 ^ (Nat.clog 2 m - 2) ≤ c) (hc_hi : c ≤ 2 ^ (Nat.clog 2 m - 1)) :
    bal base m = base * (bal base a + bal base c) := by
  let d := Nat.clog 2 m
  have hd1 : 1 ≤ d := Nat.clog_pos (by decide) (by omega)
  by_cases hd_eq1 : d = 1
  · have hmle2 : m ≤ 2 := by
      have := le_pow_clog m
      rw [show Nat.clog 2 m = 1 from hd_eq1] at this; simpa using this
    have hm2 : m = 2 := by omega
    have ha1 : a = 1 := by
      have : 2 ^ (1 - 2) = 1 := by decide
      have : 2 ^ (1 - 1) = 1 := by decide
      rw [show Nat.clog 2 m = 1 from hd_eq1] at ha_lo ha_hi
      omega
    have hc1 : c = 1 := by omega
    rw [hm2, ha1, hc1, bal_one, bal_two]; ring
  · have hd2 : 2 ≤ d := by omega
    have hma := bal_eq_int_of_bounds (base := base) (m := a) (t := d - 1) (by omega)
      (by simpa [Nat.sub_sub] using ha_lo) ha_hi
    have hmc := bal_eq_int_of_bounds (base := base) (m := c) (t := d - 1) (by omega)
      (by simpa [Nat.sub_sub] using hc_lo) hc_hi
    have hmm := bal_eq_int_of_bounds (base := base) (m := m) (t := d) hd1
      (le_of_lt (pow_pred_lt_of_clog hm)) (le_pow_clog m)
    have hbd : (base : ℤ) ^ (d - 1) = (base : ℤ) * (base : ℤ) ^ (d - 1 - 1) := by
      have : d - 1 = (d - 1 - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    have h2d : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
      have : d = (d - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    have hZ : (bal base m : ℤ) = (base : ℤ) * ((bal base a : ℤ) + (bal base c : ℤ)) := by
      rw [hmm, hma, hmc, hbd, h2d]
      have hmZ : (m : ℤ) = (a : ℤ) + (c : ℤ) := by omega
      rw [hmZ]; ring
    exact_mod_cast hZ

private lemma clog_split_le {m a c : ℕ} (hm : 2 ≤ m) (hsum : a + c = m)
    (ha_hi : a ≤ 2 ^ (Nat.clog 2 m - 1)) (hc_hi : c ≤ 2 ^ (Nat.clog 2 m - 1)) :
    1 + max (Nat.clog 2 a) (Nat.clog 2 c) ≤ Nat.clog 2 m := by
  have hd1 : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by decide) (by omega)
  have h1 : Nat.clog 2 a ≤ Nat.clog 2 m - 1 := Nat.clog_le_of_le_pow ha_hi
  have h2 : Nat.clog 2 c ≤ Nat.clog 2 m - 1 := Nat.clog_le_of_le_pow hc_hi
  omega

private lemma branch_dominance {b n : ℕ} (hb : 2 ≤ b) (hn : 2 ≤ n) :
    let base := 2 ^ (b - 1)
    let H1 := b * (1 + Nat.clog 2 n)
    let K1 := base * (2 * base + bal base n)
    let H2 := b * Nat.clog 2 (n + 3)
    let K2 := bal base (n + 3)
    (H1 ≤ H2 ∧ K1 ≤ K2) ∨ (H2 ≤ H1 ∧ K2 ≤ K1) := by
  intro base H1 K1 H2 K2
  have hbase2 : 2 ≤ base := by
    have : 1 ≤ b - 1 := by omega
    calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by decide) this
  let d := Nat.clog 2 n
  have hd1 : 1 ≤ d := Nat.clog_pos (by decide) (by omega)
  have hlo : 2 ^ (d - 1) < n := pow_pred_lt_of_clog hn
  have hhi : n ≤ 2 ^ d := le_pow_clog n
  by_cases hcase : n + 3 ≤ 2 ^ d
  · -- H2 < H1 and K2 ≤ K1!
    right
    have hclog2 : Nat.clog 2 (n + 3) = d := by
      apply le_antisymm
      · exact Nat.clog_le_of_le_pow hcase
      · exact Nat.clog_mono_right 2 (by omega)
    have hH : H2 ≤ H1 := by
      dsimp only [H1, H2]; rw [hclog2]
      exact Nat.mul_le_mul_left b (by omega)
    refine ⟨hH, ?_⟩
    -- Prove K2 ≤ K1 over ℤ
    have hd3 : 3 ≤ d := by
      by_contra hlt
      have : d ≤ 2 := by omega
      have : 2 ^ d ≤ 4 := le_trans (Nat.pow_le_pow_right (by decide) this) (by decide)
      have : 2 ^ (d - 1) ≥ 1 := Nat.one_le_pow _ _ (by decide)
      interval_cases d <;> omega
    have hK1_eq : (K1 : ℤ) = 2 * (base : ℤ) ^ 2 +
        (2 * (base : ℤ) - 1) * (n : ℤ) * (base : ℤ) ^ d -
        ((base : ℤ) - 1) * (2 : ℤ) ^ d * (base : ℤ) ^ d := by
      have hbaln := bal_eq_int_of_bounds (base := base) hd1 (le_of_lt hlo) hhi
      have hbd : (base : ℤ) ^ d = (base : ℤ) * (base : ℤ) ^ (d - 1) := by
        have : d = (d - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        ring
      dsimp only [K1]; push_cast; rw [hbaln, hbd]; ring
    have hK2_eq : (K2 : ℤ) =
        (2 * (base : ℤ) - 1) * ((n : ℤ) + 3) * (base : ℤ) ^ (d - 1) -
        ((base : ℤ) - 1) * (2 : ℤ) ^ d * (base : ℤ) ^ (d - 1) := by
      have hbal3 := bal_eq_int_of_bounds (base := base) (m := n + 3) (t := d) hd1 (by omega) hcase
      dsimp only [K2]; rw [hbal3]; push_cast; ring
    have hZ : (K2 : ℤ) ≤ (K1 : ℤ) := by
      rw [hK1_eq, hK2_eq]
      have hbd : (base : ℤ) ^ d = (base : ℤ) * (base : ℤ) ^ (d - 1) := by
        have : d = (d - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        ring
      rw [hbd]
      have hpow_pos : (1 : ℤ) ≤ (base : ℤ) ^ (d - 1) := by
        exact_mod_cast Nat.one_le_pow (d - 1) base (by omega)
      have hbZ : (2 : ℤ) ≤ (base : ℤ) := by omega
      have h2d : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
        have : d = (d - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        ring
      by_cases hd_eq3 : d = 3
      · have h8 : (2 : ℤ) ^ d = 8 := by rw [hd_eq3]; norm_num
        have hn5 : n = 5 := by
          have : 2 ^ (3 - 1) = 4 := by decide
          have : 2 ^ 3 = 8 := by decide
          rw [hd_eq3] at hlo hcase; omega
        have hnZ : (n : ℤ) = 5 := by omega
        have hbd1 : (base : ℤ) ^ (d - 1) = (base : ℤ) ^ 2 := by rw [hd_eq3]
        rw [h8, hnZ, hbd1]
        have hfac : 2 * (base : ℤ) ^ 2 +
            (2 * (base : ℤ) - 1) * 5 * ((base : ℤ) * (base : ℤ) ^ 2) -
            ((base : ℤ) - 1) * 8 * ((base : ℤ) * (base : ℤ) ^ 2) -
            ((2 * (base : ℤ) - 1) * (5 + 3) * (base : ℤ) ^ 2 -
              ((base : ℤ) - 1) * 8 * (base : ℤ) ^ 2) =
            (base : ℤ) ^ 2 * ((2 * (base : ℤ) - 1) * ((base : ℤ) - 2)) := by ring
        have hpos : 0 ≤ (base : ℤ) ^ 2 * ((2 * (base : ℤ) - 1) * ((base : ℤ) - 2)) :=
          mul_nonneg (sq_nonneg _) (by nlinarith)
        linarith
      · have hd4 : 4 ≤ d := by omega
        have h2dm1 : (8 : ℤ) ≤ (2 : ℤ) ^ (d - 1) := by
          have : 3 ≤ d - 1 := by omega
          exact_mod_cast le_trans (by decide : 8 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by decide) this)
        have hloZ : (2 : ℤ) ^ (d - 1) + 1 ≤ (n : ℤ) := by
          have : ((2 ^ (d - 1) + 1 : ℕ) : ℤ) ≤ (n : ℤ) := Nat.cast_le.mpr (by omega)
          simpa using this
        have hcoeff : 0 ≤ (2 * (base : ℤ) - 1) * (n : ℤ) * (base : ℤ) -
            ((base : ℤ) - 1) * (2 : ℤ) ^ d * (base : ℤ) -
            ((2 * (base : ℤ) - 1) * ((n : ℤ) + 3) - ((base : ℤ) - 1) * (2 : ℤ) ^ d) := by
          have hrew : (2 * (base : ℤ) - 1) * (n : ℤ) * (base : ℤ) -
              ((base : ℤ) - 1) * (2 : ℤ) ^ d * (base : ℤ) -
              ((2 * (base : ℤ) - 1) * ((n : ℤ) + 3) - ((base : ℤ) - 1) * (2 : ℤ) ^ d) =
              ((2 * (n : ℤ) - (2 : ℤ) ^ d) * (base : ℤ) + ((n : ℤ) - 6)) * ((base : ℤ) - 2) +
              (3 * (n : ℤ) - (2 : ℤ) ^ d - 9) := by ring
          rw [hrew]
          have hA : 0 ≤ 3 * (n : ℤ) - (2 : ℤ) ^ d - 9 := by rw [h2d]; linarith
          have h2n : 2 ≤ 2 * (n : ℤ) - (2 : ℤ) ^ d := by rw [h2d]; linarith
          have hn6 : 0 ≤ (n : ℤ) - 6 := by linarith
          have hB : 0 ≤ (2 * (n : ℤ) - (2 : ℤ) ^ d) * (base : ℤ) + ((n : ℤ) - 6) := by nlinarith
          have hC : 0 ≤ ((2 * (n : ℤ) - (2 : ℤ) ^ d) * (base : ℤ) + ((n : ℤ) - 6)) * ((base : ℤ) - 2) :=
            mul_nonneg hB (by linarith)
          linarith
        have hmul : 0 ≤ ((2 * (base : ℤ) - 1) * (n : ℤ) * (base : ℤ) -
            ((base : ℤ) - 1) * (2 : ℤ) ^ d * (base : ℤ) -
            ((2 * (base : ℤ) - 1) * ((n : ℤ) + 3) - ((base : ℤ) - 1) * (2 : ℤ) ^ d)) *
            (base : ℤ) ^ (d - 1) := mul_nonneg hcoeff (by linarith)
        have hsq : (0 : ℤ) ≤ 2 * (base : ℤ) ^ 2 := by positivity
        linarith
    exact_mod_cast hZ
  · -- n + 3 > 2^d, so clog 2 (n + 3) ≥ d + 1 = 1 + clog 2 n, hence H1 ≤ H2!
    have hclog_ge : d + 1 ≤ Nat.clog 2 (n + 3) := by
      by_contra hlt
      have hle : Nat.clog 2 (n + 3) ≤ d := by omega
      have := le_trans (le_pow_clog (n + 3)) (Nat.pow_le_pow_right (by decide) hle)
      omega
    have hH1_le_H2 : H1 ≤ H2 := by
      dsimp only [H1, H2]
      exact Nat.mul_le_mul_left b (by omega)
    by_cases hK : K1 ≤ K2
    · exact Or.inl ⟨hH1_le_H2, hK⟩
    · by_cases hn2 : n = 2
      · exfalso; apply hK
        subst hn2
        have hbal2 : bal base 2 = 2 * base := bal_two base
        have hbal5 : bal base 5 = 3 * base ^ 2 + 2 * base ^ 3 := by
          have hc5 : Nat.clog 2 5 = 3 := by decide
          unfold bal; dsimp only; rw [hc5]; ring
        dsimp only [K1, K2]
        rw [hbal2, hbal5]
        have h1 : 4 * base ^ 2 ≤ 3 * base ^ 2 + 2 * base ^ 3 := by nlinarith
        linarith
      · have hn3 : 3 ≤ n := by omega
        have hle_2dp1 : n + 3 ≤ 2 ^ (d + 1) := by
          have h2d : 2 ^ d ≥ 4 := by
            have : 2 ≤ d := by
              by_contra hlt
              have hd_le1 : d ≤ 1 := by omega
              have := le_trans hhi (Nat.pow_le_pow_right (by decide) hd_le1)
              omega
            exact le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) this)
          rw [pow_succ]; omega
        have hclog_eq : Nat.clog 2 (n + 3) = d + 1 :=
          le_antisymm (Nat.clog_le_of_le_pow hle_2dp1) hclog_ge
        have hH2_le_H1 : H2 ≤ H1 := by
          dsimp only [H1, H2]; rw [hclog_eq, Nat.add_comm]
        exact Or.inr ⟨hH2_le_H1, by omega⟩

end Balanced

/-! ## Section 2: Formula `F`, Parity Block Operations, `mergeTree`, and `OuterTree` -/

section Core

variable {n : ℕ} (hn : 0 < n) {b : ℕ} (hb : 0 < b)

private abbrev Raw (n b : ℕ) := (i : Fin n) × Fin ((fun _ : Fin n => b) i)

private def parity (y : Raw n b → Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin b)).filter (fun j => y ⟨i, j⟩ = true)).card)

private def liftAx (F : Set (Clause (Fin n))) (A : Clause (Raw n b)) : Prop :=
  ∃ C ∈ F, ∃ y : Raw n b → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
    A = ((Finset.univ : Finset (Raw n b)).filter (fun u => u.1 ∈ C.image Prod.fst)).image
      (fun u => (u, !(y u)))

private def shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (c : Bool), p ++ [c] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

private def refutes (F : Set (Clause (Fin n))) (H K : ℕ) : Prop :=
  ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (Raw n b)),
    shape N J ∧ line [] = ∅ ∧ (∀ p ∈ N, p.length ≤ H) ∧ (N \ J).card ≤ K ∧
    (∀ p ∈ N \ J, liftAx F (line p)) ∧
    ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)

private def atV (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩
private def first : Fin n := atV hn 0
private def last : Fin n := atV hn (n - 1)

private def cycF : Set (Clause (Fin n)) :=
  {C | C = {(last hn, true), (first hn, true)} ∨
       C = {(last hn, false), (first hn, true)} ∨
       C = {(last hn, false), (first hn, false)} ∨
       ∃ i : ℕ, i + 1 < n ∧ C = {(atV hn i, false), (atV hn (i + 1), true)}}

private lemma atV_val {i : ℕ} (hi : i < n) : (atV hn i).val = i :=
  Nat.mod_eq_of_lt hi

private lemma atV_inj {i j : ℕ} (hi : i < n) (hj : j < n) (h : atV hn i = atV hn j) : i = j := by
  have := congrArg Fin.val h
  rwa [atV_val hn hi, atV_val hn hj] at this

private lemma first_ne_last (hn2 : 2 ≤ n) : first hn ≠ last hn := by
  intro h
  have := atV_inj hn (by omega) (by omega) h
  omega

private lemma parity_update_ne (y : Raw n b → Bool) (v : Fin n) (j : Fin b) (val : Bool)
    {u : Fin n} (huv : u ≠ v) :
    parity (Function.update y ⟨v, j⟩ val) u = parity y u := by
  unfold parity
  congr 1; congr 1; congr 1; congr 1
  ext j'
  have hne : (⟨u, j'⟩ : Raw n b) ≠ ⟨v, j⟩ := by
    intro h; exact huv (congrArg Sigma.fst h)
  simp [Function.update_of_ne hne]

private lemma parity_update_flip (y : Raw n b → Bool) (v : Fin n) (j : Fin b) :
    parity (Function.update y ⟨v, j⟩ false) v ≠ parity (Function.update y ⟨v, j⟩ true) v := by
  unfold parity
  let s₀ := (Finset.univ : Finset (Fin b)).filter (fun j' => Function.update y ⟨v, j⟩ false ⟨v, j'⟩ = true)
  let s₁ := (Finset.univ : Finset (Fin b)).filter (fun j' => Function.update y ⟨v, j⟩ true ⟨v, j'⟩ = true)
  have hj0 : j ∉ s₀ := by simp [s₀]
  have hs1 : s₁ = insert j s₀ := by
    ext j'
    simp only [s₁, s₀, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hjj : j' = j
    · subst hjj; simp
    · have hne : (⟨v, j'⟩ : Raw n b) ≠ ⟨v, j⟩ := by
        intro h; exact hjj (by simpa using h)
      simp only [hjj, false_or, Function.update_of_ne hne]
  have hcard : s₁.card = s₀.card + 1 := by
    rw [hs1, Finset.card_insert_of_notMem hj0]
  change decide (Odd s₀.card) ≠ decide (Odd s₁.card)
  rw [hcard]
  intro h
  have hiff : Odd s₀.card ↔ Odd (s₀.card + 1) := by simpa using h
  rw [Nat.odd_add_one] at hiff
  exact iff_not_self hiff

private lemma parity_congr {y₁ y₂ : Raw n b → Bool} {i : Fin n}
    (h : ∀ j : Fin b, y₁ ⟨i, j⟩ = y₂ ⟨i, j⟩) : parity y₁ i = parity y₂ i := by
  unfold parity
  congr 1; congr 1; congr 1; congr 1
  ext j
  simp [h j]

/-! ### Merging two tree resolution derivations -/

private lemma mergeTree {F : Set (Clause (Fin n))}
    {N₀ J₀ N₁ J₁ : Finset (List Bool)} {line₀ line₁ : List Bool → Clause (Raw n b)}
    {h₀ h₁ k₀ k₁ : ℕ} {R : Clause (Raw n b)}
    (hs₀ : shape N₀ J₀) (hh₀ : ∀ p ∈ N₀, p.length ≤ h₀) (hk₀ : (N₀ \ J₀).card = k₀)
    (hl₀ : ∀ p ∈ N₀ \ J₀, liftAx F (line₀ p))
    (hr₀ : ∀ p ∈ J₀, IsResolvent (line₀ (p ++ [false])) (line₀ (p ++ [true])) (line₀ p))
    (hs₁ : shape N₁ J₁) (hh₁ : ∀ p ∈ N₁, p.length ≤ h₁) (hk₁ : (N₁ \ J₁).card = k₁)
    (hl₁ : ∀ p ∈ N₁ \ J₁, liftAx F (line₁ p))
    (hr₁ : ∀ p ∈ J₁, IsResolvent (line₁ (p ++ [false])) (line₁ (p ++ [true])) (line₁ p))
    (hroot : IsResolvent (line₀ []) (line₁ []) R) :
    ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (Raw n b)),
      shape N J ∧ line [] = R ∧ (∀ p ∈ N, p.length ≤ 1 + max h₀ h₁) ∧
      (N \ J).card = k₀ + k₁ ∧
      (∀ p ∈ N \ J, liftAx F (line p)) ∧
      ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) := by
  let N : Finset (List Bool) := insert [] (N₀.image (false :: ·) ∪ N₁.image (true :: ·))
  let J : Finset (List Bool) := insert [] (J₀.image (false :: ·) ∪ J₁.image (true :: ·))
  let line : List Bool → Clause (Raw n b) := fun p =>
    match p with
    | [] => R
    | false :: q => line₀ q
    | true :: q => line₁ q
  have hshape : shape N J := by
    refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hmem
      · exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        rcases Finset.mem_union.mp hmem with h0 | h1
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h0
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hs₀.2.1 hq))
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hs₁.2.1 hq))
    · intro p c hpc
      cases p with
      | nil => exact Finset.mem_insert_self _ _
      | cons hd tl =>
        apply Finset.mem_insert_of_mem
        have hne : (hd :: tl) ++ [c] ≠ [] := by simp
        have hmem := (Finset.mem_insert.mp hpc).resolve_left hne
        cases hd with
        | false =>
          rcases Finset.mem_union.mp hmem with h0 | h1
          · obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp h0
            have : tl ++ [c] = q := by simpa using hqeq.symm
            rw [← this] at hq
            exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hs₀.2.2.1 tl c hq))
          · obtain ⟨q, _, hqeq⟩ := Finset.mem_image.mp h1
            simp at hqeq
        | true =>
          rcases Finset.mem_union.mp hmem with h0 | h1
          · obtain ⟨q, _, hqeq⟩ := Finset.mem_image.mp h0
            simp at hqeq
          · obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp h1
            have : tl ++ [c] = q := by simpa using hqeq.symm
            rw [← this] at hq
            exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hs₁.2.2.1 tl c hq))
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hmem
      · constructor
        · apply Finset.mem_insert_of_mem
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs₀.1)
        · apply Finset.mem_insert_of_mem
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs₁.1)
      · rcases Finset.mem_union.mp hmem with h0 | h1
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h0
          have ⟨hf, ht⟩ := hs₀.2.2.2 q hq
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hf)),
                 Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht))⟩
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
          have ⟨hf, ht⟩ := hs₁.2.2.2 q hq
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hf)),
                 Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht))⟩
  have hleaves_eq : N \ J = (N₀ \ J₀).image (false :: ·) ∪ (N₁ \ J₁).image (true :: ·) := by
    ext p
    simp only [N, J, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    cases p with
    | nil => simp
    | cons hd tl =>
      cases hd with
      | false =>
        constructor
        · rintro ⟨hnil | (⟨q, hq, hEq⟩ | ⟨q, _, hEq⟩), hnot⟩
          · simp at hnil
          · left; refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inl ⟨q, hqJ, hEq⟩))⟩, hEq⟩
          · simp at hEq
        · rintro (⟨q, ⟨hqN, hqJ⟩, hEq⟩ | ⟨q, _, hEq⟩)
          · refine ⟨Or.inr (Or.inl ⟨q, hqN, hEq⟩), ?_⟩
            rintro (hnil | ⟨q', hq'J, hEq'⟩ | ⟨q', _, hEq'⟩)
            · simp at hnil
            · have : q' = q := by
                have h1 : tl = q := by simpa using hEq.symm
                have h2 : tl = q' := by simpa using hEq'.symm
                exact h2.symm.trans h1
              exact hqJ (this ▸ hq'J)
            · simp at hEq'
          · simp at hEq
      | true =>
        constructor
        · rintro ⟨hnil | (⟨q, _, hEq⟩ | ⟨q, hq, hEq⟩), hnot⟩
          · simp at hnil
          · simp at hEq
          · right; refine ⟨q, ⟨hq, fun hqJ => hnot (Or.inr (Or.inr ⟨q, hqJ, hEq⟩))⟩, hEq⟩
        · rintro (⟨q, _, hEq⟩ | ⟨q, ⟨hqN, hqJ⟩, hEq⟩)
          · simp at hEq
          · refine ⟨Or.inr (Or.inr ⟨q, hqN, hEq⟩), ?_⟩
            rintro (hnil | ⟨q', _, hEq'⟩ | ⟨q', hq'J, hEq'⟩)
            · simp at hnil
            · simp at hEq'
            · have : q' = q := by
                have h1 : tl = q := by simpa using hEq.symm
                have h2 : tl = q' := by simpa using hEq'.symm
                exact h2.symm.trans h1
              exact hqJ (this ▸ hq'J)
  refine ⟨N, J, line, hshape, rfl, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hmem
    · simp
    · rcases Finset.mem_union.mp hmem with h0 | h1
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h0
        have := hh₀ q hq; simp; omega
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
        have := hh₁ q hq; simp; omega
  · rw [hleaves_eq, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
          Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2), hk₀, hk₁]
    · rw [Finset.disjoint_left]
      intro p hp0 hp1
      obtain ⟨q₀, _, rfl⟩ := Finset.mem_image.mp hp0
      obtain ⟨q₁, _, hEq⟩ := Finset.mem_image.mp hp1
      simp at hEq
  · intro p hp
    rw [hleaves_eq] at hp
    rcases Finset.mem_union.mp hp with h0 | h1
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h0
      exact hl₀ q hq
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
      exact hl₁ q hq
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hmem
    · exact hroot
    · rcases Finset.mem_union.mp hmem with h0 | h1
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h0
        exact hr₀ q hq
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
        exact hr₁ q hq

/-! ### Lifting an `OuterTree` to a `b`-bit parity-lifted tree resolution proof -/

private def liftClause (C : Clause (Fin n)) (y : Raw n b → Bool) : Clause (Raw n b) :=
  ((Finset.univ : Finset (Raw n b)).filter (fun u => u.1 ∈ C.image Prod.fst)).image
    (fun u => (u, !(y u)))

private def fixedClause (v : Fin n) (k : ℕ) (y : Raw n b → Bool) : Clause (Raw n b) :=
  ((Finset.univ : Finset (Fin b)).filter (fun j => j.val < k)).image
    (fun j => (⟨v, j⟩, !(y ⟨v, j⟩)))

private inductive OuterTree (n : ℕ) where
  | leaf (C : Clause (Fin n)) : OuterTree n
  | node (v : Fin n) (l r : OuterTree n) : OuterTree n

private def OuterTree.clause : OuterTree n → Clause (Fin n)
  | .leaf C => C
  | .node v l r => l.clause.erase (v, true) ∪ r.clause.erase (v, false)

private def OuterTree.height : OuterTree n → ℕ
  | .leaf _ => 0
  | .node _ l r => 1 + max l.height r.height

private def OuterTree.cost (base : ℕ) : OuterTree n → ℕ
  | .leaf _ => 1
  | .node _ l r => base * (l.cost base + r.cost base)

private def NonTaut (C : Clause (Fin n)) : Prop :=
  ∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)

private def OuterTree.Valid (F : Set (Clause (Fin n))) : OuterTree n → Prop
  | .leaf C => C ∈ F ∧ NonTaut C
  | .node v l r =>
      l.Valid F ∧ r.Valid F ∧
      (v, true) ∈ l.clause ∧ (v, false) ∈ r.clause ∧
      NonTaut (l.clause.erase (v, true) ∪ r.clause.erase (v, false))

private lemma mem_liftClause {C : Clause (Fin n)} {y : Raw n b → Bool} {u : Raw n b} {s : Bool} :
    (u, s) ∈ liftClause C y ↔ u.1 ∈ C.image Prod.fst ∧ s = !(y u) := by
  unfold liftClause
  rw [Finset.mem_image]
  constructor
  · rintro ⟨u', hu', hEq⟩
    rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
    exact ⟨(Finset.mem_filter.mp hu').2, rfl⟩
  · rintro ⟨hu, rfl⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩

private lemma mem_fixedClause {v : Fin n} {k : ℕ} {y : Raw n b → Bool} {u : Raw n b} {s : Bool} :
    (u, s) ∈ fixedClause v k y ↔ ∃ j : Fin b, j.val < k ∧ u = ⟨v, j⟩ ∧ s = !(y ⟨v, j⟩) := by
  unfold fixedClause
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hEq⟩
    rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
    exact ⟨j, (Finset.mem_filter.mp hj).2, rfl, rfl⟩
  · rintro ⟨j, hj, rfl, rfl⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩

private lemma liftClause_congr {C : Clause (Fin n)} {y₁ y₂ : Raw n b → Bool}
    (h : ∀ u : Raw n b, u.1 ∈ C.image Prod.fst → y₁ u = y₂ u) :
    liftClause C y₁ = liftClause C y₂ := by
  ext ⟨u, s⟩
  simp only [mem_liftClause]
  constructor
  · rintro ⟨hu, rfl⟩; exact ⟨hu, by rw [h u hu]⟩
  · rintro ⟨hu, rfl⟩; exact ⟨hu, by rw [h u hu]⟩

private lemma fixedClause_congr {v : Fin n} {k : ℕ} {y₁ y₂ : Raw n b → Bool}
    (h : ∀ j : Fin b, j.val < k → y₁ ⟨v, j⟩ = y₂ ⟨v, j⟩) :
    fixedClause v k y₁ = fixedClause v k y₂ := by
  ext ⟨u, s⟩
  simp only [mem_fixedClause]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨j, hj, rfl, by rw [h j hj]⟩
  · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨j, hj, rfl, by rw [h j hj]⟩

private lemma var_not_mem_resolvent {C D : Clause (Fin n)} {v : Fin n}
    (hC : NonTaut C) (hD : NonTaut D) (hvC : (v, true) ∈ C) (hvD : (v, false) ∈ D) :
    v ∉ (C.erase (v, true) ∪ D.erase (v, false)).image Prod.fst := by
  intro hmem
  obtain ⟨⟨u, s⟩, hus, rfl⟩ := Finset.mem_image.mp hmem
  rcases Finset.mem_union.mp hus with h1 | h2
  · rw [Finset.mem_erase] at h1
    cases s
    · exact hC u ⟨hvC, h1.2⟩
    · exact h1.1 rfl
  · rw [Finset.mem_erase] at h2
    cases s
    · exact h2.1 rfl
    · exact hD u ⟨h2.2, hvD⟩

private lemma vars_resolvent {C D : Clause (Fin n)} {v : Fin n} :
    ∀ u : Fin n, u ≠ v →
      (u ∈ (C.erase (v, true) ∪ D.erase (v, false)).image Prod.fst ↔
       u ∈ C.image Prod.fst ∨ u ∈ D.image Prod.fst) := by
  intro u huv
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro ⟨⟨w, s⟩, ⟨_, h1⟩ | ⟨_, h2⟩, rfl⟩
    · exact Or.inl ⟨(w, s), h1, rfl⟩
    · exact Or.inr ⟨(w, s), h2, rfl⟩
  · rintro (⟨⟨w, s⟩, h1, rfl⟩ | ⟨⟨w, s⟩, h2, rfl⟩)
    · exact ⟨(w, s), Or.inl ⟨fun h => huv (congrArg Prod.fst h), h1⟩, rfl⟩
    · exact ⟨(w, s), Or.inr ⟨fun h => huv (congrArg Prod.fst h), h2⟩, rfl⟩

private lemma lift_outerTree (hb : 0 < b) {F : Set (Clause (Fin n))} (T : OuterTree n)
    (hV : T.Valid F) :
    ∀ y : Raw n b → Bool, (∀ lit ∈ T.clause, parity y lit.1 ≠ lit.2) →
      ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (Raw n b)),
        shape N J ∧ line [] = liftClause T.clause y ∧
        (∀ p ∈ N, p.length ≤ b * T.height) ∧
        (N \ J).card = T.cost (2 ^ (b - 1)) ∧
        (∀ p ∈ N \ J, liftAx F (line p)) ∧
        ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) := by
  induction T with
  | leaf C =>
    intro y hy
    refine ⟨{[]}, ∅, fun _ => liftClause C y, ?_, rfl, by simp [OuterTree.height],
      by simp [OuterTree.cost], ?_, by simp⟩
    · exact ⟨Finset.mem_singleton_self _, Finset.empty_subset _,
        fun p c h => by simp at h, fun p h => by simp at h⟩
    · intro p hp
      exact ⟨C, hV.1, y, hy, rfl⟩
  | node v l r ihl ihr =>
    intro y hy
    obtain ⟨hVl, hVr, hvl, hvr, hNT⟩ := hV
    have hNTl : NonTaut l.clause := by
      cases l with
      | leaf C => exact hVl.2
      | node _ _ _ => exact hVl.2.2.2.2
    have hNTr : NonTaut r.clause := by
      cases r with
      | leaf C => exact hVr.2
      | node _ _ _ => exact hVr.2.2.2.2
    let R := l.clause.erase (v, true) ∪ r.clause.erase (v, false)
    have hv_nmem : v ∉ R.image Prod.fst := var_not_mem_resolvent hNTl hNTr hvl hvr
    have hvars : ∀ u : Fin n, u ≠ v →
        (u ∈ R.image Prod.fst ↔ u ∈ l.clause.image Prod.fst ∨ u ∈ r.clause.image Prod.fst) :=
      vars_resolvent
    -- Gadget induction for 1 ≤ m ≤ b: builds root clause `liftClause R y ∪ fixedClause v (b - m) y'`
    have hgad : ∀ m : ℕ, 1 ≤ m → m ≤ b →
        ∀ y' : Raw n b → Bool, (∀ u : Raw n b, u.1 ≠ v → y' u = y u) →
          ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (Raw n b)),
            shape N J ∧ line [] = liftClause R y ∪ fixedClause v (b - m) y' ∧
            (∀ p ∈ N, p.length ≤ m + max (b * l.height) (b * r.height)) ∧
            (N \ J).card = 2 ^ (m - 1) * (l.cost (2 ^ (b - 1)) + r.cost (2 ^ (b - 1))) ∧
            (∀ p ∈ N \ J, liftAx F (line p)) ∧
            ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) := by
      intro m hm1
      induction m with
      | zero => omega
      | succ m' ihm =>
        intro hmb y' hy'_off
        cases m' with
        | zero =>
          -- m = 1: resolve on last bit j_last = ⟨b - 1, _⟩
          let j_last : Fin b := ⟨b - 1, by omega⟩
          let y₀ := Function.update y' ⟨v, j_last⟩ false
          let y₁ := Function.update y' ⟨v, j_last⟩ true
          have hy₀_off : ∀ u : Raw n b, u.1 ≠ v → y₀ u = y u := by
            intro u hu
            have hne : u ≠ ⟨v, j_last⟩ := fun h => hu (congrArg Sigma.fst h)
            dsimp only [y₀]; rw [Function.update_of_ne hne, hy'_off u hu]
          have hy₁_off : ∀ u : Raw n b, u.1 ≠ v → y₁ u = y u := by
            intro u hu
            have hne : u ≠ ⟨v, j_last⟩ := fun h => hu (congrArg Sigma.fst h)
            dsimp only [y₁]; rw [Function.update_of_ne hne, hy'_off u hu]
          have hpar_ne : parity y₀ v ≠ parity y₁ v := parity_update_flip y' v j_last
          have hfal_l : ∀ z : Raw n b → Bool, (∀ u : Raw n b, u.1 ≠ v → z u = y u) →
              parity z v = false → ∀ lit ∈ l.clause, parity z lit.1 ≠ lit.2 := by
            intro z hzoff hzpar lit hlit
            by_cases hlv : lit.1 = v
            · rcases lit with ⟨u, s⟩; dsimp only at hlv; subst hlv
              cases s
              · exact absurd ⟨hvl, hlit⟩ (hNTl u)
              · simp [hzpar]
            · have hmemR : lit ∈ R := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => hlv (congrArg Prod.fst h), hlit⟩)
              have hp : parity z lit.1 = parity y lit.1 := parity_congr (fun j => hzoff ⟨lit.1, j⟩ hlv)
              rw [hp]; exact hy lit hmemR
          have hfal_r : ∀ z : Raw n b → Bool, (∀ u : Raw n b, u.1 ≠ v → z u = y u) →
              parity z v = true → ∀ lit ∈ r.clause, parity z lit.1 ≠ lit.2 := by
            intro z hzoff hzpar lit hlit
            by_cases hlv : lit.1 = v
            · rcases lit with ⟨u, s⟩; dsimp only at hlv; subst hlv
              cases s
              · simp [hzpar]
              · exact absurd ⟨hlit, hvr⟩ (hNTr u)
            · have hmemR : lit ∈ R := Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun h => hlv (congrArg Prod.fst h), hlit⟩)
              have hp : parity z lit.1 = parity y lit.1 := parity_congr (fun j => hzoff ⟨lit.1, j⟩ hlv)
              rw [hp]; exact hy lit hmemR
          -- Helper to prove IsResolvent (liftClause C₀ y₀) (liftClause C₁ y₁) (liftClause R y ∪ fixedClause v (b-1) y')
          have hres_pair : ∀ (C₀ C₁ : Clause (Fin n)),
              (C₀ = l.clause ∧ C₁ = r.clause) ∨ (C₀ = r.clause ∧ C₁ = l.clause) →
              IsResolvent (liftClause C₀ y₀) (liftClause C₁ y₁) (liftClause R y ∪ fixedClause v (b - 1) y') := by
            intro C₀ C₁ hCD
            have hv0 : v ∈ C₀.image Prod.fst := by
              rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Finset.mem_image_of_mem Prod.fst hvl
              · exact Finset.mem_image_of_mem Prod.fst hvr
            have hv1 : v ∈ C₁.image Prod.fst := by
              rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Finset.mem_image_of_mem Prod.fst hvr
              · exact Finset.mem_image_of_mem Prod.fst hvl
            have hvarsCD : ∀ u : Fin n, u ≠ v →
                (u ∈ R.image Prod.fst ↔ u ∈ C₀.image Prod.fst ∨ u ∈ C₁.image Prod.fst) := by
              intro u huv
              rcases hCD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hvars u huv
              · rw [hvars u huv, or_comm]
            refine ⟨⟨v, j_last⟩, ?_, ?_, ?_⟩
            · rw [mem_liftClause]; exact ⟨hv0, by simp [y₀]⟩
            · rw [mem_liftClause]; exact ⟨hv1, by simp [y₁]⟩
            · ext ⟨u, s⟩
              simp only [Finset.mem_union, Finset.mem_erase, mem_liftClause, mem_fixedClause]
              by_cases huv : u.1 = v
              · rcases u with ⟨u1, j⟩; dsimp only at huv; subst u1
                constructor
                · rintro (⟨hR, _⟩ | ⟨j', hj', hEq, rfl⟩)
                  · exact absurd hR hv_nmem
                  · have hjj : j = j' := by simpa using hEq
                    subst hjj
                    have hjne : j ≠ j_last := by
                      intro h; have := congrArg Fin.val h; dsimp only [j_last] at this; omega
                    have hne_raw : (⟨v, j⟩ : Raw n b) ≠ ⟨v, j_last⟩ := fun h => hjne (by simpa using h)
                    left
                    refine ⟨fun h => hne_raw (congrArg Prod.fst h), hv0, ?_⟩
                    simp [y₀, Function.update_of_ne hne_raw]
                · rintro (⟨hne_lit, _, rfl⟩ | ⟨hne_lit, _, rfl⟩)
                  · have hjne : j ≠ j_last := by
                      intro h; subst h; apply hne_lit; simp [y₀]
                    have hjlt : j.val < b - 1 := by
                      have h1 : j.val < b := j.isLt
                      have h2 : j.val ≠ b - 1 := fun h => hjne (Fin.ext (by simpa [j_last] using h))
                      omega
                    have hne_raw : (⟨v, j⟩ : Raw n b) ≠ ⟨v, j_last⟩ := fun h => hjne (by simpa using h)
                    right; exact ⟨j, hjlt, rfl, by simp [y₀, Function.update_of_ne hne_raw]⟩
                  · have hjne : j ≠ j_last := by
                      intro h; subst h; apply hne_lit; simp [y₁]
                    have hjlt : j.val < b - 1 := by
                      have h1 : j.val < b := j.isLt
                      have h2 : j.val ≠ b - 1 := fun h => hjne (Fin.ext (by simpa [j_last] using h))
                      omega
                    have hne_raw : (⟨v, j⟩ : Raw n b) ≠ ⟨v, j_last⟩ := fun h => hjne (by simpa using h)
                    right; exact ⟨j, hjlt, rfl, by simp [y₁, Function.update_of_ne hne_raw]⟩
              · have hne_raw : u ≠ ⟨v, j_last⟩ := fun h => huv (congrArg Sigma.fst h)
                constructor
                · rintro (⟨huR, rfl⟩ | ⟨j', _, hEq, _⟩)
                  · rcases (hvarsCD u.1 huv).mp huR with h0 | h1
                    · left; exact ⟨fun h => hne_raw (congrArg Prod.fst h), h0, by rw [hy₀_off u huv]⟩
                    · right; exact ⟨fun h => hne_raw (congrArg Prod.fst h), h1, by rw [hy₁_off u huv]⟩
                  · exact absurd (congrArg Sigma.fst hEq) huv
                · rintro (⟨_, hu0, rfl⟩ | ⟨_, hu1, rfl⟩)
                  · left; exact ⟨(hvarsCD u.1 huv).mpr (Or.inl hu0), by rw [hy₀_off u huv]⟩
                  · left; exact ⟨(hvarsCD u.1 huv).mpr (Or.inr hu1), by rw [hy₁_off u huv]⟩
          by_cases hp0 : parity y₀ v = false
          · have hp1 : parity y₁ v = true := by
              cases h : parity y₁ v
              · exact absurd (hp0.trans h.symm) hpar_ne
              · rfl
            obtain ⟨N₀, J₀, line₀, hs₀, h0r, hh₀, hk₀, hl₀, hr₀⟩ :=
              ihl hVl y₀ (hfal_l y₀ hy₀_off hp0)
            obtain ⟨N₁, J₁, line₁, hs₁, h1r, hh₁, hk₁, hl₁, hr₁⟩ :=
              ihr hVr y₁ (hfal_r y₁ hy₁_off hp1)
            have hroot : IsResolvent (line₀ []) (line₁ []) (liftClause R y ∪ fixedClause v (b - 1) y') := by
              rw [h0r, h1r]; exact hres_pair l.clause r.clause (Or.inl ⟨rfl, rfl⟩)
            obtain ⟨N, J, line, hs, hrt, hh, hk, hl, hr⟩ :=
              mergeTree hs₀ hh₀ hk₀ hl₀ hr₀ hs₁ hh₁ hk₁ hl₁ hr₁ hroot
            exact ⟨N, J, line, hs, hrt, hh, by simpa using hk, hl, hr⟩
          · have hp0' : parity y₀ v = true := by
              cases h : parity y₀ v
              · exact absurd h hp0
              · rfl
            have hp1 : parity y₁ v = false := by
              cases h : parity y₁ v
              · rfl
              · exact absurd (hp0'.trans h.symm) hpar_ne
            obtain ⟨N₀, J₀, line₀, hs₀, h0r, hh₀, hk₀, hl₀, hr₀⟩ :=
              ihr hVr y₀ (hfal_r y₀ hy₀_off hp0')
            obtain ⟨N₁, J₁, line₁, hs₁, h1r, hh₁, hk₁, hl₁, hr₁⟩ :=
              ihl hVl y₁ (hfal_l y₁ hy₁_off hp1)
            have hroot : IsResolvent (line₀ []) (line₁ []) (liftClause R y ∪ fixedClause v (b - 1) y') := by
              rw [h0r, h1r]; exact hres_pair r.clause l.clause (Or.inr ⟨rfl, rfl⟩)
            obtain ⟨N, J, line, hs, hrt, hh, hk, hl, hr⟩ :=
              mergeTree hs₀ hh₀ hk₀ hl₀ hr₀ hs₁ hh₁ hk₁ hl₁ hr₁ hroot
            refine ⟨N, J, line, hs, hrt, ?_, ?_, hl, hr⟩
            · intro p hp; have := hh p hp; rw [max_comm] at this; exact this
            · rw [hk, add_comm]; simp
        | succ m'' =>
          -- m = m'' + 2 ≥ 2: resolve on j_cur = ⟨b - (m'' + 2), _⟩
          let k := b - (m'' + 2)
          let j_cur : Fin b := ⟨k, by omega⟩
          let y₀ := Function.update y' ⟨v, j_cur⟩ false
          let y₁ := Function.update y' ⟨v, j_cur⟩ true
          have hy₀_off : ∀ u : Raw n b, u.1 ≠ v → y₀ u = y u := by
            intro u hu
            have hne : u ≠ ⟨v, j_cur⟩ := fun h => hu (congrArg Sigma.fst h)
            dsimp only [y₀]; rw [Function.update_of_ne hne, hy'_off u hu]
          have hy₁_off : ∀ u : Raw n b, u.1 ≠ v → y₁ u = y u := by
            intro u hu
            have hne : u ≠ ⟨v, j_cur⟩ := fun h => hu (congrArg Sigma.fst h)
            dsimp only [y₁]; rw [Function.update_of_ne hne, hy'_off u hu]
          obtain ⟨N₀, J₀, line₀, hs₀, h0r, hh₀, hk₀, hl₀, hr₀⟩ :=
            ihm (by omega) (by omega) y₀ hy₀_off
          obtain ⟨N₁, J₁, line₁, hs₁, h1r, hh₁, hk₁, hl₁, hr₁⟩ :=
            ihm (by omega) (by omega) y₁ hy₁_off
          have hk_succ : b - (m'' + 1) = k + 1 := by dsimp [k]; omega
          have hroot : IsResolvent (line₀ []) (line₁ []) (liftClause R y ∪ fixedClause v k y') := by
            rw [h0r, h1r, hk_succ]
            refine ⟨⟨v, j_cur⟩, ?_, ?_, ?_⟩
            · apply Finset.mem_union_right
              rw [mem_fixedClause]; exact ⟨j_cur, by dsimp [j_cur]; omega, rfl, by simp [y₀]⟩
            · apply Finset.mem_union_right
              rw [mem_fixedClause]; exact ⟨j_cur, by dsimp [j_cur]; omega, rfl, by simp [y₁]⟩
            · ext ⟨u, s⟩
              simp only [Finset.mem_union, Finset.mem_erase, mem_liftClause, mem_fixedClause]
              by_cases huv : u.1 = v
              · rcases u with ⟨u1, j⟩; dsimp only at huv; subst u1
                constructor
                · rintro (⟨hR, _⟩ | ⟨j', hj', hEq, rfl⟩)
                  · exact absurd hR hv_nmem
                  · have hjj : j = j' := by simpa using hEq
                    subst hjj
                    have hjne : j ≠ j_cur := by
                      intro h; have := congrArg Fin.val h; dsimp [j_cur] at this; omega
                    have hne_raw : (⟨v, j⟩ : Raw n b) ≠ ⟨v, j_cur⟩ := fun h => hjne (by simpa using h)
                    left
                    refine ⟨fun h => hne_raw (congrArg Prod.fst h), Or.inr ⟨j, by omega, rfl, ?_⟩⟩
                    simp [y₀, Function.update_of_ne hne_raw]
                · rintro (⟨hne_lit, ⟨hR, _⟩ | ⟨j', hj', hEq, rfl⟩⟩ | ⟨hne_lit, ⟨hR, _⟩ | ⟨j', hj', hEq, rfl⟩⟩)
                  · exact absurd hR hv_nmem
                  · have hjj : j = j' := by simpa using hEq
                    subst hjj
                    have hjne : j ≠ j_cur := by intro h; subst h; apply hne_lit; simp [y₀]
                    have hjlt : j.val < k := by
                      have : j.val ≠ k := fun h => hjne (Fin.ext h); omega
                    have hne_raw : (⟨v, j⟩ : Raw n b) ≠ ⟨v, j_cur⟩ := fun h => hjne (by simpa using h)
                    right; exact ⟨j, hjlt, rfl, by simp [y₀, Function.update_of_ne hne_raw]⟩
                  · exact absurd hR hv_nmem
                  · have hjj : j = j' := by simpa using hEq
                    subst hjj
                    have hjne : j ≠ j_cur := by intro h; subst h; apply hne_lit; simp [y₁]
                    have hjlt : j.val < k := by
                      have : j.val ≠ k := fun h => hjne (Fin.ext h); omega
                    have hne_raw : (⟨v, j⟩ : Raw n b) ≠ ⟨v, j_cur⟩ := fun h => hjne (by simpa using h)
                    right; exact ⟨j, hjlt, rfl, by simp [y₁, Function.update_of_ne hne_raw]⟩
              · have hne_raw : u ≠ ⟨v, j_cur⟩ := fun h => huv (congrArg Sigma.fst h)
                constructor
                · rintro (⟨huR, rfl⟩ | ⟨j', _, hEq, _⟩)
                  · left; exact ⟨fun h => hne_raw (congrArg Prod.fst h), Or.inl ⟨huR, rfl⟩⟩
                  · exact absurd (congrArg Sigma.fst hEq) huv
                · rintro (⟨_, ⟨huR, rfl⟩ | ⟨j', _, hEq, _⟩⟩ | ⟨_, ⟨huR, rfl⟩ | ⟨j', _, hEq, _⟩⟩)
                  · left; exact ⟨huR, rfl⟩
                  · exact absurd (congrArg Sigma.fst hEq) huv
                  · left; exact ⟨huR, rfl⟩
                  · exact absurd (congrArg Sigma.fst hEq) huv
          obtain ⟨N, J, line, hs, hrt, hh, hk, hl, hr⟩ :=
            mergeTree hs₀ hh₀ hk₀ hl₀ hr₀ hs₁ hh₁ hk₁ hl₁ hr₁ hroot
          refine ⟨N, J, line, hs, hrt, ?_, ?_, hl, hr⟩
          · intro p hp; have := hh p hp; simp only [max_self] at this; omega
          · rw [hk]
            have hpow : 2 ^ (m'' + 1) = 2 ^ m'' + 2 ^ m'' := by rw [pow_succ]; ring
            change 2 ^ m'' * _ + 2 ^ m'' * _ = 2 ^ (m'' + 1) * _
            rw [hpow, Nat.add_mul]
    obtain ⟨N, J, line, hs, hrt, hh, hk, hl, hr⟩ := hgad b hb (le_refl b) y (fun _ _ => rfl)
    have hfix0 : fixedClause v (b - b) y = ∅ := by simp [fixedClause]
    rw [hfix0, Finset.union_empty] at hrt
    refine ⟨N, J, line, hs, hrt, ?_, ?_, hl, hr⟩
    · intro p hp
      have := hh p hp
      have hmul : b * (1 + max l.height r.height) = b + max (b * l.height) (b * r.height) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_max_mul_left]
      simpa [OuterTree.height, hmul] using this
    · simpa [OuterTree.cost] using hk

/-! ## Section 3: Upper Bound (`⇐`) — Outer Tree 1 and Outer Tree 2 -/

private lemma nonTaut_pair {u v : Fin n} {s₁ s₂ : Bool} (huv : u ≠ v) :
    NonTaut ({(u, s₁), (v, s₂)} : Clause (Fin n)) := by
  intro i ⟨hT, hF⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hT hF
  rcases hT with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases hF with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · exact Bool.noConfusion (h1.trans h3.symm)
  · exact huv h2
  · exact huv h2.symm
  · exact Bool.noConfusion (h1.trans h3.symm)

private lemma nonTaut_singleton (u : Fin n) (s : Bool) :
    NonTaut ({(u, s)} : Clause (Fin n)) := by
  intro i ⟨hT, hF⟩
  simp only [Finset.mem_singleton, Prod.mk.injEq] at hT hF
  exact Bool.noConfusion (hT.2.trans hF.2.symm)

private lemma nonTaut_empty : NonTaut (∅ : Clause (Fin n)) := by
  intro i ⟨hT, _⟩; simp at hT

-- Balanced chain tree on [a, c) for 0 ≤ a < c < n: derives {(atV a, false), (atV c, true)}
private lemma build_chain (_hn2 : 2 ≤ n) (base : ℕ) :
    ∀ (L : ℕ), 1 ≤ L → ∀ (a c : ℕ), c - a = L → c < n →
      ∃ T : OuterTree n, T.Valid (cycF hn) ∧
        T.clause = {(atV hn a, false), (atV hn c, true)} ∧
        T.height ≤ Nat.clog 2 L ∧ T.cost base = bal base L := by
  intro L
  induction L using Nat.strong_induction_on with
  | ind L ih =>
    intro hL a c hdiff hc
    by_cases hL1 : L = 1
    · have hc_eq : c = a + 1 := by omega
      subst hc_eq
      refine ⟨.leaf {(atV hn a, false), (atV hn (a + 1), true)}, ?_, rfl, Nat.zero_le _, ?_⟩
      · refine ⟨Or.inr (Or.inr (Or.inr ⟨a, hc, rfl⟩)), nonTaut_pair ?_⟩
        intro h; have := atV_inj hn (by omega) hc h; omega
      · rw [hL1, bal_one]; rfl
    · have hL2 : 2 ≤ L := by omega
      let L₁ := L / 2
      let L₂ := L - L₁
      let m := a + L₁
      have hL₁_pos : 1 ≤ L₁ := by omega
      have hL₂_pos : 1 ≤ L₂ := by omega
      obtain ⟨T₁, hV₁, hC₁, hH₁, hK₁⟩ := ih L₁ (by omega) hL₁_pos a m (by omega) (by omega)
      obtain ⟨T₂, hV₂, hC₂, hH₂, hK₂⟩ := ih L₂ (by omega) hL₂_pos m c (by omega) hc
      have hma : atV hn m ≠ atV hn a := fun h => by
        have := atV_inj hn (by omega) (by omega) h; omega
      have hmc : atV hn m ≠ atV hn c := fun h => by
        have := atV_inj hn (by omega) hc h; omega
      have hac : atV hn a ≠ atV hn c := fun h => by
        have := atV_inj hn (by omega) hc h; omega
      have hcl : (OuterTree.node (atV hn m) T₁ T₂).clause =
          {(atV hn a, false), (atV hn c, true)} := by
        simp only [OuterTree.clause, hC₁, hC₂]
        ext ⟨u, s⟩
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro (⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
          · exact Or.inl ⟨rfl, rfl⟩
          · exact absurd rfl hne
          · exact absurd rfl hne
          · exact Or.inr ⟨rfl, rfl⟩
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · left; exact ⟨fun h => hma (congrArg Prod.fst h).symm, Or.inl ⟨rfl, rfl⟩⟩
          · right; exact ⟨fun h => hmc (congrArg Prod.fst h).symm, Or.inr ⟨rfl, rfl⟩⟩
      refine ⟨.node (atV hn m) T₁ T₂, ?_, hcl, ?_, ?_⟩
      · refine ⟨hV₁, hV₂, ?_, ?_, ?_⟩
        · rw [hC₁]; simp
        · rw [hC₂]; simp
        · rw [← OuterTree.clause, hcl]; exact nonTaut_pair hac
      · have hhi : L ≤ 2 ^ Nat.clog 2 L := le_pow_clog L
        have hhd : 1 ≤ Nat.clog 2 L := Nat.clog_pos (by decide) (by omega)
        have h2d : 2 ^ Nat.clog 2 L = 2 * 2 ^ (Nat.clog 2 L - 1) := by
          have : Nat.clog 2 L = (Nat.clog 2 L - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ]
          ring
        have hcs := clog_split_le (m := L) (a := L₁) (c := L₂) hL2 (by omega) (by omega) (by omega)
        simp only [OuterTree.height]
        omega
      · simp only [OuterTree.cost, hK₁, hK₂]
        have hlo : 2 ^ (Nat.clog 2 L - 1) < L := pow_pred_lt_of_clog hL2
        have hhi : L ≤ 2 ^ Nat.clog 2 L := le_pow_clog L
        have hd1 : 1 ≤ Nat.clog 2 L := Nat.clog_pos (by decide) (by omega)
        have h2d : 2 ^ Nat.clog 2 L = 2 * 2 ^ (Nat.clog 2 L - 1) := by
          have : Nat.clog 2 L = (Nat.clog 2 L - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ]
          ring
        have hlo2 : 2 ^ (Nat.clog 2 L - 2) ≤ L₁ ∧ 2 ^ (Nat.clog 2 L - 2) ≤ L₂ := by
          by_cases hd2 : Nat.clog 2 L = 1
          · rw [hd2]; simp; omega
          · have h2d1 : 2 ^ (Nat.clog 2 L - 1) = 2 * 2 ^ (Nat.clog 2 L - 2) := by
              have : Nat.clog 2 L - 1 = (Nat.clog 2 L - 2) + 1 := by omega
              conv_lhs => rw [this, pow_succ]
              ring
            omega
        exact (bal_split_eq hL2 (by omega) hlo2.1 (by omega) hlo2.2 (by omega)).symm

-- Balanced right-closed tree on [a, n) for 0 ≤ a < n: derives {(atV a, false), (first, false)}
private lemma build_chain_close (hn2 : 2 ≤ n) (base : ℕ) :
    ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ), n - a = L → a < n →
      ∃ T : OuterTree n, T.Valid (cycF hn) ∧
        T.clause = {(atV hn a, false), (first hn, false)} ∧
        T.height ≤ Nat.clog 2 L ∧ T.cost base = bal base L := by
  intro L
  induction L using Nat.strong_induction_on with
  | ind L ih =>
    intro hL a hdiff ha
    by_cases hL1 : L = 1
    · have ha_eq : a = n - 1 := by omega
      subst ha_eq
      refine ⟨.leaf {(last hn, false), (first hn, false)}, ?_, rfl, Nat.zero_le _, ?_⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), nonTaut_pair (first_ne_last hn hn2).symm⟩
      · rw [hL1, bal_one]; rfl
    · have hL2 : 2 ≤ L := by omega
      let L₁ := L / 2
      let L₂ := L - L₁
      let m := a + L₁
      obtain ⟨T₁, hV₁, hC₁, hH₁, hK₁⟩ := build_chain hn hn2 base L₁ (by omega) a m (by omega) (by omega)
      obtain ⟨T₂, hV₂, hC₂, hH₂, hK₂⟩ := ih L₂ (by omega) (by omega) m (by omega) (by omega)
      have hma : atV hn m ≠ atV hn a := fun h => by
        have := atV_inj hn (by omega) ha h; omega
      have hm0 : atV hn m ≠ first hn := fun h => by
        have := atV_inj hn (by omega) (by omega) h; omega
      have hcl : (OuterTree.node (atV hn m) T₁ T₂).clause =
          {(atV hn a, false), (first hn, false)} := by
        simp only [OuterTree.clause, hC₁, hC₂]
        ext ⟨u, s⟩
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro (⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
          · exact Or.inl ⟨rfl, rfl⟩
          · exact absurd rfl hne
          · exact absurd rfl hne
          · exact Or.inr ⟨rfl, rfl⟩
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · left; exact ⟨fun h => hma (congrArg Prod.fst h).symm, Or.inl ⟨rfl, rfl⟩⟩
          · right; exact ⟨fun h => hm0 (congrArg Prod.fst h).symm, Or.inr ⟨rfl, rfl⟩⟩
      refine ⟨.node (atV hn m) T₁ T₂, ?_, hcl, ?_, ?_⟩
      · refine ⟨hV₁, hV₂, ?_, ?_, ?_⟩
        · rw [hC₁]; simp
        · rw [hC₂]; simp
        · rw [← OuterTree.clause, hcl]
          by_cases ha0 : atV hn a = first hn
          · rw [ha0, Finset.pair_eq_singleton]; exact nonTaut_singleton _ _
          · exact nonTaut_pair ha0
      · have hhi : L ≤ 2 ^ Nat.clog 2 L := le_pow_clog L
        have hhd : 1 ≤ Nat.clog 2 L := Nat.clog_pos (by decide) (by omega)
        have h2d : 2 ^ Nat.clog 2 L = 2 * 2 ^ (Nat.clog 2 L - 1) := by
          have : Nat.clog 2 L = (Nat.clog 2 L - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ]
          ring
        have hcs := clog_split_le (m := L) (a := L₁) (c := L₂) hL2 (by omega) (by omega) (by omega)
        simp only [OuterTree.height]; omega
      · simp only [OuterTree.cost, hK₁, hK₂]
        have hlo : 2 ^ (Nat.clog 2 L - 1) < L := pow_pred_lt_of_clog hL2
        have hhi : L ≤ 2 ^ Nat.clog 2 L := le_pow_clog L
        have hd1 : 1 ≤ Nat.clog 2 L := Nat.clog_pos (by decide) (by omega)
        have h2d : 2 ^ Nat.clog 2 L = 2 * 2 ^ (Nat.clog 2 L - 1) := by
          have : Nat.clog 2 L = (Nat.clog 2 L - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ]
          ring
        have hlo2 : 2 ^ (Nat.clog 2 L - 2) ≤ L₁ ∧ 2 ^ (Nat.clog 2 L - 2) ≤ L₂ := by
          by_cases hd2 : Nat.clog 2 L = 1
          · rw [hd2]; simp; omega
          · have h2d1 : 2 ^ (Nat.clog 2 L - 1) = 2 * 2 ^ (Nat.clog 2 L - 2) := by
              have : Nat.clog 2 L - 1 = (Nat.clog 2 L - 2) + 1 := by omega
              conv_lhs => rw [this, pow_succ]
              ring
            omega
        exact (bal_split_eq hL2 (by omega) hlo2.1 (by omega) hlo2.2 (by omega)).symm

-- Outer Tree 1 (Branch 1)
private lemma build_outerTree1 (hn2 : 2 ≤ n) (base : ℕ) :
    ∃ T : OuterTree n, T.Valid (cycF hn) ∧ T.clause = ∅ ∧
      T.height ≤ 1 + Nat.clog 2 n ∧ T.cost base = base * (2 * base + bal base n) := by
  let T_left : OuterTree n :=
    .node (last hn) (.leaf {(last hn, true), (first hn, true)})
                    (.leaf {(last hn, false), (first hn, true)})
  have hfl : first hn ≠ last hn := first_ne_last hn hn2
  have hCl : T_left.clause = {(first hn, true)} := by
    simp only [T_left, OuterTree.clause]
    ext ⟨u, s⟩
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro (⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
      · exact absurd rfl hne
      · exact ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      left; exact ⟨fun h => hfl (congrArg Prod.fst h), Or.inr ⟨rfl, rfl⟩⟩
  have hVl : T_left.Valid (cycF hn) := by
    refine ⟨⟨Or.inl rfl, nonTaut_pair hfl.symm⟩, ⟨Or.inr (Or.inl rfl), nonTaut_pair hfl.symm⟩,
      by simp [OuterTree.clause], by simp [OuterTree.clause], ?_⟩
    rw [← OuterTree.clause, hCl]; exact nonTaut_singleton _ _
  obtain ⟨T_right, hVr, hCr, hHr, hKr⟩ := build_chain_close hn hn2 base n (by omega) 0 (by omega) (by omega)
  have hCr' : T_right.clause = {(first hn, false)} := by
    rw [hCr]; simp [first]
  have hcl : (OuterTree.node (first hn) T_left T_right).clause = ∅ := by
    simp only [OuterTree.clause, hCl, hCr']; simp
  refine ⟨.node (first hn) T_left T_right, ?_, hcl, ?_, ?_⟩
  · refine ⟨hVl, hVr, ?_, ?_, ?_⟩
    · rw [hCl]; simp
    · rw [hCr']; simp
    · rw [← OuterTree.clause, hcl]; exact nonTaut_empty
  · have hc1 : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by decide) (by omega)
    simp only [OuterTree.height, T_left]
    omega
  · simp only [OuterTree.cost, T_left, hKr]
    ring

-- Balanced left-closed tree on [0, r) for 2 ≤ r ≤ n + 1: derives {(atV (r - 2), true)}
private lemma build_left_closed (hn2 : 2 ≤ n) (base : ℕ) :
    ∀ (r : ℕ), 2 ≤ r → r ≤ n + 1 →
      ∃ T : OuterTree n, T.Valid (cycF hn) ∧
        T.clause = {(atV hn (r - 2), true)} ∧
        T.height ≤ Nat.clog 2 r ∧ T.cost base = bal base r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr2 hrn
    by_cases hr_eq2 : r = 2
    · subst hr_eq2
      have hfl : first hn ≠ last hn := first_ne_last hn hn2
      let T : OuterTree n :=
        .node (last hn) (.leaf {(last hn, true), (first hn, true)})
                        (.leaf {(last hn, false), (first hn, true)})
      have hC : T.clause = {(atV hn 0, true)} := by
        simp only [T, OuterTree.clause, first]
        ext ⟨u, s⟩
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro (⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
          · exact absurd rfl hne
          · exact ⟨rfl, rfl⟩
          · exact absurd rfl hne
          · exact ⟨rfl, rfl⟩
        · rintro ⟨rfl, rfl⟩
          left; exact ⟨fun h => hfl (congrArg Prod.fst h), Or.inr ⟨rfl, rfl⟩⟩
      refine ⟨T, ?_, hC, by simp [T, OuterTree.height, show Nat.clog 2 2 = 1 by decide], ?_⟩
      · refine ⟨⟨Or.inl rfl, nonTaut_pair hfl.symm⟩, ⟨Or.inr (Or.inl rfl), nonTaut_pair hfl.symm⟩,
          by simp [OuterTree.clause], by simp [OuterTree.clause], ?_⟩
        rw [← OuterTree.clause, hC]; exact nonTaut_singleton _ _
      · simp [T, OuterTree.cost, bal_two]; ring
    · have hr3 : 3 ≤ r := by omega
      let m := if r = 3 then 2 else r / 2
      have hm_lo : 2 ≤ m := by dsimp [m]; split_ifs <;> omega
      have hm_hi : m < r := by dsimp [m]; split_ifs <;> omega
      obtain ⟨T₁, hV₁, hC₁, hH₁, hK₁⟩ := ih m hm_hi hm_lo (by omega)
      obtain ⟨T₂, hV₂, hC₂, hH₂, hK₂⟩ :=
        build_chain hn hn2 base (r - m) (by omega) (m - 2) (r - 2) (by omega) (by omega)
      have hmr : atV hn (m - 2) ≠ atV hn (r - 2) := fun h => by
        have := atV_inj hn (by omega) (by omega) h; omega
      have hcl : (OuterTree.node (atV hn (m - 2)) T₁ T₂).clause = {(atV hn (r - 2), true)} := by
        simp only [OuterTree.clause, hC₁, hC₂]
        ext ⟨u, s⟩
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro (⟨hne, ⟨rfl, rfl⟩⟩ | ⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
          · exact absurd rfl hne
          · exact absurd rfl hne
          · exact ⟨rfl, rfl⟩
        · rintro ⟨rfl, rfl⟩
          right; exact ⟨fun h => hmr (congrArg Prod.fst h).symm, Or.inr ⟨rfl, rfl⟩⟩
      have hlo : 2 ^ (Nat.clog 2 r - 1) < r := pow_pred_lt_of_clog (by omega)
      have hhi : r ≤ 2 ^ Nat.clog 2 r := le_pow_clog r
      have hd2 : 2 ≤ Nat.clog 2 r := by
        by_contra hlt
        have : Nat.clog 2 r ≤ 1 := by omega
        have := le_trans hhi (Nat.pow_le_pow_right (by decide) this)
        omega
      have h2d : 2 ^ Nat.clog 2 r = 2 * 2 ^ (Nat.clog 2 r - 1) := by
        have : Nat.clog 2 r = (Nat.clog 2 r - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        ring
      have h2d1 : 2 ^ (Nat.clog 2 r - 1) = 2 * 2 ^ (Nat.clog 2 r - 2) := by
        have : Nat.clog 2 r - 1 = (Nat.clog 2 r - 2) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        ring
      have hbounds : 2 ^ (Nat.clog 2 r - 2) ≤ m ∧ m ≤ 2 ^ (Nat.clog 2 r - 1) ∧
          2 ^ (Nat.clog 2 r - 2) ≤ r - m ∧ r - m ≤ 2 ^ (Nat.clog 2 r - 1) := by
        by_cases hr_eq3 : r = 3
        · subst hr_eq3
          dsimp [m]; simp only [↓reduceIte, show Nat.clog 2 3 = 2 by decide]; omega
        · dsimp [m]; simp only [hr_eq3, ↓reduceIte]; omega
      refine ⟨.node (atV hn (m - 2)) T₁ T₂, ?_, hcl, ?_, ?_⟩
      · refine ⟨hV₁, hV₂, ?_, ?_, ?_⟩
        · rw [hC₁]; simp
        · rw [hC₂]; simp
        · rw [← OuterTree.clause, hcl]; exact nonTaut_singleton _ _
      · have hcs := clog_split_le (m := r) (a := m) (c := r - m) (by omega) (by omega)
          hbounds.2.1 hbounds.2.2.2
        simp only [OuterTree.height]; omega
      · simp only [OuterTree.cost, hK₁, hK₂]
        exact (bal_split_eq (by omega) (by omega) hbounds.1 hbounds.2.1
          hbounds.2.2.1 hbounds.2.2.2).symm

-- Balanced right-closed tree on [l, n + 3) for 2 ≤ l ≤ n + 1: derives {(atV (l - 2), false)}
private lemma build_right_closed (hn2 : 2 ≤ n) (base : ℕ) :
    ∀ (L : ℕ), 2 ≤ L → L ≤ n + 1 →
      ∃ T : OuterTree n, T.Valid (cycF hn) ∧
        T.clause = {(atV hn (n + 1 - L), false)} ∧
        T.height ≤ Nat.clog 2 L ∧ T.cost base = bal base L := by
  intro L
  induction L using Nat.strong_induction_on with
  | ind L ih =>
    intro hL2 hLn
    by_cases hL_eq2 : L = 2
    · subst hL_eq2
      have hfl : first hn ≠ last hn := first_ne_last hn hn2
      let T : OuterTree n :=
        .node (first hn) (.leaf {(last hn, false), (first hn, true)})
                         (.leaf {(last hn, false), (first hn, false)})
      have hC : T.clause = {(atV hn (n + 1 - 2), false)} := by
        have hsub : n + 1 - 2 = n - 1 := by omega
        rw [hsub]
        simp only [T, OuterTree.clause, last]
        ext ⟨u, s⟩
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro (⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
          · exact ⟨rfl, rfl⟩
          · exact absurd rfl hne
          · exact ⟨rfl, rfl⟩
          · exact absurd rfl hne
        · rintro ⟨rfl, rfl⟩
          left; exact ⟨fun h => hfl (congrArg Prod.fst h).symm, Or.inl ⟨rfl, rfl⟩⟩
      refine ⟨T, ?_, hC, by simp [T, OuterTree.height, show Nat.clog 2 2 = 1 by decide], ?_⟩
      · refine ⟨⟨Or.inr (Or.inl rfl), nonTaut_pair hfl.symm⟩,
          ⟨Or.inr (Or.inr (Or.inl rfl)), nonTaut_pair hfl.symm⟩,
          by simp [OuterTree.clause], by simp [OuterTree.clause], ?_⟩
        rw [← OuterTree.clause, hC]; exact nonTaut_singleton _ _
      · simp [T, OuterTree.cost, bal_two]; ring
    · have hL3 : 3 ≤ L := by omega
      let L₂ := if L = 3 then 2 else L / 2
      let L₁ := L - L₂
      have hL₂_lo : 2 ≤ L₂ := by dsimp [L₂]; split_ifs <;> omega
      have hL₂_hi : L₂ < L := by dsimp [L₂]; split_ifs <;> omega
      obtain ⟨T₁, hV₁, hC₁, hH₁, hK₁⟩ :=
        build_chain hn hn2 base L₁ (by omega) (n + 1 - L) (n + 1 - L₂) (by omega) (by omega)
      obtain ⟨T₂, hV₂, hC₂, hH₂, hK₂⟩ := ih L₂ hL₂_hi hL₂_lo (by omega)
      have hne : atV hn (n + 1 - L₂) ≠ atV hn (n + 1 - L) := fun h => by
        have := atV_inj hn (by omega) (by omega) h; omega
      have hcl : (OuterTree.node (atV hn (n + 1 - L₂)) T₁ T₂).clause =
          {(atV hn (n + 1 - L), false)} := by
        simp only [OuterTree.clause, hC₁, hC₂]
        ext ⟨u, s⟩
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro (⟨hne', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hne', ⟨rfl, rfl⟩⟩)
          · exact ⟨rfl, rfl⟩
          · exact absurd rfl hne'
          · exact absurd rfl hne'
        · rintro ⟨rfl, rfl⟩
          left; exact ⟨fun h => hne (congrArg Prod.fst h).symm, Or.inl ⟨rfl, rfl⟩⟩
      have hlo : 2 ^ (Nat.clog 2 L - 1) < L := pow_pred_lt_of_clog (by omega)
      have hhi : L ≤ 2 ^ Nat.clog 2 L := le_pow_clog L
      have hd2 : 2 ≤ Nat.clog 2 L := by
        by_contra hlt
        have : Nat.clog 2 L ≤ 1 := by omega
        have := le_trans hhi (Nat.pow_le_pow_right (by decide) this)
        omega
      have h2d : 2 ^ Nat.clog 2 L = 2 * 2 ^ (Nat.clog 2 L - 1) := by
        have : Nat.clog 2 L = (Nat.clog 2 L - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        ring
      have h2d1 : 2 ^ (Nat.clog 2 L - 1) = 2 * 2 ^ (Nat.clog 2 L - 2) := by
        have : Nat.clog 2 L - 1 = (Nat.clog 2 L - 2) + 1 := by omega
        conv_lhs => rw [this, pow_succ]
        ring
      have hbounds : 2 ^ (Nat.clog 2 L - 2) ≤ L₁ ∧ L₁ ≤ 2 ^ (Nat.clog 2 L - 1) ∧
          2 ^ (Nat.clog 2 L - 2) ≤ L₂ ∧ L₂ ≤ 2 ^ (Nat.clog 2 L - 1) := by
        by_cases hL_eq3 : L = 3
        · subst hL_eq3
          dsimp [L₁, L₂]; simp only [↓reduceIte, show Nat.clog 2 3 = 2 by decide]; omega
        · dsimp [L₁, L₂]; simp only [hL_eq3, ↓reduceIte]; omega
      refine ⟨.node (atV hn (n + 1 - L₂)) T₁ T₂, ?_, hcl, ?_, ?_⟩
      · refine ⟨hV₁, hV₂, ?_, ?_, ?_⟩
        · rw [hC₁]; simp
        · rw [hC₂]; simp
        · rw [← OuterTree.clause, hcl]; exact nonTaut_singleton _ _
      · have hcs := clog_split_le (m := L) (a := L₁) (c := L₂) (by omega) (by omega)
          hbounds.2.1 hbounds.2.2.2
        simp only [OuterTree.height]; omega
      · simp only [OuterTree.cost, hK₁, hK₂]
        exact (bal_split_eq (by omega) (by omega) hbounds.1 hbounds.2.1
          hbounds.2.2.1 hbounds.2.2.2).symm

-- Outer Tree 2 (Branch 2)
private lemma build_outerTree2 (hn2 : 2 ≤ n) (base : ℕ) :
    ∃ T : OuterTree n, T.Valid (cycF hn) ∧ T.clause = ∅ ∧
      T.height ≤ Nat.clog 2 (n + 3) ∧ T.cost base = bal base (n + 3) := by
  let r := (n + 3) / 2
  let L := n + 3 - r
  have hr2 : 2 ≤ r := by omega
  have hrn : r ≤ n + 1 := by omega
  have hL2 : 2 ≤ L := by omega
  have hLn : L ≤ n + 1 := by omega
  have hidx : n + 1 - L = r - 2 := by omega
  obtain ⟨T₁, hV₁, hC₁, hH₁, hK₁⟩ := build_left_closed hn hn2 base r hr2 hrn
  obtain ⟨T₂, hV₂, hC₂, hH₂, hK₂⟩ := build_right_closed hn hn2 base L hL2 hLn
  rw [hidx] at hC₂
  have hcl : (OuterTree.node (atV hn (r - 2)) T₁ T₂).clause = ∅ := by
    simp only [OuterTree.clause, hC₁, hC₂]; simp
  have hlo : 2 ^ (Nat.clog 2 (n + 3) - 1) < n + 3 := pow_pred_lt_of_clog (by omega)
  have hhi : n + 3 ≤ 2 ^ Nat.clog 2 (n + 3) := le_pow_clog (n + 3)
  have hd3 : 3 ≤ Nat.clog 2 (n + 3) := by
    by_contra hlt
    have : Nat.clog 2 (n + 3) ≤ 2 := by omega
    have := le_trans hhi (Nat.pow_le_pow_right (by decide) this)
    omega
  have h2d : 2 ^ Nat.clog 2 (n + 3) = 2 * 2 ^ (Nat.clog 2 (n + 3) - 1) := by
    have : Nat.clog 2 (n + 3) = (Nat.clog 2 (n + 3) - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  have h2d1 : 2 ^ (Nat.clog 2 (n + 3) - 1) = 2 * 2 ^ (Nat.clog 2 (n + 3) - 2) := by
    have : Nat.clog 2 (n + 3) - 1 = (Nat.clog 2 (n + 3) - 2) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  refine ⟨.node (atV hn (r - 2)) T₁ T₂, ?_, hcl, ?_, ?_⟩
  · refine ⟨hV₁, hV₂, ?_, ?_, ?_⟩
    · rw [hC₁]; simp
    · rw [hC₂]; simp
    · rw [← OuterTree.clause, hcl]; exact nonTaut_empty
  · have hcs := clog_split_le (m := n + 3) (a := r) (c := L) (by omega) (by omega)
      (by omega) (by omega)
    simp only [OuterTree.height]; omega
  · simp only [OuterTree.cost, hK₁, hK₂]
    exact (bal_split_eq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm

/-! ## Section 4: Lower Bound (`⇒`) via Critical Assignments and `deficit` Potential -/

private def Falsifies (ρ : Raw n b → Option Bool) (A : Clause (Raw n b)) : Prop :=
  ∀ lit ∈ A, ρ lit.1 = some (!lit.2)

private def rem (ρ : Raw n b → Option Bool) (i : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin b)).filter (fun j => ρ ⟨i, j⟩ = none)).card

private def par (ρ : Raw n b → Option Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin b)).filter (fun j => ρ ⟨i, j⟩ = some true)).card)

private def deficit (ρ : Raw n b → Option Bool) : ℕ :=
  ∑ i : Fin n, if 0 < rem ρ i then b - rem ρ i else 0

private lemma rem_le_b (ρ : Raw n b → Option Bool) (i : Fin n) : rem ρ i ≤ b := by
  calc rem ρ i ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_filter_le _ _
    _ = b := Fintype.card_fin b

private lemma rem_empty (i : Fin n) : rem (fun _ : Raw n b => (none : Option Bool)) i = b := by
  simp [rem]

private lemma deficit_empty (hb : 0 < b) :
    deficit (fun _ : Raw n b => (none : Option Bool)) = 0 := by
  simp [deficit, rem_empty, hb]

private lemma rem_update_ne (ρ : Raw n b → Option Bool) (v : Fin n) (j : Fin b) (val : Bool)
    {u : Fin n} (huv : u ≠ v) :
    rem (Function.update ρ ⟨v, j⟩ (some val)) u = rem ρ u := by
  unfold rem; congr 1; ext j'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : (⟨u, j'⟩ : Raw n b) ≠ ⟨v, j⟩ := fun h => huv (congrArg Sigma.fst h)
  rw [Function.update_of_ne hne]

private lemma rem_update_eq (ρ : Raw n b → Option Bool) (v : Fin n) (j : Fin b) (val : Bool)
    (hnone : ρ ⟨v, j⟩ = none) :
    rem (Function.update ρ ⟨v, j⟩ (some val)) v + 1 = rem ρ v := by
  unfold rem
  let s := (Finset.univ : Finset (Fin b)).filter (fun j' => ρ ⟨v, j'⟩ = none)
  let s' := (Finset.univ : Finset (Fin b)).filter
    (fun j' => Function.update ρ ⟨v, j⟩ (some val) ⟨v, j'⟩ = none)
  have hj_mem : j ∈ s := by simp [s, hnone]
  have hs'_eq : s' = s.erase j := by
    ext j'
    simp only [s', s, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hjj : j' = j
    · subst hjj; simp
    · simp [hjj]
  change s'.card + 1 = s.card
  rw [hs'_eq, Finset.card_erase_add_one hj_mem]

private lemma par_update_ne (ρ : Raw n b → Option Bool) (v : Fin n) (j : Fin b) (val : Bool)
    {u : Fin n} (huv : u ≠ v) :
    par (Function.update ρ ⟨v, j⟩ (some val)) u = par ρ u := by
  unfold par; congr 1; congr 1; congr 1; congr 1; ext j'
  have hne : (⟨u, j'⟩ : Raw n b) ≠ ⟨v, j⟩ := fun h => huv (congrArg Sigma.fst h)
  simp [Function.update_of_ne hne]

private lemma par_update_flip (ρ : Raw n b → Option Bool) (v : Fin n) (j : Fin b) :
    par (Function.update ρ ⟨v, j⟩ (some false)) v ≠
    par (Function.update ρ ⟨v, j⟩ (some true)) v := by
  unfold par
  let s₀ := (Finset.univ : Finset (Fin b)).filter
    (fun j' => Function.update ρ ⟨v, j⟩ (some false) ⟨v, j'⟩ = some true)
  let s₁ := (Finset.univ : Finset (Fin b)).filter
    (fun j' => Function.update ρ ⟨v, j⟩ (some true) ⟨v, j'⟩ = some true)
  have hj0 : j ∉ s₀ := by simp [s₀]
  have hs1 : s₁ = insert j s₀ := by
    ext j'
    simp only [s₁, s₀, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hjj : j' = j
    · subst hjj; simp
    · have hne : (⟨v, j'⟩ : Raw n b) ≠ ⟨v, j⟩ := fun h => hjj (by simpa using h)
      simp only [hjj, false_or, Function.update_of_ne hne]
  have hcard : s₁.card = s₀.card + 1 := by rw [hs1, Finset.card_insert_of_notMem hj0]
  change decide (Odd s₀.card) ≠ decide (Odd s₁.card)
  rw [hcard]
  intro h
  have hiff : Odd s₀.card ↔ Odd (s₀.card + 1) := by simpa using h
  rw [Nat.odd_add_one] at hiff
  exact iff_not_self hiff

private lemma deficit_update_ge2 (ρ : Raw n b → Option Bool) (v : Fin n) (j : Fin b) (val : Bool)
    (hnone : ρ ⟨v, j⟩ = none) (hge : 2 ≤ rem ρ v) :
    deficit (Function.update ρ ⟨v, j⟩ (some val)) = deficit ρ + 1 := by
  let ρ' := Function.update ρ ⟨v, j⟩ (some val)
  change deficit ρ' = deficit ρ + 1
  have hrem_v : rem ρ' v + 1 = rem ρ v := rem_update_eq ρ v j val hnone
  have hrem_le : rem ρ v ≤ b := rem_le_b ρ v
  unfold deficit
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  have hrest : ∑ i ∈ Finset.univ.erase v, (if 0 < rem ρ' i then b - rem ρ' i else 0) =
      ∑ i ∈ Finset.univ.erase v, (if 0 < rem ρ i then b - rem ρ i else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [rem_update_ne ρ v j val (Finset.ne_of_mem_erase hi)]
  rw [hrest]
  have h1 : 0 < rem ρ' v := by omega
  have h2 : 0 < rem ρ v := by omega
  simp only [h1, h2, ↓reduceIte]
  omega

private lemma deficit_update_eq1 (ρ : Raw n b → Option Bool) (v : Fin n) (j : Fin b) (val : Bool)
    (hnone : ρ ⟨v, j⟩ = none) (heq1 : rem ρ v = 1) :
    deficit ρ = deficit (Function.update ρ ⟨v, j⟩ (some val)) + (b - 1) := by
  let ρ' := Function.update ρ ⟨v, j⟩ (some val)
  change deficit ρ = deficit ρ' + (b - 1)
  have hrem_v : rem ρ' v + 1 = rem ρ v := rem_update_eq ρ v j val hnone
  unfold deficit
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  have hrest : ∑ i ∈ Finset.univ.erase v, (if 0 < rem ρ' i then b - rem ρ' i else 0) =
      ∑ i ∈ Finset.univ.erase v, (if 0 < rem ρ i then b - rem ρ i else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [rem_update_ne ρ v j val (Finset.ne_of_mem_erase hi)]
  rw [hrest]
  have h1 : ¬ (0 < rem ρ' v) := by omega
  have h2 : 0 < rem ρ v := by omega
  simp only [h1, h2, ↓reduceIte]
  rw [heq1]
  omega

-- Tree metrics on `(N, J)`
private def subtreeLeaves (N J : Finset (List Bool)) (p : List Bool) : ℕ :=
  ((N \ J).filter (fun s => p <+: s)).card

private def subtreeHeight (N : Finset (List Bool)) (p : List Bool) : ℕ :=
  (N.filter (fun s => p <+: s)).sup (fun s => s.length - p.length)

private lemma subtreeLeaves_leaf {N J : Finset (List Bool)} (hs : shape N J)
    {p : List Bool} (hp : p ∈ N \ J) :
    subtreeLeaves N J p = 1 := by
  have heq : (N \ J).filter (fun s => p <+: s) = {p} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hs_leaf, ⟨t, rfl⟩⟩
      cases t with
      | nil => simp
      | cons c tl =>
        exfalso
        have hpN : p ++ [c] ∈ N := by
          have hpref : ∀ u : List Bool, p ++ c :: u ∈ N → p ++ [c] ∈ N := by
            intro u
            induction u using List.reverseRecOn with
            | nil => intro h; exact h
            | append_singleton u' d ih =>
              intro h
              have h1 : (p ++ c :: u') ++ [d] ∈ N := by simpa [List.append_assoc] using h
              exact ih (hs.2.1 (hs.2.2.1 _ d h1))
          exact hpref tl (Finset.mem_sdiff.mp hs_leaf).1
        exact (Finset.mem_sdiff.mp hp).2 (hs.2.2.1 p c hpN)
    · rintro rfl; exact ⟨hp, List.prefix_refl _⟩
  unfold subtreeLeaves; rw [heq, Finset.card_singleton]

private lemma subtreeLeaves_node {N J : Finset (List Bool)} (_hs : shape N J)
    {p : List Bool} (hp : p ∈ J) :
    subtreeLeaves N J p = subtreeLeaves N J (p ++ [false]) + subtreeLeaves N J (p ++ [true]) := by
  unfold subtreeLeaves
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext s
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hsL, ⟨t, rfl⟩⟩
      cases t with
      | nil => exact absurd (by simpa using hp) (Finset.mem_sdiff.mp hsL).2
      | cons c tl =>
        cases c
        · left; exact ⟨hsL, ⟨tl, by simp [List.append_assoc]⟩⟩
        · right; exact ⟨hsL, ⟨tl, by simp [List.append_assoc]⟩⟩
    · rintro (⟨hsL, ⟨t, rfl⟩⟩ | ⟨hsL, ⟨t, rfl⟩⟩)
      · exact ⟨hsL, ⟨false :: t, by simp [List.append_assoc]⟩⟩
      · exact ⟨hsL, ⟨true :: t, by simp [List.append_assoc]⟩⟩
  · rw [Finset.disjoint_left]
    intro s h0 h1
    obtain ⟨_, ⟨t0, rfl⟩⟩ := Finset.mem_filter.mp h0
    obtain ⟨_, ⟨t1, hEq⟩⟩ := Finset.mem_filter.mp h1
    rw [List.append_assoc, List.append_assoc] at hEq
    have := List.append_cancel_left hEq
    simp at this

private lemma subtreeHeight_node {N J : Finset (List Bool)} (hs : shape N J)
    {p : List Bool} (hp : p ∈ J) :
    subtreeHeight N p = 1 + max (subtreeHeight N (p ++ [false])) (subtreeHeight N (p ++ [true])) := by
  have hpf : p ++ [false] ∈ N := (hs.2.2.2 p hp).1
  have hpt : p ++ [true] ∈ N := (hs.2.2.2 p hp).2
  apply le_antisymm
  · apply Finset.sup_le
    intro s hs_mem
    obtain ⟨hsN, ⟨t, rfl⟩⟩ := Finset.mem_filter.mp hs_mem
    cases t with
    | nil => simp
    | cons c tl =>
      cases c
      · have hle : ((p ++ [false]) ++ tl).length - (p ++ [false]).length ≤
            subtreeHeight N (p ++ [false]) :=
          Finset.le_sup (f := fun s : List Bool => s.length - (p ++ [false]).length)
            (Finset.mem_filter.mpr ⟨by simpa [List.append_assoc] using hsN, ⟨tl, rfl⟩⟩)
        simp only [List.length_append, List.length_cons, List.length_nil] at hle ⊢
        omega
      · have hle : ((p ++ [true]) ++ tl).length - (p ++ [true]).length ≤
            subtreeHeight N (p ++ [true]) :=
          Finset.le_sup (f := fun s : List Bool => s.length - (p ++ [true]).length)
            (Finset.mem_filter.mpr ⟨by simpa [List.append_assoc] using hsN, ⟨tl, rfl⟩⟩)
        simp only [List.length_append, List.length_cons, List.length_nil] at hle ⊢
        omega
  · have hleft : 1 + subtreeHeight N (p ++ [false]) ≤ subtreeHeight N p := by
      have hne : (N.filter (fun s => p ++ [false] <+: s)).Nonempty :=
        ⟨p ++ [false], Finset.mem_filter.mpr ⟨hpf, List.prefix_refl _⟩⟩
      obtain ⟨s, hs_mem, hs_eq⟩ :=
        Finset.exists_mem_eq_sup _ hne (fun s : List Bool => s.length - (p ++ [false]).length)
      unfold subtreeHeight
      rw [hs_eq]
      obtain ⟨hsN, ⟨t, rfl⟩⟩ := Finset.mem_filter.mp hs_mem
      have hle : ((p ++ [false]) ++ t).length - p.length ≤
          (N.filter (fun s => p <+: s)).sup (fun s => s.length - p.length) :=
        Finset.le_sup (f := fun s : List Bool => s.length - p.length)
          (Finset.mem_filter.mpr ⟨hsN, ⟨false :: t, by simp [List.append_assoc]⟩⟩)
      simp only [List.length_append, List.length_cons, List.length_nil] at hle ⊢
      omega
    have hright : 1 + subtreeHeight N (p ++ [true]) ≤ subtreeHeight N p := by
      have hne : (N.filter (fun s => p ++ [true] <+: s)).Nonempty :=
        ⟨p ++ [true], Finset.mem_filter.mpr ⟨hpt, List.prefix_refl _⟩⟩
      obtain ⟨s, hs_mem, hs_eq⟩ :=
        Finset.exists_mem_eq_sup _ hne (fun s : List Bool => s.length - (p ++ [true]).length)
      unfold subtreeHeight
      rw [hs_eq]
      obtain ⟨hsN, ⟨t, rfl⟩⟩ := Finset.mem_filter.mp hs_mem
      have hle : ((p ++ [true]) ++ t).length - p.length ≤
          (N.filter (fun s => p <+: s)).sup (fun s => s.length - p.length) :=
        Finset.le_sup (f := fun s : List Bool => s.length - p.length)
          (Finset.mem_filter.mpr ⟨hsN, ⟨true :: t, by simp [List.append_assoc]⟩⟩)
      simp only [List.length_append, List.length_cons, List.length_nil] at hle ⊢
      omega
    omega

private lemma leaf_forces_falsified {F : Set (Clause (Fin n))} {A : Clause (Raw n b)}
    {ρ : Raw n b → Option Bool} (hA : liftAx F A) (hF : Falsifies ρ A) :
    ∃ C ∈ F, ∀ lit ∈ C, rem ρ lit.1 = 0 ∧ par ρ lit.1 ≠ lit.2 := by
  obtain ⟨C, hCF, y, hy, rfl⟩ := hA
  refine ⟨C, hCF, fun lit hlit => ?_⟩
  have hbits : ∀ j : Fin b, ρ ⟨lit.1, j⟩ = some (y ⟨lit.1, j⟩) := by
    intro j
    have hmem : (⟨lit.1, j⟩, !(y ⟨lit.1, j⟩)) ∈
        ((Finset.univ : Finset (Raw n b)).filter (fun u => u.1 ∈ C.image Prod.fst)).image
          (fun u => (u, !(y u))) := by
      apply Finset.mem_image_of_mem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_image_of_mem Prod.fst hlit
    have := hF _ hmem
    simpa using this
  constructor
  · unfold rem
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _; simp [hbits j]
  · have hpar : par ρ lit.1 = parity y lit.1 := by
      unfold par parity; congr 1; congr 1; congr 1; congr 1; ext j; simp [hbits j]
    rw [hpar]
    exact hy lit hlit

-- Critical assignment structure
private structure CritAssgn (n : ℕ) (hn : 0 < n) where
  val : Fin n → Bool
  cl : Clause (Fin n)
  hclF : cl ∈ cycF hn
  hfals : ∀ lit ∈ cl, val lit.1 ≠ lit.2
  huniq : ∀ C ∈ cycF hn, (∀ lit ∈ C, val lit.1 ≠ lit.2) → C = cl

private def Compat (ρ : Raw n b → Option Bool) (x : Fin n → Bool) : Prop :=
  ∀ i : Fin n, rem ρ i = 0 → par ρ i = x i

private lemma falsifies_resolvent_step {C D R : Clause (Raw n b)}
    {ρ : Raw n b → Option Bool} (hres : IsResolvent C D R) (hF : Falsifies ρ R) :
    ∃ v : Raw n b,
      (ρ v = some false → Falsifies ρ C) ∧
      (ρ v = some true → Falsifies ρ D) ∧
      (ρ v = none → Falsifies (Function.update ρ v (some false)) C ∧
                    Falsifies (Function.update ρ v (some true)) D) := by
  obtain ⟨v, hvC, hvD, rfl⟩ := hres
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv0 lit hlit
    by_cases hlv : lit = (v, true)
    · subst hlv; simpa using hv0
    · exact hF lit (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlv, hlit⟩))
  · intro hv1 lit hlit
    by_cases hlv : lit = (v, false)
    · subst hlv; simpa using hv1
    · exact hF lit (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlv, hlit⟩))
  · intro hnone
    constructor
    · intro lit hlit
      by_cases hlv : lit = (v, true)
      · subst hlv; simp
      · have hmem : lit ∈ C.erase (v, true) ∪ D.erase (v, false) :=
          Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlv, hlit⟩)
        have hlit_ne : lit.1 ≠ v := by
          intro heq
          have h1 := hF lit hmem
          rw [heq, hnone] at h1; simp at h1
        rw [Function.update_of_ne hlit_ne]
        exact hF lit hmem
    · intro lit hlit
      by_cases hlv : lit = (v, false)
      · subst hlv; simp
      · have hmem : lit ∈ C.erase (v, true) ∪ D.erase (v, false) :=
          Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlv, hlit⟩)
        have hlit_ne : lit.1 ≠ v := by
          intro heq
          have h1 := hF lit hmem
          rw [heq, hnone] at h1; simp at h1
        rw [Function.update_of_ne hlit_ne]
        exact hF lit hmem

private lemma leaf_impossible_of_two_crit {N J : Finset (List Bool)}
    {line : List Bool → Clause (Raw n b)}
    (hl : ∀ p ∈ N \ J, liftAx (cycF hn) (line p))
    {p : List Bool} (hp : p ∈ N \ J)
    {ρ : Raw n b → Option Bool} (hF : Falsifies ρ (line p))
    {x₁ x₂ : CritAssgn n hn} (h1 : Compat ρ x₁.val) (h2 : Compat ρ x₂.val)
    (hne : x₁.cl ≠ x₂.cl) : False := by
  obtain ⟨C, hCF, hC⟩ := leaf_forces_falsified (hl p hp) hF
  have hC1 : C = x₁.cl := x₁.huniq C hCF (fun lit hlit => by
    have ⟨hr, hp⟩ := hC lit hlit
    rw [← h1 lit.1 hr]; exact hp)
  have hC2 : C = x₂.cl := x₂.huniq C hCF (fun lit hlit => by
    have ⟨hr, hp⟩ := hC lit hlit
    rw [← h2 lit.1 hr]; exact hp)
  exact hne (hC1.symm.trans hC2)

-- Core critical-set lower bounds: BOTH leaf AND height bounds!
private lemma lb_crit (hb : 0 < b) {N J : Finset (List Bool)}
    {line : List Bool → Clause (Raw n b)}
    (hs : shape N J) (hl : ∀ p ∈ N \ J, liftAx (cycF hn) (line p))
    (hr : ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    ∀ (h : ℕ) (p : List Bool), p ∈ N → subtreeHeight N p ≤ h →
      ∀ (ρ : Raw n b → Option Bool), Falsifies ρ (line p) →
        ∀ (S : List (CritAssgn n hn)), S ≠ [] →
          (∀ x ∈ S, Compat ρ x.val) →
          (S.map CritAssgn.cl).Nodup →
          bal (2 ^ (b - 1)) S.length ≤ 2 ^ deficit ρ * subtreeLeaves N J p ∧
          b * Nat.clog 2 S.length ≤ subtreeHeight N p + deficit ρ := by
  intro h
  induction h with
  | zero =>
    intro p hpN hh0 ρ hF S hSne hcomp hnd
    have hp_leaf : p ∈ N \ J := by
      refine Finset.mem_sdiff.mpr ⟨hpN, fun hpJ => ?_⟩
      have := subtreeHeight_node hs hpJ; omega
    have hlen1 : S.length = 1 := by
      cases S with
      | nil => exact absurd rfl hSne
      | cons x₁ rest =>
        cases rest with
        | nil => rfl
        | cons x₂ tl =>
          exfalso
          have hne : x₁.cl ≠ x₂.cl := by
            simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnd
            exact fun h => hnd.1 (Or.inl h)
          exact leaf_impossible_of_two_crit hn hl hp_leaf hF
            (hcomp x₁ (by simp)) (hcomp x₂ (by simp)) hne
    rw [hlen1, bal_one, Nat.clog_one_right, Nat.mul_zero, subtreeLeaves_leaf hs hp_leaf, Nat.mul_one]
    exact ⟨Nat.one_le_pow _ _ (by decide), Nat.zero_le _⟩
  | succ h ih =>
    intro p hpN hhh ρ hF S hSne hcomp hnd
    by_cases hpJ : p ∈ J
    · have hh_eq := subtreeHeight_node hs hpJ
      have hl_eq := subtreeLeaves_node hs hpJ
      have hpf : p ++ [false] ∈ N := (hs.2.2.2 p hpJ).1
      have hpt : p ++ [true] ∈ N := (hs.2.2.2 p hpJ).2
      obtain ⟨⟨v, j⟩, hfalse, htrue, hnone⟩ := falsifies_resolvent_step (hr p hpJ) hF
      cases hρ : ρ ⟨v, j⟩ with
      | some val =>
        cases val
        · have ⟨hK, hH⟩ := ih (p ++ [false]) hpf (by omega) ρ (hfalse hρ) S hSne hcomp hnd
          exact ⟨le_trans hK (Nat.mul_le_mul_left _ (by omega)), by omega⟩
        · have ⟨hK, hH⟩ := ih (p ++ [true]) hpt (by omega) ρ (htrue hρ) S hSne hcomp hnd
          exact ⟨le_trans hK (Nat.mul_le_mul_left _ (by omega)), by omega⟩
      | none =>
        obtain ⟨hF0, hF1⟩ := hnone hρ
        let ρ₀ := Function.update ρ ⟨v, j⟩ (some false)
        let ρ₁ := Function.update ρ ⟨v, j⟩ (some true)
        have hrem_pos : 1 ≤ rem ρ v := by
          unfold rem
          exact Finset.card_pos.mpr ⟨j, by simp [hρ]⟩
        by_cases hrem2 : 2 ≤ rem ρ v
        · -- Still unknown after update: both children keep S, deficit increases by 1!
          have hd0 : deficit ρ₀ = deficit ρ + 1 := deficit_update_ge2 ρ v j false hρ hrem2
          have hd1 : deficit ρ₁ = deficit ρ + 1 := deficit_update_ge2 ρ v j true hρ hrem2
          have hcomp' : ∀ (val : Bool) (x : CritAssgn n hn), x ∈ S →
              Compat (Function.update ρ ⟨v, j⟩ (some val)) x.val := by
            intro val x hx i hri
            have hiv : i ≠ v := by
              intro h; subst h
              have := rem_update_eq ρ i j val hρ; omega
            rw [rem_update_ne ρ v j val hiv] at hri
            rw [par_update_ne ρ v j val hiv]
            exact hcomp x hx i hri
          have ⟨hK0, hH0⟩ := ih (p ++ [false]) hpf (by omega) ρ₀ hF0 S hSne (hcomp' false) hnd
          have ⟨hK1, hH1⟩ := ih (p ++ [true]) hpt (by omega) ρ₁ hF1 S hSne (hcomp' true) hnd
          rw [hd0] at hK0 hH0
          rw [hd1] at hK1 hH1
          constructor
          · have h2 : 2 * bal (2 ^ (b - 1)) S.length ≤
                2 * (2 ^ deficit ρ * subtreeLeaves N J p) := by
              rw [hl_eq, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc]
              have : 2 * 2 ^ deficit ρ = 2 ^ (deficit ρ + 1) := by rw [pow_succ]; ring
              rw [this]; omega
            omega
          · omega
        · -- rem ρ v = 1: block v becomes known with opposite parities in ρ₀ and ρ₁!
          have hrem1 : rem ρ v = 1 := by omega
          have hd0 : deficit ρ = deficit ρ₀ + (b - 1) := deficit_update_eq1 ρ v j false hρ hrem1
          have hd1 : deficit ρ = deficit ρ₁ + (b - 1) := deficit_update_eq1 ρ v j true hρ hrem1
          have hpar_ne : par ρ₀ v ≠ par ρ₁ v := par_update_flip ρ v j
          let S₀ := S.filter (fun x => decide (x.val v = par ρ₀ v))
          let S₁ := S.filter (fun x => decide (x.val v = par ρ₁ v))
          have hlen_sum : S₀.length + S₁.length = S.length := by
            have hpart : ∀ x : CritAssgn n hn,
                decide (x.val v = par ρ₁ v) = !decide (x.val v = par ρ₀ v) := by
              intro x
              cases h0 : par ρ₀ v <;> cases h1 : par ρ₁ v
              · exact absurd (h0.trans h1.symm) hpar_ne
              · cases x.val v <;> rfl
              · cases x.val v <;> rfl
              · exact absurd (h0.trans h1.symm) hpar_ne
            have hS1_eq : S₁ = S.filter (fun x => !decide (x.val v = par ρ₀ v)) :=
              List.filter_congr fun x _ => hpart x
            rw [hS1_eq]
            have hfilt : ∀ (l : List (CritAssgn n hn)) (q : CritAssgn n hn → Bool),
                (l.filter q).length + (l.filter (fun x => !q x)).length = l.length := by
              intro l q
              induction l with
              | nil => rfl
              | cons a tl ihtl =>
                cases hqa : q a <;> simp [List.filter, hqa] <;> omega
            exact hfilt S (fun x => decide (x.val v = par ρ₀ v))
          have hnd₀ : (S₀.map CritAssgn.cl).Nodup := hnd.sublist ((List.filter_sublist).map _)
          have hnd₁ : (S₁.map CritAssgn.cl).Nodup := hnd.sublist ((List.filter_sublist).map _)
          have hcomp₀ : ∀ x ∈ S₀, Compat ρ₀ x.val := by
            intro x hx i hri
            have ⟨hxS, hxv⟩ := List.mem_filter.mp hx
            by_cases hiv : i = v
            · subst hiv; exact (of_decide_eq_true hxv).symm
            · rw [rem_update_ne ρ v j false hiv] at hri
              rw [par_update_ne ρ v j false hiv]
              exact hcomp x hxS i hri
          have hcomp₁ : ∀ x ∈ S₁, Compat ρ₁ x.val := by
            intro x hx i hri
            have ⟨hxS, hxv⟩ := List.mem_filter.mp hx
            by_cases hiv : i = v
            · subst hiv; exact (of_decide_eq_true hxv).symm
            · rw [rem_update_ne ρ v j true hiv] at hri
              rw [par_update_ne ρ v j true hiv]
              exact hcomp x hxS i hri
          have hbase1 : 1 ≤ 2 ^ (b - 1) := Nat.one_le_pow _ _ (by decide)
          have h2d0 : 2 ^ deficit ρ = 2 ^ (b - 1) * 2 ^ deficit ρ₀ := by
            rw [hd0, pow_add, Nat.mul_comm]
          have h2d1 : 2 ^ deficit ρ = 2 ^ (b - 1) * 2 ^ deficit ρ₁ := by
            rw [hd1, pow_add, Nat.mul_comm]
          by_cases hS₀e : S₀ = []
          · have hS₁ne : S₁ ≠ [] := by
              intro h; rw [hS₀e, h] at hlen_sum; cases S with | nil => exact hSne rfl | cons _ _ => simp at hlen_sum
            have hS₁len : S₁.length = S.length := by rw [hS₀e] at hlen_sum; simpa using hlen_sum
            have ⟨hK1, hH1⟩ := ih (p ++ [true]) hpt (by omega) ρ₁ hF1 S₁ hS₁ne hcomp₁ hnd₁
            rw [hS₁len] at hK1 hH1
            constructor
            · calc bal (2 ^ (b - 1)) S.length ≤ 2 ^ (b - 1) * bal (2 ^ (b - 1)) S.length :=
                    Nat.le_mul_of_pos_left _ hbase1
                _ ≤ 2 ^ (b - 1) * (2 ^ deficit ρ₁ * subtreeLeaves N J (p ++ [true])) :=
                    Nat.mul_le_mul_left _ hK1
                _ = 2 ^ deficit ρ * subtreeLeaves N J (p ++ [true]) := by rw [← Nat.mul_assoc, ← h2d1]
                _ ≤ 2 ^ deficit ρ * subtreeLeaves N J p := Nat.mul_le_mul_left _ (by omega)
            · omega
          · by_cases hS₁e : S₁ = []
            · have hS₀len : S₀.length = S.length := by rw [hS₁e] at hlen_sum; simpa using hlen_sum
              have ⟨hK0, hH0⟩ := ih (p ++ [false]) hpf (by omega) ρ₀ hF0 S₀ hS₀e hcomp₀ hnd₀
              rw [hS₀len] at hK0 hH0
              constructor
              · calc bal (2 ^ (b - 1)) S.length ≤ 2 ^ (b - 1) * bal (2 ^ (b - 1)) S.length :=
                      Nat.le_mul_of_pos_left _ hbase1
                  _ ≤ 2 ^ (b - 1) * (2 ^ deficit ρ₀ * subtreeLeaves N J (p ++ [false])) :=
                      Nat.mul_le_mul_left _ hK0
                  _ = 2 ^ deficit ρ * subtreeLeaves N J (p ++ [false]) := by rw [← Nat.mul_assoc, ← h2d0]
                  _ ≤ 2 ^ deficit ρ * subtreeLeaves N J p := Nat.mul_le_mul_left _ (by omega)
              · omega
            · -- Both S₀ and S₁ nonempty!
              have ⟨hK0, hH0⟩ := ih (p ++ [false]) hpf (by omega) ρ₀ hF0 S₀ hS₀e hcomp₀ hnd₀
              have ⟨hK1, hH1⟩ := ih (p ++ [true]) hpt (by omega) ρ₁ hF1 S₁ hS₁e hcomp₁ hnd₁
              have hlen0 : 1 ≤ S₀.length := List.length_pos_of_ne_nil hS₀e
              have hlen1 : 1 ≤ S₁.length := List.length_pos_of_ne_nil hS₁e
              constructor
              · rw [← hlen_sum]
                calc bal (2 ^ (b - 1)) (S₀.length + S₁.length)
                    ≤ 2 ^ (b - 1) * (bal (2 ^ (b - 1)) S₀.length + bal (2 ^ (b - 1)) S₁.length) :=
                      bal_convex hbase1 hlen0 hlen1
                  _ ≤ 2 ^ (b - 1) * (2 ^ deficit ρ₀ * subtreeLeaves N J (p ++ [false]) +
                                     2 ^ deficit ρ₁ * subtreeLeaves N J (p ++ [true])) :=
                      Nat.mul_le_mul_left _ (Nat.add_le_add hK0 hK1)
                  _ = 2 ^ deficit ρ * subtreeLeaves N J p := by
                      rw [hl_eq, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc,
                        ← h2d0, ← h2d1]
              · have hclog := clog_add_le hlen0 hlen1
                rw [hlen_sum] at hclog
                have hmul : b * Nat.clog 2 S.length ≤
                    b + max (b * Nat.clog 2 S₀.length) (b * Nat.clog 2 S₁.length) := by
                  calc b * Nat.clog 2 S.length
                      ≤ b * (1 + max (Nat.clog 2 S₀.length) (Nat.clog 2 S₁.length)) :=
                        Nat.mul_le_mul_left b hclog
                    _ = b + max (b * Nat.clog 2 S₀.length) (b * Nat.clog 2 S₁.length) := by
                        rw [Nat.mul_add, Nat.mul_one, Nat.mul_max_mul_left]
                omega
    · -- Leaf: p ∈ N \ J
      have hp_leaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hpN, hpJ⟩
      have hlen1 : S.length = 1 := by
        cases S with
        | nil => exact absurd rfl hSne
        | cons x₁ rest =>
          cases rest with
          | nil => rfl
          | cons x₂ tl =>
            exfalso
            have hne : x₁.cl ≠ x₂.cl := by
              simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnd
              exact fun h => hnd.1 (Or.inl h)
            exact leaf_impossible_of_two_crit hn hl hp_leaf hF
              (hcomp x₁ (by simp)) (hcomp x₂ (by simp)) hne
      rw [hlen1, bal_one, Nat.clog_one_right, Nat.mul_zero, subtreeLeaves_leaf hs hp_leaf, Nat.mul_one]
      exact ⟨Nat.one_le_pow _ _ (by decide), Nat.zero_le _⟩

end Core

/-! ### Explicit construction of the `n + 3` critical assignments of `cycF` -/

section Crit

variable {n : ℕ} (hn : 0 < n)

private def critC1 (_hn2 : 2 ≤ n) : CritAssgn n hn where
  val := fun _ => false
  cl := {(last hn, true), (first hn, true)}
  hclF := Or.inl rfl
  hfals := by intro lit hlit; simp at hlit; rcases hlit with rfl | rfl <;> simp
  huniq := by
    intro C hCF hfal
    rcases hCF with rfl | rfl | rfl | ⟨i, hi, rfl⟩
    · rfl
    · exfalso; exact hfal (last hn, false) (by simp) rfl
    · exfalso; exact hfal (last hn, false) (by simp) rfl
    · exfalso; exact hfal (atV hn i, false) (by simp) rfl

private def critC3 (_hn2 : 2 ≤ n) : CritAssgn n hn where
  val := fun _ => true
  cl := {(last hn, false), (first hn, false)}
  hclF := Or.inr (Or.inr (Or.inl rfl))
  hfals := by intro lit hlit; simp at hlit; rcases hlit with rfl | rfl <;> simp
  huniq := by
    intro C hCF hfal
    rcases hCF with rfl | rfl | rfl | ⟨i, hi, rfl⟩
    · exfalso; exact hfal (last hn, true) (by simp) rfl
    · exfalso; exact hfal (first hn, true) (by simp) rfl
    · rfl
    · exfalso; exact hfal (atV hn (i + 1), true) (by simp) rfl

private def critC2L (hn2 : 2 ≤ n) : CritAssgn n hn where
  val := fun i => decide (i = last hn)
  cl := {(last hn, false), (first hn, true)}
  hclF := Or.inr (Or.inl rfl)
  hfals := by
    intro lit hlit; simp at hlit
    rcases hlit with rfl | rfl
    · simp
    · simp [first_ne_last hn hn2]
  huniq := by
    intro C hCF hfal
    rcases hCF with rfl | rfl | rfl | ⟨i, hi, rfl⟩
    · exfalso; exact hfal (last hn, true) (by simp) (by simp)
    · rfl
    · exfalso; exact hfal (first hn, false) (by simp) (by simp [first_ne_last hn hn2])
    · exfalso
      have hne : atV hn i ≠ last hn := fun h => by
        have := atV_inj hn (by omega) (by omega) h; omega
      exact hfal (atV hn i, false) (by simp) (by simp [hne])

private def critC2R (hn2 : 2 ≤ n) : CritAssgn n hn where
  val := fun i => decide (i ≠ first hn)
  cl := {(last hn, false), (first hn, true)}
  hclF := Or.inr (Or.inl rfl)
  hfals := by
    intro lit hlit; simp at hlit
    rcases hlit with rfl | rfl
    · simp [(first_ne_last hn hn2).symm]
    · simp
  huniq := by
    intro C hCF hfal
    rcases hCF with rfl | rfl | rfl | ⟨i, hi, rfl⟩
    · exfalso; exact hfal (last hn, true) (by simp) (by simp [(first_ne_last hn hn2).symm])
    · rfl
    · exfalso; exact hfal (first hn, false) (by simp) (by simp)
    · exfalso
      have hne : atV hn (i + 1) ≠ first hn := fun h => by
        have := atV_inj hn hi (by omega) h; omega
      exact hfal (atV hn (i + 1), true) (by simp) (by simp [hne])

private def critImp (hn2 : 2 ≤ n) (k : ℕ) (hk : k + 1 < n) : CritAssgn n hn where
  val := fun i => decide (i.val ≤ k)
  cl := {(atV hn k, false), (atV hn (k + 1), true)}
  hclF := Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩))
  hfals := by
    intro lit hlit; simp at hlit
    rcases hlit with rfl | rfl
    · simp [atV_val hn (by omega : k < n)]
    · simp [atV_val hn hk]
  huniq := by
    intro C hCF hfal
    rcases hCF with rfl | rfl | rfl | ⟨i, hi, rfl⟩
    · exfalso
      have h0 : (first hn).val = 0 := atV_val hn hn
      exact hfal (first hn, true) (by simp) (by simp [h0])
    · exfalso
      have h0 : (first hn).val = 0 := atV_val hn hn
      exact hfal (first hn, true) (by simp) (by simp [h0])
    · exfalso
      have hlast : (last hn).val = n - 1 := atV_val hn (by omega)
      have hlt : ¬ (n - 1 ≤ k) := by omega
      exact hfal (last hn, false) (by simp) (by simp [hlast, hlt])
    · by_cases hik : i = k
      · subst hik; rfl
      · exfalso
        by_cases hlt : i < k
        · have hle : (atV hn (i + 1)).val ≤ k := by rw [atV_val hn hi]; omega
          exact hfal (atV hn (i + 1), true) (by simp) (by simp [hle])
        · have hgt : ¬ ((atV hn i).val ≤ k) := by rw [atV_val hn (by omega)]; omega
          exact hfal (atV hn i, false) (by simp) (by simp [hgt])

-- Distinctness of clauses in `cycF`
private lemma imp_cl_ne_C1 (_hn2 : 2 ≤ n) {k : ℕ} (_hk : k + 1 < n) :
    ({(atV hn k, false), (atV hn (k + 1), true)} : Clause (Fin n)) ≠
    {(last hn, true), (first hn, true)} := by
  intro h
  have hmem : (atV hn k, false) ∈ ({(last hn, true), (first hn, true)} : Clause (Fin n)) := by
    rw [← h]; simp
  simp at hmem

private lemma imp_cl_ne_C3 (_hn2 : 2 ≤ n) {k : ℕ} (_hk : k + 1 < n) :
    ({(atV hn k, false), (atV hn (k + 1), true)} : Clause (Fin n)) ≠
    {(last hn, false), (first hn, false)} := by
  intro h
  have hmem : (atV hn (k + 1), true) ∈ ({(last hn, false), (first hn, false)} : Clause (Fin n)) := by
    rw [← h]; simp
  simp at hmem

private lemma imp_cl_ne_C2 (hn2 : 2 ≤ n) {k : ℕ} (hk : k + 1 < n) :
    ({(atV hn k, false), (atV hn (k + 1), true)} : Clause (Fin n)) ≠
    {(last hn, false), (first hn, true)} := by
  intro h
  have hmem : (atV hn k, false) ∈ ({(last hn, false), (first hn, true)} : Clause (Fin n)) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨heq, _⟩ | ⟨_, hbf⟩
  · have := atV_inj hn (by omega) (by omega) heq; omega
  · simp at hbf

private lemma imp_cl_inj (_hn2 : 2 ≤ n) {k₁ k₂ : ℕ} (hk₁ : k₁ + 1 < n) (hk₂ : k₂ + 1 < n)
    (h : ({(atV hn k₁, false), (atV hn (k₁ + 1), true)} : Clause (Fin n)) =
         {(atV hn k₂, false), (atV hn (k₂ + 1), true)}) : k₁ = k₂ := by
  have hmem : (atV hn k₁, false) ∈ ({(atV hn k₂, false), (atV hn (k₂ + 1), true)} : Clause (Fin n)) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨heq, _⟩ | ⟨_, hbf⟩
  · exact atV_inj hn (by omega) (by omega) heq
  · simp at hbf

private lemma C1_ne_C2 (hn2 : 2 ≤ n) :
    ({(last hn, true), (first hn, true)} : Clause (Fin n)) ≠ {(last hn, false), (first hn, true)} := by
  intro h
  have hmem : (last hn, true) ∈ ({(last hn, false), (first hn, true)} : Clause (Fin n)) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, htf⟩ | ⟨heq, _⟩
  · simp at htf
  · exact (first_ne_last hn hn2).symm heq

private lemma C3_ne_C2 (hn2 : 2 ≤ n) :
    ({(last hn, false), (first hn, false)} : Clause (Fin n)) ≠ {(last hn, false), (first hn, true)} := by
  intro h
  have hmem : (first hn, false) ∈ ({(last hn, false), (first hn, true)} : Clause (Fin n)) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
  rcases hmem with ⟨heq, _⟩ | ⟨_, hft⟩
  · exact first_ne_last hn hn2 heq
  · simp at hft

-- Build list of `critImp` for `k` in `[a, c)` (for `c ≤ n - 1`)
private def critImpList (hn2 : 2 ≤ n) (a : ℕ) : ∀ (len : ℕ), a + len ≤ n - 1 → List (CritAssgn n hn)
  | 0, _ => []
  | len + 1, h => critImp hn hn2 a (by omega) :: critImpList hn2 (a + 1) len (by omega)

private lemma critImpList_length (hn2 : 2 ≤ n) (a len : ℕ) (h : a + len ≤ n - 1) :
    (critImpList hn hn2 a len h).length = len := by
  induction len generalizing a with
  | zero => rfl
  | succ len ih => simp [critImpList, ih]

private lemma critImpList_mem (hn2 : 2 ≤ n) (a len : ℕ) (h : a + len ≤ n - 1)
    {x : CritAssgn n hn} (hx : x ∈ critImpList hn hn2 a len h) :
    ∃ k : ℕ, a ≤ k ∧ k < a + len ∧ ∃ hk : k + 1 < n, x = critImp hn hn2 k hk := by
  induction len generalizing a with
  | zero => simp [critImpList] at hx
  | succ len ih =>
    simp only [critImpList, List.mem_cons] at hx
    rcases hx with rfl | htl
    · exact ⟨a, le_refl _, by omega, by omega, rfl⟩
    · obtain ⟨k, hk1, hk2, hk3, rfl⟩ := ih (a + 1) (by omega) htl
      exact ⟨k, by omega, by omega, hk3, rfl⟩

private lemma critImpList_nodup (hn2 : 2 ≤ n) (a len : ℕ) (h : a + len ≤ n - 1) :
    ((critImpList hn hn2 a len h).map CritAssgn.cl).Nodup := by
  induction len generalizing a with
  | zero => simp [critImpList]
  | succ len ih =>
    simp only [critImpList, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (a + 1) (by omega)⟩
    intro hmem
    obtain ⟨x, hx, hcl⟩ := List.mem_map.mp hmem
    obtain ⟨k, hk1, _, hk3, rfl⟩ := critImpList_mem hn hn2 (a + 1) len (by omega) hx
    have := imp_cl_inj hn hn2 hk3 (by omega) hcl
    omega

end Crit

section Core2

variable {n : ℕ} (hn : 0 < n) {b : ℕ} (hb : 0 < b)

-- One-step block-completion split when `rem ρ v = 1` and all other blocks have `rem ρ i ≥ 1`
private lemma first_block_split (hn2 : 2 ≤ n) (hb : 0 < b) {N J : Finset (List Bool)}
    {line : List Bool → Clause (Raw n b)}
    (hs : shape N J) (hl : ∀ p ∈ N \ J, liftAx (cycF hn) (line p))
    (hr : ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p))
    {p : List Bool} (hpJ : p ∈ J)
    {ρ : Raw n b → Option Bool} (hall : ∀ i : Fin n, 0 < rem ρ i)
    {v : Fin n} {j : Fin b} (hnone : ρ ⟨v, j⟩ = none) (hrem1 : rem ρ v = 1)
    (hF0 : Falsifies (Function.update ρ ⟨v, j⟩ (some false)) (line (p ++ [false])))
    (hF1 : Falsifies (Function.update ρ ⟨v, j⟩ (some true)) (line (p ++ [true]))) :
    let base := 2 ^ (b - 1)
    (b * (1 + Nat.clog 2 n) ≤ subtreeHeight N p + deficit ρ ∧
     base * (2 * base + bal base n) ≤ 2 ^ deficit ρ * subtreeLeaves N J p) ∨
    (b * Nat.clog 2 (n + 3) ≤ subtreeHeight N p + deficit ρ ∧
     bal base (n + 3) ≤ 2 ^ deficit ρ * subtreeLeaves N J p) := by
  intro base
  let ρ₀ := Function.update ρ ⟨v, j⟩ (some false)
  let ρ₁ := Function.update ρ ⟨v, j⟩ (some true)
  have hpf : p ++ [false] ∈ N := (hs.2.2.2 p hpJ).1
  have hpt : p ++ [true] ∈ N := (hs.2.2.2 p hpJ).2
  have hh_eq := subtreeHeight_node hs hpJ
  have hl_eq := subtreeLeaves_node hs hpJ
  have hd0 : deficit ρ = deficit ρ₀ + (b - 1) := deficit_update_eq1 ρ v j false hnone hrem1
  have hd1 : deficit ρ = deficit ρ₁ + (b - 1) := deficit_update_eq1 ρ v j true hnone hrem1
  have h2d0 : 2 ^ deficit ρ = base * 2 ^ deficit ρ₀ := by rw [hd0, pow_add, Nat.mul_comm]
  have h2d1 : 2 ^ deficit ρ = base * 2 ^ deficit ρ₁ := by rw [hd1, pow_add, Nat.mul_comm]
  have hpar_ne : par ρ₀ v ≠ par ρ₁ v := par_update_flip ρ v j
  -- Helper: Compat ρ' x iff x v = par ρ' v (since v is the ONLY block with rem ρ' = 0!)
  have hcompat_iff : ∀ (val : Bool) (x : Fin n → Bool),
      Compat (Function.update ρ ⟨v, j⟩ (some val)) x ↔
        x v = par (Function.update ρ ⟨v, j⟩ (some val)) v := by
    intro val x
    constructor
    · intro hc
      have hr0 : rem (Function.update ρ ⟨v, j⟩ (some val)) v = 0 := by
        have := rem_update_eq ρ v j val hnone; omega
      exact (hc v hr0).symm
    · intro hv i hri
      by_cases hiv : i = v
      · subst hiv; exact hv.symm
      · rw [rem_update_ne ρ v j val hiv] at hri
        have := hall i; omega
  -- Helper: given S_F (all val v = false) and S_T (all val v = true), get combined (H, K) bounds!
  have hcombine : ∀ (S_F S_T : List (CritAssgn n hn)),
      S_F ≠ [] → S_T ≠ [] →
      (∀ x ∈ S_F, x.val v = false) → (∀ x ∈ S_T, x.val v = true) →
      (S_F.map CritAssgn.cl).Nodup → (S_T.map CritAssgn.cl).Nodup →
      base * (bal base S_F.length + bal base S_T.length) ≤ 2 ^ deficit ρ * subtreeLeaves N J p ∧
      b + max (b * Nat.clog 2 S_F.length) (b * Nat.clog 2 S_T.length) ≤
        subtreeHeight N p + deficit ρ := by
    intro S_F S_T hFe hTe hFv hTv hFnd hTnd
    by_cases hp0 : par ρ₀ v = false
    · have hp1 : par ρ₁ v = true := by
        cases h : par ρ₁ v
        · exact absurd (hp0.trans h.symm) hpar_ne
        · rfl
      have ⟨hK0, hH0⟩ := lb_crit hn hb hs hl hr (subtreeHeight N (p ++ [false])) (p ++ [false]) hpf
        (le_refl _) ρ₀ hF0 S_F hFe (fun x hx => (hcompat_iff false x.val).mpr ((hFv x hx).trans hp0.symm)) hFnd
      have ⟨hK1, hH1⟩ := lb_crit hn hb hs hl hr (subtreeHeight N (p ++ [true])) (p ++ [true]) hpt
        (le_refl _) ρ₁ hF1 S_T hTe (fun x hx => (hcompat_iff true x.val).mpr ((hTv x hx).trans hp1.symm)) hTnd
      constructor
      · calc base * (bal base S_F.length + bal base S_T.length)
            ≤ base * (2 ^ deficit ρ₀ * subtreeLeaves N J (p ++ [false]) +
                      2 ^ deficit ρ₁ * subtreeLeaves N J (p ++ [true])) :=
              Nat.mul_le_mul_left _ (Nat.add_le_add hK0 hK1)
          _ = 2 ^ deficit ρ * subtreeLeaves N J p := by
              rw [hl_eq, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, ← h2d0, ← h2d1]
      · omega
    · have hp0' : par ρ₀ v = true := by
        cases h : par ρ₀ v
        · exact absurd h hp0
        · rfl
      have hp1 : par ρ₁ v = false := by
        cases h : par ρ₁ v
        · rfl
        · exact absurd (hp0'.trans h.symm) hpar_ne
      have ⟨hK0, hH0⟩ := lb_crit hn hb hs hl hr (subtreeHeight N (p ++ [false])) (p ++ [false]) hpf
        (le_refl _) ρ₀ hF0 S_T hTe (fun x hx => (hcompat_iff false x.val).mpr ((hTv x hx).trans hp0'.symm)) hTnd
      have ⟨hK1, hH1⟩ := lb_crit hn hb hs hl hr (subtreeHeight N (p ++ [true])) (p ++ [true]) hpt
        (le_refl _) ρ₁ hF1 S_F hFe (fun x hx => (hcompat_iff true x.val).mpr ((hFv x hx).trans hp1.symm)) hFnd
      constructor
      · calc base * (bal base S_F.length + bal base S_T.length)
            = base * (bal base S_T.length + bal base S_F.length) := by rw [Nat.add_comm]
          _ ≤ base * (2 ^ deficit ρ₀ * subtreeLeaves N J (p ++ [false]) +
                      2 ^ deficit ρ₁ * subtreeLeaves N J (p ++ [true])) :=
              Nat.mul_le_mul_left _ (Nat.add_le_add hK0 hK1)
          _ = 2 ^ deficit ρ * subtreeLeaves N J p := by
              rw [hl_eq, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, ← h2d0, ← h2d1]
      · omega
  by_cases hv0 : v = first hn
  · -- Branch 1: v = first
    subst hv0
    left
    let S_F : List (CritAssgn n hn) := [critC1 hn hn2, critC2L hn hn2]
    let S_T : List (CritAssgn n hn) := critC3 hn hn2 :: critImpList hn hn2 0 (n - 1) (by omega)
    have hFnd : (S_F.map CritAssgn.cl).Nodup := by
      simp [S_F, critC1, critC2L, C1_ne_C2 hn hn2]
    have hTnd : (S_T.map CritAssgn.cl).Nodup := by
      simp only [S_T, List.map_cons, List.nodup_cons]
      refine ⟨?_, critImpList_nodup hn hn2 0 (n - 1) (by omega)⟩
      intro hmem
      obtain ⟨x, hx, hcl⟩ := List.mem_map.mp hmem
      obtain ⟨k, _, _, hk, rfl⟩ := critImpList_mem hn hn2 0 (n - 1) (by omega) hx
      exact imp_cl_ne_C3 hn hn2 hk hcl
    have hFv : ∀ x ∈ S_F, x.val (first hn) = false := by
      intro x hx; simp only [S_F, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rfl
      · simp [critC2L, first_ne_last hn hn2]
    have hTv : ∀ x ∈ S_T, x.val (first hn) = true := by
      intro x hx; simp only [S_T, List.mem_cons] at hx
      rcases hx with rfl | htl
      · rfl
      · obtain ⟨k, _, _, hk, rfl⟩ := critImpList_mem hn hn2 0 (n - 1) (by omega) htl
        simp [critImp, first, atV_val hn hn]
    have hFl : S_F.length = 2 := rfl
    have hTl : S_T.length = n := by
      simp [S_T, critImpList_length]; omega
    have ⟨hK, hH⟩ := hcombine S_F S_T (by simp [S_F]) (by simp [S_T]) hFv hTv hFnd hTnd
    rw [hFl, hTl, bal_two] at hK
    rw [hFl, hTl] at hH
    have hH' : b * (1 + Nat.clog 2 n) ≤ subtreeHeight N p + deficit ρ := by
      have : b * (1 + Nat.clog 2 n) = b + b * Nat.clog 2 n := by ring
      omega
    exact ⟨hH', hK⟩
  · by_cases hvlast : v = last hn
    · -- Branch 1: v = last
      subst hvlast
      left
      let S_F : List (CritAssgn n hn) := critC1 hn hn2 :: critImpList hn hn2 0 (n - 1) (by omega)
      let S_T : List (CritAssgn n hn) := [critC3 hn hn2, critC2R hn hn2]
      have hFnd : (S_F.map CritAssgn.cl).Nodup := by
        simp only [S_F, List.map_cons, List.nodup_cons]
        refine ⟨?_, critImpList_nodup hn hn2 0 (n - 1) (by omega)⟩
        intro hmem
        obtain ⟨x, hx, hcl⟩ := List.mem_map.mp hmem
        obtain ⟨k, _, _, hk, rfl⟩ := critImpList_mem hn hn2 0 (n - 1) (by omega) hx
        exact imp_cl_ne_C1 hn hn2 hk hcl
      have hTnd : (S_T.map CritAssgn.cl).Nodup := by
        simp [S_T, critC3, critC2R, C3_ne_C2 hn hn2]
      have hFv : ∀ x ∈ S_F, x.val (last hn) = false := by
        intro x hx; simp only [S_F, List.mem_cons] at hx
        rcases hx with rfl | htl
        · rfl
        · obtain ⟨k, _, hk2, hk, rfl⟩ := critImpList_mem hn hn2 0 (n - 1) (by omega) htl
          simp only [critImp, last, atV_val hn (by omega : n - 1 < n), decide_eq_false_iff_not]
          omega
      have hTv : ∀ x ∈ S_T, x.val (last hn) = true := by
        intro x hx; simp only [S_T, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · rfl
        · simp [critC2R, (first_ne_last hn hn2).symm]
      have hFl : S_F.length = n := by simp [S_F, critImpList_length]; omega
      have hTl : S_T.length = 2 := rfl
      have ⟨hK, hH⟩ := hcombine S_F S_T (by simp [S_F]) (by simp [S_T]) hFv hTv hFnd hTnd
      rw [hFl, hTl, bal_two, Nat.add_comm (bal base n)] at hK
      rw [hFl, hTl] at hH
      have hH' : b * (1 + Nat.clog 2 n) ≤ subtreeHeight N p + deficit ρ := by
        have : b * (1 + Nat.clog 2 n) = b + b * Nat.clog 2 n := by ring
        omega
      exact ⟨hH', hK⟩
    · -- Branch 2: interior v (1 ≤ v.val ≤ n - 2)
      right
      have hv_lo : 1 ≤ v.val := by
        by_contra hlt
        apply hv0; apply Fin.ext; rw [first, atV_val hn hn]; omega
      have hv_hi : v.val ≤ n - 2 := by
        by_contra hgt
        apply hvlast; apply Fin.ext; rw [last, atV_val hn (by omega)]; have := v.isLt; omega
      let S_F : List (CritAssgn n hn) :=
        critC1 hn hn2 :: critC2L hn hn2 :: critImpList hn hn2 0 v.val (by omega)
      let S_T : List (CritAssgn n hn) :=
        critC3 hn hn2 :: critC2R hn hn2 :: critImpList hn hn2 v.val (n - 1 - v.val) (by omega)
      have hFnd : (S_F.map CritAssgn.cl).Nodup := by
        simp only [S_F, List.map_cons, List.nodup_cons, List.mem_cons]
        refine ⟨?_, ?_, critImpList_nodup hn hn2 0 v.val (by omega)⟩
        · rintro (h | hmem)
          · exact C1_ne_C2 hn hn2 h
          · obtain ⟨x, hx, hcl⟩ := List.mem_map.mp hmem
            obtain ⟨k, _, _, hk, rfl⟩ := critImpList_mem hn hn2 0 v.val (by omega) hx
            exact imp_cl_ne_C1 hn hn2 hk hcl
        · intro hmem
          obtain ⟨x, hx, hcl⟩ := List.mem_map.mp hmem
          obtain ⟨k, _, _, hk, rfl⟩ := critImpList_mem hn hn2 0 v.val (by omega) hx
          exact imp_cl_ne_C2 hn hn2 hk hcl
      have hTnd : (S_T.map CritAssgn.cl).Nodup := by
        simp only [S_T, List.map_cons, List.nodup_cons, List.mem_cons]
        refine ⟨?_, ?_, critImpList_nodup hn hn2 v.val (n - 1 - v.val) (by omega)⟩
        · rintro (h | hmem)
          · exact C3_ne_C2 hn hn2 h
          · obtain ⟨x, hx, hcl⟩ := List.mem_map.mp hmem
            obtain ⟨k, _, _, hk, rfl⟩ := critImpList_mem hn hn2 v.val (n - 1 - v.val) (by omega) hx
            exact imp_cl_ne_C3 hn hn2 hk hcl
        · intro hmem
          obtain ⟨x, hx, hcl⟩ := List.mem_map.mp hmem
          obtain ⟨k, _, _, hk, rfl⟩ := critImpList_mem hn hn2 v.val (n - 1 - v.val) (by omega) hx
          exact imp_cl_ne_C2 hn hn2 hk hcl
      have hFv : ∀ x ∈ S_F, x.val v = false := by
        intro x hx; simp only [S_F, List.mem_cons] at hx
        rcases hx with rfl | rfl | htl
        · rfl
        · simp [critC2L, hvlast]
        · obtain ⟨k, _, hk2, hk, rfl⟩ := critImpList_mem hn hn2 0 v.val (by omega) htl
          simp only [critImp, decide_eq_false_iff_not]; omega
      have hTv : ∀ x ∈ S_T, x.val v = true := by
        intro x hx; simp only [S_T, List.mem_cons] at hx
        rcases hx with rfl | rfl | htl
        · rfl
        · simp [critC2R, hv0]
        · obtain ⟨k, hk1, _, hk, rfl⟩ := critImpList_mem hn hn2 v.val (n - 1 - v.val) (by omega) htl
          simp only [critImp, decide_eq_true_iff]; omega
      have hFl : S_F.length = v.val + 2 := by simp [S_F, critImpList_length]
      have hTl : S_T.length = n - v.val + 1 := by simp [S_T, critImpList_length]; omega
      have hsum : S_F.length + S_T.length = n + 3 := by omega
      have ⟨hK, hH⟩ := hcombine S_F S_T (by simp [S_F]) (by simp [S_T]) hFv hTv hFnd hTnd
      have hK' : bal base (n + 3) ≤ 2 ^ deficit ρ * subtreeLeaves N J p := by
        rw [← hsum]
        exact le_trans (bal_convex (Nat.one_le_pow _ _ (by decide)) (by omega) (by omega)) hK
      have hH' : b * Nat.clog 2 (n + 3) ≤ subtreeHeight N p + deficit ρ := by
        have hclog := clog_add_le (a := S_F.length) (c := S_T.length) (by omega) (by omega)
        rw [hsum] at hclog
        have hmul : b * Nat.clog 2 (n + 3) ≤
            b + max (b * Nat.clog 2 S_F.length) (b * Nat.clog 2 S_T.length) := by
          calc b * Nat.clog 2 (n + 3)
              ≤ b * (1 + max (Nat.clog 2 S_F.length) (Nat.clog 2 S_T.length)) :=
                Nat.mul_le_mul_left b hclog
            _ = b + max (b * Nat.clog 2 S_F.length) (b * Nat.clog 2 S_T.length) := by
                rw [Nat.mul_add, Nat.mul_one, Nat.mul_max_mul_left]
        omega
      exact ⟨hH', hK'⟩

-- Root-phase induction (when `∀ i, 0 < rem ρ i`): proves the min bounds!
private lemma lb_init_min (hn2 : 2 ≤ n) (hb : 0 < b) {N J : Finset (List Bool)}
    {line : List Bool → Clause (Raw n b)}
    (hs : shape N J) (hl : ∀ p ∈ N \ J, liftAx (cycF hn) (line p))
    (hr : ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    let base := 2 ^ (b - 1)
    ∀ (h : ℕ) (p : List Bool), p ∈ N → subtreeHeight N p ≤ h →
      ∀ (ρ : Raw n b → Option Bool), Falsifies ρ (line p) →
        (∀ i : Fin n, 0 < rem ρ i) →
        min (base * (2 * base + bal base n)) (bal base (n + 3)) ≤
          2 ^ deficit ρ * subtreeLeaves N J p ∧
        min (b * (1 + Nat.clog 2 n)) (b * Nat.clog 2 (n + 3)) ≤
          subtreeHeight N p + deficit ρ := by
  intro base h
  induction h with
  | zero =>
    intro p hpN hh0 ρ hF hall
    exfalso
    have hp_leaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hpN, fun hpJ => by
      have := subtreeHeight_node hs hpJ; omega⟩
    obtain ⟨C, hCF, hC⟩ := leaf_forces_falsified (hl p hp_leaf) hF
    have hCne : C.Nonempty := by
      rcases hCF with rfl | rfl | rfl | ⟨i, _, rfl⟩ <;> exact Finset.insert_nonempty _ _
    obtain ⟨lit, hlit⟩ := hCne
    have := (hC lit hlit).1
    have := hall lit.1
    omega
  | succ h ih =>
    intro p hpN hhh ρ hF hall
    have hpJ : p ∈ J := by
      by_contra hnotJ
      have hp_leaf : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨hpN, hnotJ⟩
      obtain ⟨C, hCF, hC⟩ := leaf_forces_falsified (hl p hp_leaf) hF
      have hCne : C.Nonempty := by
        rcases hCF with rfl | rfl | rfl | ⟨i, _, rfl⟩ <;> exact Finset.insert_nonempty _ _
      obtain ⟨lit, hlit⟩ := hCne
      have := (hC lit hlit).1; have := hall lit.1; omega
    have hh_eq := subtreeHeight_node hs hpJ
    have hl_eq := subtreeLeaves_node hs hpJ
    have hpf : p ++ [false] ∈ N := (hs.2.2.2 p hpJ).1
    have hpt : p ++ [true] ∈ N := (hs.2.2.2 p hpJ).2
    obtain ⟨⟨v, j⟩, hfalse, htrue, hnone⟩ := falsifies_resolvent_step (hr p hpJ) hF
    cases hρ : ρ ⟨v, j⟩ with
    | some val =>
      cases val
      · have ⟨hK, hH⟩ := ih (p ++ [false]) hpf (by omega) ρ (hfalse hρ) hall
        exact ⟨le_trans hK (Nat.mul_le_mul_left _ (by omega)), by omega⟩
      · have ⟨hK, hH⟩ := ih (p ++ [true]) hpt (by omega) ρ (htrue hρ) hall
        exact ⟨le_trans hK (Nat.mul_le_mul_left _ (by omega)), by omega⟩
    | none =>
      obtain ⟨hF0, hF1⟩ := hnone hρ
      have hrem_pos : 1 ≤ rem ρ v := by
        unfold rem; exact Finset.card_pos.mpr ⟨j, by simp [hρ]⟩
      by_cases hrem2 : 2 ≤ rem ρ v
      · let ρ₀ := Function.update ρ ⟨v, j⟩ (some false)
        let ρ₁ := Function.update ρ ⟨v, j⟩ (some true)
        have hd0 : deficit ρ₀ = deficit ρ + 1 := deficit_update_ge2 ρ v j false hρ hrem2
        have hd1 : deficit ρ₁ = deficit ρ + 1 := deficit_update_ge2 ρ v j true hρ hrem2
        have hall' : ∀ (val : Bool) (i : Fin n), 0 < rem (Function.update ρ ⟨v, j⟩ (some val)) i := by
          intro val i
          by_cases hiv : i = v
          · subst hiv; have := rem_update_eq ρ i j val hρ; omega
          · rw [rem_update_ne ρ v j val hiv]; exact hall i
        have ⟨hK0, hH0⟩ := ih (p ++ [false]) hpf (by omega) ρ₀ hF0 (hall' false)
        have ⟨hK1, hH1⟩ := ih (p ++ [true]) hpt (by omega) ρ₁ hF1 (hall' true)
        rw [hd0] at hK0 hH0
        rw [hd1] at hK1 hH1
        constructor
        · have h2 : 2 * min (base * (2 * base + bal base n)) (bal base (n + 3)) ≤
              2 * (2 ^ deficit ρ * subtreeLeaves N J p) := by
            have hpow : 2 * 2 ^ deficit ρ = 2 ^ (deficit ρ + 1) := by rw [pow_succ]; ring
            calc 2 * min (base * (2 * base + bal base n)) (bal base (n + 3))
                = min (base * (2 * base + bal base n)) (bal base (n + 3)) +
                  min (base * (2 * base + bal base n)) (bal base (n + 3)) := by ring
              _ ≤ 2 ^ (deficit ρ + 1) * subtreeLeaves N J (p ++ [false]) +
                  2 ^ (deficit ρ + 1) * subtreeLeaves N J (p ++ [true]) := Nat.add_le_add hK0 hK1
              _ = 2 * (2 ^ deficit ρ * subtreeLeaves N J p) := by rw [hl_eq, ← hpow]; ring
          omega
        · omega
      · have hrem1 : rem ρ v = 1 := by omega
        rcases first_block_split hn hn2 hb hs hl hr hpJ hall hρ hrem1 hF0 hF1 with
          ⟨hH1, hK1⟩ | ⟨hH2, hK2⟩
        · exact ⟨le_trans (min_le_left _ _) hK1, le_trans (min_le_left _ _) hH1⟩
        · exact ⟨le_trans (min_le_right _ _) hK2, le_trans (min_le_right _ _) hH2⟩

end Core2

/-! ## Section 5: Main Theorem -/

private lemma main_proof (n : ℕ) (hn : 0 < n) (b : ℕ) (hb : 0 < b) :
    let w := fun _ : Fin n => b
    let Raw_l := (i : Fin n) × Fin (w i)
    let parity_l := fun (y : Raw_l → Bool) (i : Fin n) =>
      decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i, j⟩ = true)).card)
    let liftAx_l := fun (F : Set (Clause (Fin n))) (A : Clause Raw_l) =>
      ∃ C ∈ F, ∃ y : Raw_l → Bool, (∀ lit ∈ C, parity_l y lit.1 ≠ lit.2) ∧
        A = ((Finset.univ : Finset Raw_l).filter (fun b => b.1 ∈ C.image Prod.fst)).image
          (fun b => (b, !(y b)))
    let shape_l := fun (N J : Finset (List Bool)) =>
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
    let refutes_l := fun (F : Set (Clause (Fin n))) (H K : ℕ) =>
      ∃ (N J : Finset (List Bool)) (line : List Bool → Clause Raw_l),
        shape_l N J ∧ line [] = ∅ ∧ (∀ p ∈ N, p.length ≤ H) ∧ (N \ J).card ≤ K ∧
        (∀ p ∈ N \ J, liftAx_l F (line p)) ∧
        ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)
    let base := 2 ^ (b - 1)
    let balanced := fun m : ℕ =>
      let d := Nat.clog 2 m
      (2 ^ d - m) * base ^ (d - 1) + (2 * m - 2 ^ d) * base ^ d
    let atV_l := fun i : ℕ => (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n)
    let first_l := atV_l 0
    let last_l := atV_l (n - 1)
    let F : Set (Clause (Fin n)) := {C |
      C = {(last_l, true), (first_l, true)} ∨ C = {(last_l, false), (first_l, true)} ∨
        C = {(last_l, false), (first_l, false)} ∨
      ∃ i : ℕ, i + 1 < n ∧ C = {(atV_l i, false), (atV_l (i + 1), true)}}
    ∀ H K : ℕ, 2 ≤ n →
      Iff (refutes_l F H K)
        ((b * (1 + Nat.clog 2 n) ≤ H ∧ base * (2 * base + balanced n) ≤ K) ∨
         (b * Nat.clog 2 (n + 3) ≤ H ∧ balanced (n + 3) ≤ K)) := by
  intro w Raw_l parity_l liftAx_l shape_l refutes_l base balanced atV_l first_l last_l F H K hn2
  change Iff (refutes (b := b) (cycF hn) H K)
    ((b * (1 + Nat.clog 2 n) ≤ H ∧ base * (2 * base + bal base n) ≤ K) ∨
     (b * Nat.clog 2 (n + 3) ≤ H ∧ bal base (n + 3) ≤ K))
  constructor
  · -- (⇒) Lower bound
    rintro ⟨N, J, line, hs, hroot, hH, hK, hl, hr⟩
    have hH_sub : subtreeHeight N [] ≤ H := by
      apply Finset.sup_le
      intro s hs_mem
      have hsN := (Finset.mem_filter.mp hs_mem).1
      simpa using hH s hsN
    have hK_sub : subtreeLeaves N J [] ≤ K := by
      have : subtreeLeaves N J [] = (N \ J).card := by
        unfold subtreeLeaves
        congr 1; ext s; simp
      rw [this]; exact hK
    let ρ₀ : Raw n b → Option Bool := fun _ => none
    have hF₀ : Falsifies ρ₀ (line []) := by rw [hroot]; intro lit h; simp at h
    have hall₀ : ∀ i : Fin n, 0 < rem ρ₀ i := by intro i; rw [rem_empty]; exact hb
    have hdef₀ : deficit ρ₀ = 0 := deficit_empty hb
    by_cases hb1 : b = 1
    · -- For b = 1, the root itself must be in J and completes a block immediately!
      have hrootJ : [] ∈ J := by
        by_contra hnotJ
        have hleaf : [] ∈ N \ J := Finset.mem_sdiff.mpr ⟨hs.1, hnotJ⟩
        obtain ⟨C, hCF, hC⟩ := leaf_forces_falsified (hl [] hleaf) hF₀
        have hCne : C.Nonempty := by
          rcases hCF with rfl | rfl | rfl | ⟨i, _, rfl⟩ <;> exact Finset.insert_nonempty _ _
        obtain ⟨lit, hlit⟩ := hCne
        have := (hC lit hlit).1; have := hall₀ lit.1; omega
      obtain ⟨⟨v, j⟩, _, _, hnone⟩ := falsifies_resolvent_step (hr [] hrootJ) hF₀
      obtain ⟨hF0, hF1⟩ := hnone rfl
      have hrem1 : rem ρ₀ v = 1 := by rw [rem_empty, hb1]
      rcases first_block_split hn hn2 hb hs hl hr hrootJ hall₀ rfl hrem1 hF0 hF1 with
        ⟨hH1, hK1⟩ | ⟨hH2, hK2⟩
      · rw [hdef₀] at hH1 hK1; simp only [pow_zero, Nat.one_mul, Nat.add_zero] at hH1 hK1
        exact Or.inl ⟨le_trans hH1 hH_sub, le_trans hK1 hK_sub⟩
      · rw [hdef₀] at hH2 hK2; simp only [pow_zero, Nat.one_mul, Nat.add_zero] at hH2 hK2
        exact Or.inr ⟨le_trans hH2 hH_sub, le_trans hK2 hK_sub⟩
    · -- For b ≥ 2, combine lb_init_min with branch_dominance!
      have hb2 : 2 ≤ b := by omega
      have ⟨hKmin, hHmin⟩ := lb_init_min hn hn2 hb hs hl hr (subtreeHeight N []) [] hs.1
        (le_refl _) ρ₀ hF₀ hall₀
      rw [hdef₀] at hKmin hHmin
      simp only [pow_zero, Nat.one_mul, Nat.add_zero] at hKmin hHmin
      rcases branch_dominance hb2 hn2 with ⟨hH12, hK12⟩ | ⟨hH21, hK21⟩
      · rw [min_eq_left hH12] at hHmin
        rw [min_eq_left hK12] at hKmin
        exact Or.inl ⟨le_trans hHmin hH_sub, le_trans hKmin hK_sub⟩
      · rw [min_eq_right hH21] at hHmin
        rw [min_eq_right hK21] at hKmin
        exact Or.inr ⟨le_trans hHmin hH_sub, le_trans hKmin hK_sub⟩
  · -- (⇐) Upper bound
    rintro (⟨hH1, hK1⟩ | ⟨hH2, hK2⟩)
    · obtain ⟨T, hV, hC, hHt, hKt⟩ := build_outerTree1 hn hn2 base
      obtain ⟨N, J, line, hs, hrt, hh, hk, hl, hr⟩ :=
        lift_outerTree hb T hV (fun _ => false) (by rw [hC]; intro _ h; simp at h)
      have hrt0 : line [] = ∅ := by rw [hrt, hC]; simp [liftClause]
      refine ⟨N, J, line, hs, hrt0, ?_, ?_, hl, hr⟩
      · intro p hp
        calc p.length ≤ b * T.height := hh p hp
          _ ≤ b * (1 + Nat.clog 2 n) := Nat.mul_le_mul_left b hHt
          _ ≤ H := hH1
      · rw [hk, hKt]; exact hK1
    · obtain ⟨T, hV, hC, hHt, hKt⟩ := build_outerTree2 hn hn2 base
      obtain ⟨N, J, line, hs, hrt, hh, hk, hl, hr⟩ :=
        lift_outerTree hb T hV (fun _ => false) (by rw [hC]; intro _ h; simp at h)
      have hrt0 : line [] = ∅ := by rw [hrt, hC]; simp [liftClause]
      refine ⟨N, J, line, hs, hrt0, ?_, ?_, hl, hr⟩
      · intro p hp
        calc p.length ≤ b * T.height := hh p hp
          _ ≤ b * Nat.clog 2 (n + 3) := Nat.mul_le_mul_left b hHt
          _ ≤ H := hH2
      · rw [hk, hKt]; exact hK2

end PEqualNP.Outside.L_pcx_308_aux

theorem PEqualNP.Outside.L_pcx_308 :
    ∀ (n : ℕ) (hn : 0 < n) (b : ℕ), 0 < b →
      let w := fun _ : Fin n => b
      let Raw := (i : Fin n) × Fin (w i)
      let parity := fun (y : Raw → Bool) (i : Fin n) =>
        decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
      let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
          (A : PEqualNP.ProofComplexity.Clause Raw) =>
        ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
          A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
            (fun b => (b, !(y b)))
      let shape := fun (N J : Finset (List Bool)) =>
        [] ∈ N ∧ J ⊆ N ∧
        (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
        ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
      let refutes := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (H K : ℕ) =>
        ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw),
          shape N J ∧ line [] = ∅ ∧ (∀ p ∈ N, p.length ≤ H) ∧ (N \ J).card ≤ K ∧
          (∀ p ∈ N \ J, liftAx F (line p)) ∧
          ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
            (line (p ++ [false])) (line (p ++ [true])) (line p)
      let base := 2^(b-1)
      let balanced := fun m : ℕ =>
        let d := Nat.clog 2 m
        (2^d-m)*base^(d-1) + (2*m-2^d)*base^d
      let atV := fun i : ℕ => (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n)
      let first := atV 0
      let last := atV (n-1)
      let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) := {C |
        C = {(last,true),(first,true)} ∨ C = {(last,false),(first,true)} ∨
          C = {(last,false),(first,false)} ∨
        ∃ i : ℕ, i+1 < n ∧ C = {(atV i,false),(atV (i+1),true)}}
      ∀ H K : ℕ, 2 ≤ n →
        Iff (refutes F H K)
          ((b*(1+Nat.clog 2 n) ≤ H ∧ base*(2*base + balanced n) ≤ K) ∨
           (b*Nat.clog 2 (n+3) ≤ H ∧ balanced (n+3) ≤ K)) :=
  PEqualNP.Outside.L_pcx_308_aux.main_proof
