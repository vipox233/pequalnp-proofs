import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_887_aux

lemma rpow_lt_linear (t p : ℝ) (ht : 0 < t) (ht1 : t ≠ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    t ^ p < p * t + (1 - p) := by
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have hs1 : 0 < t ^ (1 - p) := Real.rpow_pos_of_pos ht (1 - p)
  have hs1_ne : t ^ (1 - p) ≠ 1 := by
    intro h
    have hlog : Real.log (t ^ (1 - p)) = 0 := by rw [h, Real.log_one]
    rw [Real.log_rpow ht] at hlog
    rcases mul_eq_zero.mp hlog with h0 | h0
    · linarith
    · rcases Real.log_eq_zero.mp h0 with rfl | rfl | rfl <;> first | exact ht1 rfl | linarith
  have hs2 : 0 < t ^ (-p) := Real.rpow_pos_of_pos ht (-p)
  have hs2_ne : t ^ (-p) ≠ 1 := by
    intro h
    have hlog : Real.log (t ^ (-p)) = 0 := by rw [h, Real.log_one]
    rw [Real.log_rpow ht] at hlog
    rcases mul_eq_zero.mp hlog with h0 | h0
    · linarith
    · rcases Real.log_eq_zero.mp h0 with rfl | rfl | rfl <;> first | exact ht1 rfl | linarith
  have hL1 := Real.log_lt_sub_one_of_pos hs1 hs1_ne
  have hL2 := Real.log_lt_sub_one_of_pos hs2 hs2_ne
  rw [Real.log_rpow ht] at hL1 hL2
  have hm1 := mul_lt_mul_of_pos_left hL1 hp0
  have hm2 := mul_lt_mul_of_pos_left hL2 h1p
  have hsum : p * ((1 - p) * Real.log t) + (1 - p) * (-p * Real.log t) = 0 := by ring
  have hlt : 0 < p * (t ^ (1 - p) - 1) + (1 - p) * (t ^ (-p) - 1) := by linarith
  have hpow1 : t ^ (1 - p) = t / t ^ p := by
    rw [Real.rpow_sub ht, Real.rpow_one]
  have hpow2 : t ^ (-p) = 1 / t ^ p := by
    rw [Real.rpow_neg ht.le, one_div]
  rw [hpow1, hpow2] at hlt
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hmul : 0 < t ^ p * (p * (t / t ^ p - 1) + (1 - p) * (1 / t ^ p - 1)) := mul_pos htp hlt
  have hid : t ^ p * (p * (t / t ^ p - 1) + (1 - p) * (1 / t ^ p - 1)) =
      p * t + (1 - p) - t ^ p := by
    field_simp [htp.ne']
    ring
  linarith

lemma rpow_le_linear (t p : ℝ) (ht : 0 ≤ t) (hp0 : 0 < p) (hp1 : p < 1) :
    t ^ p ≤ p * t + (1 - p) := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [Real.zero_rpow hp0.ne']
    linarith
  · by_cases ht1 : t = 1
    · subst ht1
      rw [Real.one_rpow]
      linarith
    · exact (rpow_lt_linear t p hpos ht1 hp0 hp1).le

lemma rpow_eq_linear_iff (t p : ℝ) (ht : 0 ≤ t) (hp0 : 0 < p) (hp1 : p < 1) :
    t ^ p = p * t + (1 - p) ↔ t = 1 := by
  constructor
  · intro heq
    by_contra ht1
    rcases eq_or_lt_of_le ht with rfl | hpos
    · rw [Real.zero_rpow hp0.ne'] at heq
      linarith
    · exact (rpow_lt_linear t p hpos ht1 hp0 hp1).ne heq
  · rintro rfl
    rw [Real.one_rpow]
    ring

lemma local_factor_bound (a t : ℕ) (ha : 3 ≤ a) (ht : t ≤ a) :
    let q : ℝ := (2 : ℝ) ^ a
    let ρ : ℝ := 1 - 4 / q
    let c : ℝ := 1 - 2 / q
    ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ)) ≤ c ^ (2 * (t : ℝ) / (a : ℝ)) := by
  intro q ρ c
  have hq8 : (8 : ℝ) ≤ q := by
    have hpow : (8 : ℕ) ≤ 2 ^ a := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    calc (8 : ℝ) = ((8 : ℕ) : ℝ) := by norm_num
      _ ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast hpow
      _ = q := by push_cast [q]; rfl
  have hq0 : 0 < q := by linarith
  have hc_pos : 0 < c := by
    change 0 < 1 - 2 / q
    rw [sub_pos, div_lt_one hq0]
    linarith
  have hc_lt : c < 1 := by
    change 1 - 2 / q < 1
    have : 0 < 2 / q := div_pos (by norm_num) hq0
    linarith
  have hρ_pos : 0 < ρ := by
    change 0 < 1 - 4 / q
    rw [sub_pos, div_lt_one hq0]
    linarith
  have h1ρ_pos : 0 < 1 - ρ := by
    change 0 < 1 - (1 - 4 / q)
    linarith [div_pos (by norm_num : (0 : ℝ) < 4) hq0]
  have hS_eq : ρ + (1 - ρ) / q = c ^ 2 := by
    change (1 - 4 / q) + (1 - (1 - 4 / q)) / q = (1 - 2 / q) ^ 2
    field_simp [hq0.ne']
    ring
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp
  · by_cases hta : t = a
    · subst hta
      have ht0' : (t : ℝ) ≠ 0 := by positivity
      have hexp : 2 * (t : ℝ) / (t : ℝ) = ((2 : ℕ) : ℝ) := by field_simp [ht0']; norm_num
      rw [hexp, Real.rpow_natCast]
      have h2t : (2 : ℝ) ^ (-(t : ℝ)) = 1 / q := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
      rw [h2t, mul_one_div, hS_eq]
    · have hta_lt : t < a := lt_of_le_of_ne ht hta
      have ha_pos : (0 : ℝ) < a := by positivity
      let p : ℝ := (t : ℝ) / (a : ℝ)
      have hp0 : 0 < p := div_pos (by positivity) ha_pos
      have hp1 : p < 1 := (div_lt_one ha_pos).mpr (by exact_mod_cast hta_lt)
      let S : ℝ := c ^ 2
      have hS0 : 0 < S := sq_pos_of_pos hc_pos
      have hS1 : S < 1 := by
        nlinarith [hc_pos, hc_lt]
      have hu1_gt : 1 < 1 / S := one_lt_one_div hS0 hS1
      have hle1 := rpow_lt_linear (1 / S) p (by positivity) hu1_gt.ne' hp0 hp1
      have hu2_nn : 0 ≤ 1 / (q * S) := by positivity
      have hle2 := rpow_le_linear (1 / (q * S)) p hu2_nn hp0 hp1
      have hmul1 : ρ * (1 / S) ^ p < ρ * (p * (1 / S) + (1 - p)) :=
        mul_lt_mul_of_pos_left hle1 hρ_pos
      have hmul2 : (1 - ρ) * (1 / (q * S)) ^ p ≤ (1 - ρ) * (p * (1 / (q * S)) + (1 - p)) :=
        mul_le_mul_of_nonneg_left hle2 h1ρ_pos.le
      have hcomb : ρ * (1 / S) ^ p + (1 - ρ) * (1 / (q * S)) ^ p < 1 := by
        have hrhs : ρ * (p * (1 / S) + (1 - p)) + (1 - ρ) * (p * (1 / (q * S)) + (1 - p)) =
            p * ((ρ + (1 - ρ) / q) / S) + (1 - p) := by
          field_simp [hq0.ne', hS0.ne']
          ring
        rw [hS_eq, show c ^ 2 = S from rfl, div_self hS0.ne', mul_one] at hrhs
        linarith
      have hSp : 0 < S ^ p := Real.rpow_pos_of_pos hS0 p
      have hq_rpow : q ^ p = (2 : ℝ) ^ (t : ℝ) := by
        change ((2 : ℝ) ^ a) ^ ((t : ℝ) / (a : ℝ)) = (2 : ℝ) ^ (t : ℝ)
        rw [← Real.rpow_natCast (2 : ℝ) a, ← Real.rpow_mul (by norm_num)]
        congr 1
        field_simp [ha_pos.ne']
      have hlhs : (ρ * (1 / S) ^ p + (1 - ρ) * (1 / (q * S)) ^ p) * S ^ p =
          ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ)) := by
        rw [one_div, Real.inv_rpow hS0.le, one_div,
          Real.inv_rpow (mul_pos hq0 hS0).le, Real.mul_rpow hq0.le hS0.le, hq_rpow]
        rw [Real.rpow_neg (by norm_num)]
        field_simp [hSp.ne', (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (t : ℝ)).ne']
      have hcexp : c ^ (2 * (t : ℝ) / (a : ℝ)) = S ^ p := by
        change c ^ (2 * (t : ℝ) / (a : ℝ)) = (c ^ 2) ^ p
        rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc_pos.le]
        congr 1
        simp only [p]
        ring
      rw [hcexp, ← hlhs]
      nlinarith

lemma local_factor_eq_iff (a t : ℕ) (ha : 3 ≤ a) (ht : t ≤ a) :
    let q : ℝ := (2 : ℝ) ^ a
    let ρ : ℝ := 1 - 4 / q
    let c : ℝ := 1 - 2 / q
    ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ)) = c ^ (2 * (t : ℝ) / (a : ℝ)) ↔ t = 0 ∨ t = a := by
  intro q ρ c
  have hq8 : (8 : ℝ) ≤ q := by
    have hpow : (8 : ℕ) ≤ 2 ^ a := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    calc (8 : ℝ) = ((8 : ℕ) : ℝ) := by norm_num
      _ ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast hpow
      _ = q := by push_cast [q]; rfl
  have hq0 : 0 < q := by linarith
  have hc_pos : 0 < c := by
    change 0 < 1 - 2 / q
    rw [sub_pos, div_lt_one hq0]
    linarith
  have hc_lt : c < 1 := by
    change 1 - 2 / q < 1
    linarith [div_pos (by norm_num : (0 : ℝ) < 2) hq0]
  have hρ_pos : 0 < ρ := by
    change 0 < 1 - 4 / q
    rw [sub_pos, div_lt_one hq0]
    linarith
  have h1ρ_pos : 0 < 1 - ρ := by
    change 0 < 1 - (1 - 4 / q)
    linarith [div_pos (by norm_num : (0 : ℝ) < 4) hq0]
  have hS_eq : ρ + (1 - ρ) / q = c ^ 2 := by
    change (1 - 4 / q) + (1 - (1 - 4 / q)) / q = (1 - 2 / q) ^ 2
    field_simp [hq0.ne']
    ring
  constructor
  · intro heq
    by_contra hne
    push Not at hne
    have ht0 : 0 < t := Nat.pos_of_ne_zero hne.1
    have hta_lt : t < a := lt_of_le_of_ne ht hne.2
    have ha_pos : (0 : ℝ) < a := by positivity
    let p : ℝ := (t : ℝ) / (a : ℝ)
    have hp0 : 0 < p := div_pos (by positivity) ha_pos
    have hp1 : p < 1 := (div_lt_one ha_pos).mpr (by exact_mod_cast hta_lt)
    let S : ℝ := c ^ 2
    have hS0 : 0 < S := sq_pos_of_pos hc_pos
    have hS1 : S < 1 := by nlinarith [hc_pos, hc_lt]
    have hu1_gt : 1 < 1 / S := one_lt_one_div hS0 hS1
    have hle1 := rpow_lt_linear (1 / S) p (by positivity) hu1_gt.ne' hp0 hp1
    have hle2 := rpow_le_linear (1 / (q * S)) p (by positivity) hp0 hp1
    have hmul1 : ρ * (1 / S) ^ p < ρ * (p * (1 / S) + (1 - p)) :=
      mul_lt_mul_of_pos_left hle1 hρ_pos
    have hmul2 : (1 - ρ) * (1 / (q * S)) ^ p ≤ (1 - ρ) * (p * (1 / (q * S)) + (1 - p)) :=
      mul_le_mul_of_nonneg_left hle2 h1ρ_pos.le
    have hcomb : ρ * (1 / S) ^ p + (1 - ρ) * (1 / (q * S)) ^ p < 1 := by
      have hrhs : ρ * (p * (1 / S) + (1 - p)) + (1 - ρ) * (p * (1 / (q * S)) + (1 - p)) =
          p * ((ρ + (1 - ρ) / q) / S) + (1 - p) := by
        field_simp [hq0.ne', hS0.ne']
        ring
      rw [hS_eq, show c ^ 2 = S from rfl, div_self hS0.ne', mul_one] at hrhs
      linarith
    have hSp : 0 < S ^ p := Real.rpow_pos_of_pos hS0 p
    have hq_rpow : q ^ p = (2 : ℝ) ^ (t : ℝ) := by
      change ((2 : ℝ) ^ a) ^ ((t : ℝ) / (a : ℝ)) = (2 : ℝ) ^ (t : ℝ)
      rw [← Real.rpow_natCast (2 : ℝ) a, ← Real.rpow_mul (by norm_num)]
      congr 1
      field_simp [ha_pos.ne']
    have hlhs : (ρ * (1 / S) ^ p + (1 - ρ) * (1 / (q * S)) ^ p) * S ^ p =
        ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ)) := by
      rw [one_div, Real.inv_rpow hS0.le, one_div,
        Real.inv_rpow (mul_pos hq0 hS0).le, Real.mul_rpow hq0.le hS0.le, hq_rpow]
      rw [Real.rpow_neg (by norm_num)]
      field_simp [hSp.ne', (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (t : ℝ)).ne']
    have hcexp : c ^ (2 * (t : ℝ) / (a : ℝ)) = S ^ p := by
      change c ^ (2 * (t : ℝ) / (a : ℝ)) = (c ^ 2) ^ p
      rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc_pos.le]
      congr 1
      simp only [p]
      ring
    rw [hcexp, ← hlhs] at heq
    have : (ρ * (1 / S) ^ p + (1 - ρ) * (1 / (q * S)) ^ p) * S ^ p < 1 * S ^ p :=
      mul_lt_mul_of_pos_right hcomb hSp
    linarith
  · rintro (rfl | rfl)
    · simp
    · have ht0' : (t : ℝ) ≠ 0 := by positivity
      have hexp : 2 * (t : ℝ) / (t : ℝ) = ((2 : ℕ) : ℝ) := by field_simp [ht0']; norm_num
      rw [hexp, Real.rpow_natCast]
      have h2t : (2 : ℝ) ^ (-(t : ℝ)) = 1 / q := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
      rw [h2t, mul_one_div, hS_eq]

lemma sum_rpow_le (N : ℕ) (hN : 0 < N) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    ∑ i, (x i) ^ p ≤ (N : ℝ) ^ (1 - p) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hNp : 0 < (N : ℝ) ^ p := Real.rpow_pos_of_pos hNpos p
  have hle : ∀ i : Fin N, ((N : ℝ) * x i) ^ p ≤ p * ((N : ℝ) * x i) + (1 - p) :=
    fun i => rpow_le_linear ((N : ℝ) * x i) p (mul_nonneg hNpos.le (hx i)) hp0 hp1
  have hsum_le : ∑ i : Fin N, ((N : ℝ) * x i) ^ p ≤ ∑ i : Fin N, (p * ((N : ℝ) * x i) + (1 - p)) :=
    Finset.sum_le_sum (fun i _ => hle i)
  have hlhs : ∑ i : Fin N, ((N : ℝ) * x i) ^ p = (N : ℝ) ^ p * ∑ i : Fin N, (x i) ^ p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.mul_rpow hNpos.le (hx i)]
  have hrhs : ∑ i : Fin N, (p * ((N : ℝ) * x i) + (1 - p)) = (N : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hmul : ∑ i : Fin N, p * ((N : ℝ) * x i) = p * (N : ℝ) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_one]
    rw [hmul]
    ring
  rw [hlhs, hrhs] at hsum_le
  have hdiv : ∑ i, (x i) ^ p ≤ (N : ℝ) / (N : ℝ) ^ p := (le_div_iff₀' hNp).mpr hsum_le
  calc ∑ i, (x i) ^ p ≤ (N : ℝ) / (N : ℝ) ^ p := hdiv
    _ = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ p := by rw [Real.rpow_one]
    _ = (N : ℝ) ^ (1 - p) := (Real.rpow_sub hNpos 1 p).symm

lemma sum_rpow_eq_iff (N : ℕ) (hN : 0 < N) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    ∑ i, (x i) ^ p = (N : ℝ) ^ (1 - p) ↔ ∀ i, x i = 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hNp : 0 < (N : ℝ) ^ p := Real.rpow_pos_of_pos hNpos p
  have hle : ∀ i : Fin N, ((N : ℝ) * x i) ^ p ≤ p * ((N : ℝ) * x i) + (1 - p) :=
    fun i => rpow_le_linear ((N : ℝ) * x i) p (mul_nonneg hNpos.le (hx i)) hp0 hp1
  have hlhs : ∑ i : Fin N, ((N : ℝ) * x i) ^ p = (N : ℝ) ^ p * ∑ i : Fin N, (x i) ^ p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.mul_rpow hNpos.le (hx i)]
  have hrhs : ∑ i : Fin N, (p * ((N : ℝ) * x i) + (1 - p)) = (N : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hmul : ∑ i : Fin N, p * ((N : ℝ) * x i) = p * (N : ℝ) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_one]
    rw [hmul]
    ring
  have hN1p : (N : ℝ) ^ p * (N : ℝ) ^ (1 - p) = (N : ℝ) := by
    rw [← Real.rpow_add hNpos]
    simp
  constructor
  · intro heq i
    have heq2 : ∑ j : Fin N, ((N : ℝ) * x j) ^ p = ∑ j : Fin N, (p * ((N : ℝ) * x j) + (1 - p)) := by
      rw [hlhs, hrhs, heq, hN1p]
    have hpt := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp heq2 i (Finset.mem_univ i)
    have h1 := (rpow_eq_linear_iff ((N : ℝ) * x i) p (mul_nonneg hNpos.le (hx i)) hp0 hp1).mp hpt
    field_simp [hNpos.ne'] at h1 ⊢
    linarith
  · intro hall
    have hcongr : ∑ i : Fin N, (x i) ^ p = ∑ _ : Fin N, (1 / (N : ℝ)) ^ p :=
      Finset.sum_congr rfl (fun i _ => by rw [hall i])
    rw [hcongr, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, one_div,
      Real.inv_rpow hNpos.le]
    have : (N : ℝ) * ((N : ℝ) ^ p)⁻¹ = (N : ℝ) ^ (1 - p) := by
      rw [Real.rpow_sub hNpos, Real.rpow_one, div_eq_mul_inv]
    exact this

lemma exists_affine_cylinder (a m r : ℕ) (hr : r ≤ m) :
    let F := ZMod 2
    let W := Fin m → Fin a → F
    let q := 2 ^ a
    let M := Fin (q ^ (m - r))
    ∃ send : W → M,
      (∀ x : W, ∃ H : Submodule F W, ∀ y : W, send y = send x ↔ y - x ∈ H) ∧
      (∀ label : M, ∃ (center : W) (free : Finset (Fin m)),
        free.card = r ∧
        (∀ u : W, send u = label ↔ ∀ i : Fin m, i ∉ free → u i = center i) ∧
        (∀ u : W, send u = label → false = false)) := by
  intro F W q M
  let free0 : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.val < r)
  have hfree0_card : free0.card = r := by
    have himg : free0 = (Finset.range r).attach.map
        ⟨fun k => ⟨k.1, lt_of_lt_of_le (Finset.mem_range.mp k.2) hr⟩,
          fun k1 k2 h => Subtype.ext (Fin.mk.inj h)⟩ := by
      ext i
      simp only [free0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_attach, Function.Embedding.coeFn_mk, Subtype.exists, Finset.mem_range]
      constructor
      · intro hi
        exact ⟨i.val, hi, Fin.ext rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact hk
    rw [himg, Finset.card_map, Finset.card_attach, Finset.card_range]
  let Fixed := {i : Fin m // ¬ (i.val < r)}
  have hfixed_card : Fintype.card Fixed = m - r := by
    rw [Fintype.card_subtype]
    have hcomp : (Finset.univ.filter (fun i : Fin m => ¬ (i.val < r))) = Finset.univ \ free0 := by
      ext i
      simp [free0]
    rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hfree0_card]
  have hcard : Fintype.card (Fixed → Fin a → F) = Fintype.card M := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ZMod.card, hfixed_card,
      Fintype.card_fin]
  let e : (Fixed → Fin a → F) ≃ M := Fintype.equivOfCardEq hcard
  let send : W → M := fun w => e (fun i => w i.1)
  let H : Submodule F W :=
    { carrier := {h : W | ∀ i : Fin m, ¬ (i.val < r) → h i = 0},
      zero_mem' := fun _ _ => rfl, add_mem' := fun hx hy i hi => by rw [Pi.add_apply, hx i hi, hy i hi, add_zero],
      smul_mem' := fun c _ hx i hi => by rw [Pi.smul_apply, hx i hi, smul_zero] }
  have hH_mem : ∀ w : W, w ∈ H ↔ ∀ i : Fin m, ¬ (i.val < r) → w i = 0 := fun _ => Iff.rfl
  refine ⟨send, ?_, ?_⟩
  · intro x
    refine ⟨H, fun y => ?_⟩
    rw [hH_mem]
    constructor
    · intro hy i hi
      have hy' : (fun j : Fixed => y j.1) = (fun j : Fixed => x j.1) := e.injective hy
      exact sub_eq_zero.mpr (congrFun hy' ⟨i, hi⟩)
    · intro h
      apply congrArg e
      ext j : 1
      exact sub_eq_zero.mp (h j.1 j.2)
  · intro label
    let g := e.symm label
    let center : W := fun i => if hi : i.val < r then 0 else g ⟨i, hi⟩
    refine ⟨center, free0, hfree0_card, ?_, fun _ _ => rfl⟩
    intro u
    simp only [send, free0, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h i hi
      have h1 : (fun j : Fixed => u j.1) = g := e.injective (by simpa [g] using h)
      have h2 := congrFun h1 ⟨i, hi⟩
      simpa [center, hi] using h2
    · intro h
      have h1 : (fun j : Fixed => u j.1) = g := by
        ext j k
        have h2 := congrFun (h j.1 j.2) k
        simpa [center, j.2] using h2
      simpa [g] using congrArg e h1

def sgn (b : Bool) : ℝ := if b then -1 else 1

@[simp] lemma sgn_true : sgn true = -1 := rfl
@[simp] lemma sgn_false : sgn false = 1 := rfl

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num

lemma sgn_le_one (b : Bool) : sgn b ≤ 1 := by
  cases b <;> norm_num

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> norm_num

lemma sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> norm_num

lemma sgn_beq (a b : Bool) : sgn (a == b) = -(sgn a * sgn b) := by
  cases a <;> cases b <;> norm_num

lemma sgn_mod2_eq_one (n : ℕ) : sgn (n % 2 == 1) = (-1 : ℝ) ^ n := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases h with h0 | h1
  · have : (n % 2 == 1) = false := by rw [h0]; decide
    rw [this, sgn_false]
    exact (Even.neg_one_pow (Nat.even_iff.mpr h0)).symm
  · have : (n % 2 == 1) = true := by rw [h1]; decide
    rw [this, sgn_true]
    exact (Odd.neg_one_pow (Nat.odd_iff.mpr h1)).symm

def chi {a m : ℕ} (x y : Fin m → Fin a → ZMod 2) : ℝ :=
  ∏ i : Fin m, (if x i = y i then (-1 : ℝ) else 1)

lemma chi_eq_sgn {a m : ℕ} (x y : Fin m → Fin a → ZMod 2) :
    sgn (((Finset.univ.filter (fun i : Fin m => x i = y i)).card % 2) == 1) = chi x y := by
  rw [sgn_mod2_eq_one]
  unfold chi
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

def wt {a m : ℕ} (h : Fin m → Fin a → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => h i ≠ 0)).card

lemma chi_inner {a m : ℕ} (x x' : Fin m → Fin a → ZMod 2) :
    let q : ℝ := (2 : ℝ) ^ a
    let ρ : ℝ := 1 - 4 / q
    ∑ y : Fin m → Fin a → ZMod 2, chi x y * chi x' y = q ^ m * ρ ^ wt (x - x') := by
  intro q ρ
  have hprod : ∀ y : Fin m → Fin a → ZMod 2,
      chi x y * chi x' y = ∏ i : Fin m, (if x i = y i then (-1 : ℝ) else 1) * (if x' i = y i then (-1 : ℝ) else 1) := by
    intro y
    unfold chi
    rw [← Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun i z => (if x i = z then (-1 : ℝ) else 1) * (if x' i = z then (-1 : ℝ) else 1))]
  have hq0 : q ≠ 0 := by positivity
  have hcoord : ∀ i : Fin m,
      (∑ z : Fin a → ZMod 2, (if x i = z then (-1 : ℝ) else 1) * (if x' i = z then (-1 : ℝ) else 1)) =
        q * (if (x - x') i ≠ 0 then ρ else 1) := by
    intro i
    have hcard : (Fintype.card (Fin a → ZMod 2) : ℝ) = q := by
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
      push_cast
      rfl
    by_cases heq : x i = x' i
    · have hsub : ¬ ((x - x') i ≠ 0) := by simp [heq]
      simp only [hsub, ↓reduceIte, mul_one]
      have h1 : ∀ z : Fin a → ZMod 2, (if x i = z then (-1 : ℝ) else 1) * (if x' i = z then (-1 : ℝ) else 1) = 1 := by
        intro z
        rw [← heq]
        split_ifs <;> norm_num
      simp_rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
    · have hsub : (x - x') i ≠ 0 := by simpa [sub_eq_zero] using heq
      rw [if_pos hsub]
      have hsum_split : ∑ z : Fin a → ZMod 2,
          (if x i = z then (-1 : ℝ) else 1) * (if x' i = z then (-1 : ℝ) else 1) =
          ∑ z : Fin a → ZMod 2, ((1 : ℝ) + (if z = x i then -2 else 0) + (if z = x' i then -2 else 0)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hzx : z = x i <;> by_cases hzx' : z = x' i <;>
          simp [hzx, hzx', heq, eq_comm] <;> norm_num
      rw [hsum_split, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      change q + -2 + -2 = q * (1 - 4 / q)
      field_simp [hq0]
      ring
  simp_rw [hcoord, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  unfold wt
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

lemma zmod2_neg_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v : V) : -v = v := by
  have h : (2 : ZMod 2) • v = 0 := by
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_smul]
  have h2 : v + v = 0 := by
    simpa [two_smul] using h
  exact neg_eq_iff_add_eq_zero.mpr h2

lemma zmod2_sub_eq_add {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (u v : V) : u - v = u + v := by
  rw [sub_eq_add_neg, zmod2_neg_eq]

lemma sum_fib {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β)
    (g : α → β) (hmaps : ∀ x ∈ s, g x ∈ t) (f : α → ℝ) :
    ∑ x ∈ s, f x = ∑ y ∈ t, ∑ x ∈ s.filter (fun x => g x = y), f x := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_ite_eq t (g x) (fun _ => f x), if_pos (hmaps x hx)]

lemma submodule_card_eq_pow {a m : ℕ} (H : Submodule (ZMod 2) (Fin m → Fin a → ZMod 2))
    [DecidablePred (· ∈ H)] :
    (Finset.univ.filter (fun h : Fin m → Fin a → ZMod 2 => h ∈ H)).card = 2 ^ Module.finrank (ZMod 2) H := by
  letI : Fintype H := Fintype.ofFinite _
  have h1 : (Finset.univ.filter (fun h : Fin m → Fin a → ZMod 2 => h ∈ H)).card = Fintype.card H := by
    rw [Fintype.card_subtype]
  rw [h1]
  let b := Module.finBasis (ZMod 2) H
  have h2 : Fintype.card H = Fintype.card (Fin (Module.finrank (ZMod 2) H) → ZMod 2) :=
    Fintype.card_congr b.equivFun.toEquiv
  rw [h2, Fintype.card_fun, Fintype.card_fin, ZMod.card]

lemma submodule_local_card_eq_pow {a : ℕ} (V : Submodule (ZMod 2) (Fin a → ZMod 2))
    [DecidablePred (· ∈ V)] :
    (Finset.univ.filter (fun v : Fin a → ZMod 2 => v ∈ V)).card = 2 ^ Module.finrank (ZMod 2) V := by
  letI : Fintype V := Fintype.ofFinite _
  have h1 : (Finset.univ.filter (fun v : Fin a → ZMod 2 => v ∈ V)).card = Fintype.card V := by
    rw [Fintype.card_subtype]
  rw [h1]
  let b := Module.finBasis (ZMod 2) V
  have h2 : Fintype.card V = Fintype.card (Fin (Module.finrank (ZMod 2) V) → ZMod 2) :=
    Fintype.card_congr b.equivFun.toEquiv
  rw [h2, Fintype.card_fun, Fintype.card_fin, ZMod.card]

noncomputable def Phi (a m : ℕ) (H : Submodule (ZMod 2) (Fin m → Fin a → ZMod 2)) : ℝ :=
  letI : DecidablePred (· ∈ H) := Classical.decPred _
  (∑ h : Fin m → Fin a → ZMod 2, if h ∈ H then (1 - 4 / ((2 : ℝ) ^ a)) ^ wt h else 0) /
    ((Finset.univ.filter (fun h : Fin m → Fin a → ZMod 2 => h ∈ H)).card : ℝ)

set_option maxHeartbeats 800000 in
lemma Phi_ind (a : ℕ) (ha : 3 ≤ a) :
    let q : ℝ := (2 : ℝ) ^ a
    let c : ℝ := 1 - 2 / q
    ∀ (m : ℕ) (H : Submodule (ZMod 2) (Fin m → Fin a → ZMod 2)),
    Phi a m H ≤ c ^ (2 * (Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) ∧
    (Phi a m H = c ^ (2 * (Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) →
      ∃ free : Finset (Fin m), a * free.card = Module.finrank (ZMod 2) H ∧
        ∀ h : Fin m → Fin a → ZMod 2, h ∈ H ↔ ∀ i : Fin m, i ∉ free → h i = 0) := by
  intro q c m
  have hq8 : (8 : ℝ) ≤ q := by
    have hpow : (8 : ℕ) ≤ 2 ^ a := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    calc (8 : ℝ) = ((8 : ℕ) : ℝ) := by norm_num
      _ ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast hpow
      _ = q := by push_cast [q]; rfl
  have hq0 : 0 < q := by linarith
  have hc_pos : 0 < c := by
    change 0 < 1 - 2 / q
    rw [sub_pos, div_lt_one hq0]
    linarith
  let ρ : ℝ := 1 - 4 / q
  have hρ_pos : 0 < ρ := by
    change 0 < 1 - 4 / q
    rw [sub_pos, div_lt_one hq0]
    linarith
  have h1ρ_pos : 0 < 1 - ρ := by
    change 0 < 1 - (1 - 4 / q)
    linarith [div_pos (by norm_num : (0 : ℝ) < 4) hq0]
  induction m with
  | zero =>
    intro H
    letI : DecidablePred (· ∈ H) := Classical.decPred _
    have hdim : Module.finrank (ZMod 2) H = 0 := by
      have hsub : Subsingleton (Fin 0 → Fin a → ZMod 2) := inferInstance
      exact Module.finrank_zero_of_subsingleton
    have hcard : (Finset.univ.filter (fun h : Fin 0 → Fin a → ZMod 2 => h ∈ H)).card = 1 := by
      rw [submodule_card_eq_pow, hdim, pow_zero]
    have hphi : Phi a 0 H = 1 := by
      unfold Phi
      have hwt0 : wt (0 : Fin 0 → Fin a → ZMod 2) = 0 := by simp [wt]
      have huniq : ∀ h : Fin 0 → Fin a → ZMod 2, h = 0 := fun h => Subsingleton.elim h 0
      have hsum : (∑ h : Fin 0 → Fin a → ZMod 2, if h ∈ H then (1 - 4 / ((2 : ℝ) ^ a)) ^ wt h else 0) = 1 := by
        rw [Finset.sum_eq_single (0 : Fin 0 → Fin a → ZMod 2)]
        · rw [if_pos H.zero_mem, hwt0, pow_zero]
        · intro b _ hb; exact absurd (huniq b) hb
        · intro hmem; exact absurd (Finset.mem_univ 0) hmem
      have hcard' : ((Finset.univ.filter (fun h : Fin 0 → Fin a → ZMod 2 => h ∈ H)).card : ℝ) = 1 := by
        exact_mod_cast hcard
      rw [hsum, hcard', div_one]
    rw [hphi, hdim]
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.rpow_zero]
    refine ⟨le_rfl, fun _ => ⟨∅, by simp, fun h => ⟨fun _ i _ => Fin.elim0 i, fun _ => by rw [Subsingleton.elim h 0]; exact H.zero_mem⟩⟩⟩
  | succ m ih =>
    intro H
    let F := ZMod 2
    let W1 := Fin (m + 1) → Fin a → F
    let W0 := Fin m → Fin a → F
    let tail : W1 →ₗ[F] W0 :=
      { toFun := fun w i => w i.succ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    let head : W1 →ₗ[F] (Fin a → F) :=
      { toFun := fun w => w 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    let H' : Submodule F W0 := H.map tail
    let K : Submodule F W1 := H ⊓ LinearMap.ker tail
    let V : Submodule F (Fin a → F) := K.map head
    have hhead_inj : ∀ k ∈ K, head k = 0 → k = 0 := by
      intro k hk h0
      ext i j
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · exact congrFun h0 j
      · have hker : tail k = 0 := (Submodule.mem_inf.mp hk).2
        exact congrFun (congrFun hker i') j
    have hdim_KV : Module.finrank F K = Module.finrank F V := by
      let f : K →ₗ[F] V :=
        { toFun := fun k => ⟨head k.1, Submodule.mem_map_of_mem k.2⟩,
          map_add' := fun x y => Subtype.ext (head.map_add x.1 y.1),
          map_smul' := fun c x => Subtype.ext (head.map_smul c x.1) }
      have hf_inj : Function.Injective f := by
        intro x y hxy
        have h0 : head (x.1 - y.1) = 0 := by
          rw [head.map_sub, sub_eq_zero]
          exact congrArg Subtype.val hxy
        exact Subtype.ext (sub_eq_zero.mp (hhead_inj (x.1 - y.1) (K.sub_mem x.2 y.2) h0))
      have hf_surj : Function.Surjective f := by
        rintro ⟨v, hv⟩
        obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hv
        exact ⟨⟨k, hk⟩, rfl⟩
      exact (LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).finrank_eq
    have hdim_sum : Module.finrank F H' + Module.finrank F K = Module.finrank F H := by
      let g : H →ₗ[F] W0 := tail.domRestrict H
      have hrng : LinearMap.range g ≃ₗ[F] H' :=
        LinearEquiv.ofEq (LinearMap.range g) H' (by
          ext y
          simp only [LinearMap.mem_range, Subtype.exists, Submodule.mem_map, g,
            LinearMap.domRestrict_apply]
          constructor
          · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
          · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩)
      let fker : LinearMap.ker g →ₗ[F] K :=
        { toFun := fun x => ⟨x.1.1, x.1.2, by exact x.2⟩,
          map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      have hfker_inj : Function.Injective fker := fun x y h =>
        Subtype.ext (Subtype.ext (congrArg (fun z : K => z.1) h))
      have hfker_surj : Function.Surjective fker := fun ⟨x, hx⟩ =>
        ⟨⟨⟨x, hx.1⟩, hx.2⟩, rfl⟩
      have hker : LinearMap.ker g ≃ₗ[F] K := LinearEquiv.ofBijective fker ⟨hfker_inj, hfker_surj⟩
      have hrk := LinearMap.finrank_range_add_finrank_ker g
      rw [hrng.finrank_eq, hker.finrank_eq] at hrk
      exact hrk
    have hdim_H : Module.finrank F H = Module.finrank F H' + Module.finrank F V := by
      rw [← hdim_KV, hdim_sum]
    let t : ℕ := Module.finrank F V
    have ht_le : t ≤ a := by
      have h := Submodule.finrank_le V
      simpa [t, Module.finrank_fin_fun] using h
    letI : DecidablePred (· ∈ H) := Classical.decPred _
    letI : DecidablePred (· ∈ H') := Classical.decPred _
    letI : DecidablePred (· ∈ V) := Classical.decPred _
    let Hset := Finset.univ.filter (fun h : W1 => h ∈ H)
    let H'set := Finset.univ.filter (fun h' : W0 => h' ∈ H')
    let Vset := Finset.univ.filter (fun v : Fin a → F => v ∈ V)
    have hHcard : (Hset.card : ℝ) = (H'set.card : ℝ) * (Vset.card : ℝ) := by
      have h1 : Hset.card = 2 ^ Module.finrank F H := submodule_card_eq_pow H
      have h2 : H'set.card = 2 ^ Module.finrank F H' := submodule_card_eq_pow H'
      have h3 : Vset.card = 2 ^ Module.finrank F V := submodule_local_card_eq_pow V
      rw [h1, h2, h3, hdim_H, pow_add]
      push_cast
      ring
    have hVcard_pos : (0 : ℝ) < Vset.card := by
      rw [submodule_local_card_eq_pow]
      positivity
    have hH'card_pos : (0 : ℝ) < H'set.card := by
      rw [submodule_card_eq_pow]
      positivity
    have hVcard_pow : (Vset.card : ℝ) = (2 : ℝ) ^ (t : ℝ) := by
      rw [submodule_local_card_eq_pow]
      change ((2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ (t : ℝ)
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    have hsum_split : (∑ h : W1, if h ∈ H then ρ ^ wt h else 0) =
        ∑ h' ∈ H'set, ∑ h ∈ Hset.filter (fun h => tail h = h'), ρ ^ wt h := by
      have h1 : (∑ h : W1, if h ∈ H then ρ ^ wt h else 0) = ∑ h ∈ Hset, ρ ^ wt h := by
        rw [Finset.sum_filter]
      rw [h1]
      exact sum_fib Hset H'set tail
        (fun h hh => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Submodule.mem_map_of_mem (Finset.mem_filter.mp hh).2⟩) _
    have hwt_succ : ∀ h : W1, wt h = wt (tail h) + (if h 0 ≠ 0 then 1 else 0) := by
      intro h
      unfold wt
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      rw [add_comm]
      rfl
    have hfiber_le : ∀ h' ∈ H'set,
        (∑ h ∈ Hset.filter (fun h => tail h = h'), ρ ^ wt h) ≤
          (Vset.card : ℝ) * (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * ρ ^ wt h' := by
      intro h' hh'
      have hh'm : h' ∈ H' := (Finset.mem_filter.mp hh').2
      obtain ⟨h0, hh0, rfl⟩ := Submodule.mem_map.mp hh'm
      let toV : W1 → (Fin a → F) := fun h => h 0 - h0 0
      have hsum_v : (∑ h ∈ Hset.filter (fun h => tail h = tail h0), ρ ^ wt h) =
          ρ ^ wt (tail h0) * ∑ v ∈ Vset, (if h0 0 + v ≠ 0 then ρ else 1) := by
        have hstep : ∀ h ∈ Hset.filter (fun h => tail h = tail h0),
            ρ ^ wt h = ρ ^ wt (tail h0) * (if h0 0 + toV h ≠ 0 then ρ else 1) := by
          intro h hh
          have htail := (Finset.mem_filter.mp hh).2
          rw [hwt_succ h, htail, pow_add]
          have hh0v : h0 0 + toV h = h 0 := by simp [toV]
          rw [hh0v]
          split_ifs <;> simp
        rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
        congr 1
        refine Finset.sum_bij (fun h _ => toV h) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro h hh
          have hhm := (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).2
          have htail := (Finset.mem_filter.mp hh).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hk : h - h0 ∈ K := ⟨H.sub_mem hhm hh0, by simp [LinearMap.mem_ker, tail.map_sub, htail]⟩
          exact ⟨h - h0, hk, rfl⟩
        · intro h1 hh1 h2 hh2 heq
          have htail1 := (Finset.mem_filter.mp hh1).2
          have htail2 := (Finset.mem_filter.mp hh2).2
          ext i j
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · have h0eq : h1 0 = h2 0 := sub_left_injective (show h1 0 - h0 0 = h2 0 - h0 0 from heq)
            exact congrFun h0eq j
          · have : tail h1 i' = tail h2 i' := congrFun (htail1.trans htail2.symm) i'
            exact congrFun this j
        · intro v hv
          obtain ⟨k, hk, hkv⟩ := Submodule.mem_map.mp (Finset.mem_filter.mp hv).2
          refine ⟨h0 + k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, H.add_mem hh0 hk.1⟩, ?_⟩, ?_⟩
          · simp [tail.map_add, show tail k = 0 from hk.2]
          · dsimp [toV, head] at hkv ⊢
            rw [← hkv, Pi.add_apply, add_sub_cancel_left]
      rw [hsum_v]
      have hV_bound : (∑ v ∈ Vset, (if h0 0 + v ≠ 0 then ρ else 1)) ≤
          (Vset.card : ℝ) * (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) := by
        have h2t : (2 : ℝ) ^ (-(t : ℝ)) = 1 / (Vset.card : ℝ) := by
          rw [Real.rpow_neg (by norm_num), ← hVcard_pow, one_div]
        rw [h2t, mul_add, mul_one_div, mul_div_cancel₀ _ hVcard_pos.ne']
        by_cases hmem : h0 0 ∈ V
        · have huniq : Vset.filter (fun v => h0 0 + v = 0) = {h0 0} := by
            ext v
            simp only [Vset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro ⟨_, hv0⟩
              have : v = -h0 0 := eq_neg_of_add_eq_zero_right hv0
              rwa [zmod2_neg_eq] at this
            · rintro rfl
              refine ⟨hmem, ?_⟩
              have : h0 0 + h0 0 = 0 := by
                have h2 : (2 : F) = 0 := by decide
                calc h0 0 + h0 0 = (2 : F) • h0 0 := (two_smul F (h0 0)).symm
                  _ = 0 := by rw [h2, zero_smul]
              exact this
          have hsplit : ∑ v ∈ Vset, (if h0 0 + v ≠ 0 then ρ else 1) =
              ∑ v ∈ Vset, (ρ + if h0 0 + v = 0 then (1 - ρ) else 0) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            by_cases hv : h0 0 + v = 0 <;> simp [hv]
          rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_filter, huniq,
            Finset.sum_singleton]
        · have hne : ∀ v ∈ Vset, h0 0 + v ≠ 0 := by
            intro v hv hzero
            have hv_mem : v ∈ V := (Finset.mem_filter.mp hv).2
            have heq : h0 0 = v := by
              have : h0 0 = -v := eq_neg_of_add_eq_zero_left hzero
              rwa [zmod2_neg_eq] at this
            exact hmem (heq ▸ hv_mem)
          have hsum_all : ∑ v ∈ Vset, (if h0 0 + v ≠ 0 then ρ else 1) = (Vset.card : ℝ) * ρ := by
            have hcon : ∑ v ∈ Vset, (if h0 0 + v ≠ 0 then ρ else 1) = ∑ _ ∈ Vset, ρ :=
              Finset.sum_congr rfl (fun v hv => if_pos (hne v hv))
            rw [hcon, Finset.sum_const, nsmul_eq_mul]
          rw [hsum_all]
          linarith
      have hpow_nn : 0 ≤ ρ ^ wt (tail h0) := pow_nonneg hρ_pos.le _
      nlinarith
    have hphi_step : Phi a (m + 1) H ≤ (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * Phi a m H' := by
      unfold Phi
      rw [hsum_split, hHcard]
      have hsum_le : (∑ h' ∈ H'set, ∑ h ∈ Hset.filter (fun h => tail h = h'), ρ ^ wt h) ≤
          ∑ h' ∈ H'set, (Vset.card : ℝ) * (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * ρ ^ wt h' :=
        Finset.sum_le_sum (fun h' hh' => hfiber_le h' hh')
      rw [← Finset.mul_sum] at hsum_le
      have hH'sum : (∑ h' ∈ H'set, ρ ^ wt h') =
          ∑ h' : W0, if h' ∈ H' then ρ ^ wt h' else 0 := by
        rw [← Finset.sum_filter]
      rw [hH'sum] at hsum_le
      have hdiv : (∑ h' ∈ H'set, ∑ h ∈ Hset.filter (fun h => tail h = h'), ρ ^ wt h) /
            ((H'set.card : ℝ) * (Vset.card : ℝ)) ≤
          ((Vset.card : ℝ) * (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) *
            ∑ h' : W0, if h' ∈ H' then ρ ^ wt h' else 0) / ((H'set.card : ℝ) * (Vset.card : ℝ)) :=
        div_le_div_of_nonneg_right hsum_le (mul_nonneg hH'card_pos.le hVcard_pos.le)
      have hid : ((Vset.card : ℝ) * (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) *
            ∑ h' : W0, if h' ∈ H' then ρ ^ wt h' else 0) / ((H'set.card : ℝ) * (Vset.card : ℝ)) =
          (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) *
            ((∑ h' : W0, if h' ∈ H' then ρ ^ wt h' else 0) / (H'set.card : ℝ)) := by
        field_simp [hVcard_pos.ne', hH'card_pos.ne']
      rw [hid] at hdiv
      exact hdiv
    have hloc := local_factor_bound a t ha ht_le
    have hih := ih H'
    have hloc_nn : 0 ≤ ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ)) := by
      have : 0 ≤ (2 : ℝ) ^ (-(t : ℝ)) := (Real.rpow_pos_of_pos (by norm_num) _).le
      nlinarith
    have hphi_nn : 0 ≤ Phi a m H' := by
      unfold Phi
      refine div_nonneg (Finset.sum_nonneg fun h' _ => ?_) (Nat.cast_nonneg _)
      split_ifs
      · exact pow_nonneg hρ_pos.le _
      · exact le_rfl
    have hphi_pos : 0 < Phi a m H' := by
      unfold Phi
      have h0mem : (0 : W0) ∈ H' := H'.zero_mem
      have hsum_pos : 0 < ∑ h' : W0, if h' ∈ H' then ρ ^ wt h' else 0 := by
        refine Finset.sum_pos' (fun h' _ => ?_) ⟨0, Finset.mem_univ _, ?_⟩
        · split_ifs
          · exact pow_nonneg hρ_pos.le _
          · exact le_rfl
        · rw [if_pos h0mem]
          exact pow_pos hρ_pos _
      exact div_pos hsum_pos hH'card_pos
    have hmul_bound : (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * Phi a m H' ≤
        c ^ (2 * (t : ℝ) / (a : ℝ)) * c ^ (2 * (Module.finrank F H' : ℝ) / (a : ℝ)) :=
      mul_le_mul hloc hih.1 hphi_nn (Real.rpow_pos_of_pos hc_pos _).le
    have hpow_comb : c ^ (2 * (t : ℝ) / (a : ℝ)) * c ^ (2 * (Module.finrank F H' : ℝ) / (a : ℝ)) =
        c ^ (2 * (Module.finrank F H : ℝ) / (a : ℝ)) := by
      rw [← Real.rpow_add hc_pos]
      congr 1
      rw [hdim_H]
      push_cast
      ring
    have hle_final : Phi a (m + 1) H ≤ c ^ (2 * (Module.finrank F H : ℝ) / (a : ℝ)) :=
      hphi_step.trans (hmul_bound.trans_eq hpow_comb)
    refine ⟨hle_final, ?_⟩
    intro heq
    have hchain1 : Phi a (m + 1) H = (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * Phi a m H' := by
      linarith [hphi_step, hmul_bound, hpow_comb, heq]
    have hchain2 : (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * Phi a m H' =
        c ^ (2 * (t : ℝ) / (a : ℝ)) * c ^ (2 * (Module.finrank F H' : ℝ) / (a : ℝ)) := by
      linarith [hphi_step, hmul_bound, hpow_comb, heq]
    have hloc_eq : ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ)) = c ^ (2 * (t : ℝ) / (a : ℝ)) := by
      by_contra hne
      have hlt : ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ)) < c ^ (2 * (t : ℝ) / (a : ℝ)) :=
        lt_of_le_of_ne hloc hne
      have : (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * Phi a m H' <
          c ^ (2 * (t : ℝ) / (a : ℝ)) * c ^ (2 * (Module.finrank F H' : ℝ) / (a : ℝ)) := by
        calc (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * Phi a m H'
            < c ^ (2 * (t : ℝ) / (a : ℝ)) * Phi a m H' := mul_lt_mul_of_pos_right hlt hphi_pos
          _ ≤ c ^ (2 * (t : ℝ) / (a : ℝ)) * c ^ (2 * (Module.finrank F H' : ℝ) / (a : ℝ)) :=
              mul_le_mul_of_nonneg_left hih.1 (Real.rpow_pos_of_pos hc_pos _).le
      exact this.ne hchain2
    have hih_eq : Phi a m H' = c ^ (2 * (Module.finrank F H' : ℝ) / (a : ℝ)) := by
      have hloc_pos : 0 < ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ)) := by
        have : 0 < (2 : ℝ) ^ (-(t : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
        nlinarith
      rw [hloc_eq] at hchain2
      exact mul_left_cancel₀ (Real.rpow_pos_of_pos hc_pos _).ne' hchain2
    obtain ⟨free', hfree'_card, hfree'_iff⟩ := hih.2 hih_eq
    have hfiber_eq : ∀ h' ∈ H'set,
        (∑ h ∈ Hset.filter (fun h => tail h = h'), ρ ^ wt h) =
          (Vset.card : ℝ) * (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * ρ ^ wt h' := by
      intro h' hh'
      have hsum_eq_all : ∑ h'' ∈ H'set, ∑ h ∈ Hset.filter (fun h => tail h = h''), ρ ^ wt h =
          ∑ h'' ∈ H'set, (Vset.card : ℝ) * (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * ρ ^ wt h'' := by
        have h1 := hchain1
        unfold Phi at h1
        have hH'_card_eq : ∀ [DecidablePred (fun x : W0 => x ∈ H')],
            (Finset.univ.filter (fun h'' : W0 => h'' ∈ H')).card = H'set.card := by
          intro _
          congr 1
          ext x
          simp [H'set]
        rw [hsum_split, hHcard, hH'_card_eq] at h1
        have h2 : ∑ h'' ∈ H'set, (Vset.card : ℝ) * (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) * ρ ^ wt h'' =
            (Vset.card : ℝ) * (ρ + (1 - ρ) * (2 : ℝ) ^ (-(t : ℝ))) *
              ∑ h'' : W0, if h'' ∈ H' then ρ ^ wt h'' else 0 := by
          rw [← Finset.mul_sum, ← Finset.sum_filter]
        rw [h2]
        dsimp [ρ, q] at h1 ⊢
        field_simp [hH'card_pos.ne', hVcard_pos.ne'] at h1 ⊢
        linarith
      exact (Finset.sum_eq_sum_iff_of_le (fun h'' hh'' => hfiber_le h'' hh'')).mp hsum_eq_all h' hh'
    have h0_in_V : ∀ h ∈ H, h 0 ∈ V := by
      intro h hh
      by_contra hnot
      have htail_mem : tail h ∈ H'set := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Submodule.mem_map_of_mem hh⟩
      have hfeq := hfiber_eq (tail h) htail_mem
      have hsum_v : (∑ x ∈ Hset.filter (fun x => tail x = tail h), ρ ^ wt x) =
          ρ ^ wt (tail h) * ∑ v ∈ Vset, (if h 0 + v ≠ 0 then ρ else 1) := by
        let toV : W1 → (Fin a → F) := fun x => x 0 - h 0
        have hstep : ∀ x ∈ Hset.filter (fun x => tail x = tail h),
            ρ ^ wt x = ρ ^ wt (tail h) * (if h 0 + toV x ≠ 0 then ρ else 1) := by
          intro x hx
          have htail := (Finset.mem_filter.mp hx).2
          rw [hwt_succ x, htail, pow_add]
          have hh0v : h 0 + toV x = x 0 := by simp [toV]
          rw [hh0v]; split_ifs <;> simp
        rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
        congr 1
        refine Finset.sum_bij (fun x _ => toV x) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro x hx
          have hxm := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
          have hxtail := (Finset.mem_filter.mp hx).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          exact ⟨x - h, ⟨H.sub_mem hxm hh, by simp [LinearMap.mem_ker, tail.map_sub, hxtail]⟩, rfl⟩
        · intro x1 hx1 x2 hx2 heq
          have ht1 := (Finset.mem_filter.mp hx1).2
          have ht2 := (Finset.mem_filter.mp hx2).2
          ext i j
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · exact congrFun (sub_left_injective (show x1 0 - h 0 = x2 0 - h 0 from heq)) j
          · exact congrFun (congrFun (ht1.trans ht2.symm) i') j
        · intro v hv
          obtain ⟨k, hk, hkv⟩ := Submodule.mem_map.mp (Finset.mem_filter.mp hv).2
          refine ⟨h + k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, H.add_mem hh hk.1⟩, ?_⟩, ?_⟩
          · simp [tail.map_add, show tail k = 0 from hk.2]
          · dsimp [toV, head] at hkv ⊢
            rw [← hkv, Pi.add_apply, add_sub_cancel_left]
      have hne : ∀ v ∈ Vset, h 0 + v ≠ 0 := by
        intro v hv hzero
        have hv_mem : v ∈ V := (Finset.mem_filter.mp hv).2
        have heq : h 0 = v := by
          have : h 0 = -v := eq_neg_of_add_eq_zero_left hzero
          rwa [zmod2_neg_eq] at this
        exact hnot (heq ▸ hv_mem)
      have hsum_all : ∑ v ∈ Vset, (if h 0 + v ≠ 0 then ρ else 1) = (Vset.card : ℝ) * ρ := by
        have hcon : ∑ v ∈ Vset, (if h 0 + v ≠ 0 then ρ else 1) = ∑ _ ∈ Vset, ρ :=
          Finset.sum_congr rfl (fun v hv => if_pos (hne v hv))
        rw [hcon, Finset.sum_const, nsmul_eq_mul]
      rw [hsum_v, hsum_all] at hfeq
      have h2t : (2 : ℝ) ^ (-(t : ℝ)) = 1 / (Vset.card : ℝ) := by
        rw [Real.rpow_neg (by norm_num), ← hVcard_pow, one_div]
      rw [h2t, mul_add, mul_one_div, mul_div_cancel₀ _ hVcard_pos.ne'] at hfeq
      have hpow_pos : 0 < ρ ^ wt (tail h) := pow_pos hρ_pos _
      have hlt : ρ ^ wt (tail h) * ((Vset.card : ℝ) * ρ) <
          ((Vset.card : ℝ) * ρ + (1 - ρ)) * ρ ^ wt (tail h) := by
        nlinarith
      exact hlt.ne hfeq
    rcases (local_factor_eq_iff a t ha ht_le).mp hloc_eq with ht0 | hta
    · have hVbot : V = ⊥ := (Submodule.finrank_eq_zero.mp ht0)
      have h0_zero : ∀ h ∈ H, h 0 = 0 := by
        intro h hh
        have := h0_in_V h hh
        rwa [hVbot, Submodule.mem_bot] at this
      let free : Finset (Fin (m + 1)) := free'.map (Fin.succEmb m)
      refine ⟨free, ?_, ?_⟩
      · rw [Finset.card_map, hfree'_card, hdim_H, show Module.finrank F V = 0 from ht0, add_zero]
      · intro h
        constructor
        · intro hh i hi
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · exact h0_zero h hh
          · have hi' : i' ∉ free' := fun hmem => hi (Finset.mem_map_of_mem (Fin.succEmb m) hmem)
            exact (hfree'_iff (tail h)).mp (Submodule.mem_map_of_mem hh) i' hi'
        · intro hcond
          have htail_in : tail h ∈ H' := by
            refine (hfree'_iff (tail h)).mpr fun i' hi' => ?_
            have hi : i'.succ ∉ free := by
              intro hmem
              obtain ⟨j, hj, hj_eq⟩ := Finset.mem_map.mp hmem
              have : j = i' := Fin.succ_injective _ hj_eq
              exact hi' (this ▸ hj)
            exact hcond i'.succ hi
          obtain ⟨h1, hh1, h1tail⟩ := Submodule.mem_map.mp htail_in
          have h0_eq : h = h1 := by
            ext i j
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
            · have h0not : (0 : Fin (m + 1)) ∉ free := by
                intro hmem
                obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hmem
                exact Fin.succ_ne_zero j hj
              rw [hcond 0 h0not, h0_zero h1 hh1]
            · exact congrFun (congrFun h1tail.symm i') j
          rwa [h0_eq]
    · have hVtop : V = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact hta)
      have h0_free : ∀ v : Fin a → F, Pi.single (0 : Fin (m + 1)) v ∈ H := by
        intro v
        have hv : v ∈ V := by rw [hVtop]; exact Submodule.mem_top
        obtain ⟨k, hk, hkv⟩ := Submodule.mem_map.mp hv
        have hk_eq : k = Pi.single (0 : Fin (m + 1)) v := by
          ext i j
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · dsimp [head] at hkv
            rw [hkv, Pi.single_eq_same]
          · have hker : tail k = 0 := hk.2
            have : k i'.succ j = 0 := congrFun (congrFun hker i') j
            rw [this, Pi.single_eq_of_ne (Fin.succ_ne_zero i'), Pi.zero_apply]
        exact hk_eq ▸ hk.1
      let free : Finset (Fin (m + 1)) := insert 0 (free'.map (Fin.succEmb m))
      have h0_notin : (0 : Fin (m + 1)) ∉ free'.map (Fin.succEmb m) := by
        intro hmem
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hmem
        exact Fin.succ_ne_zero j hj
      refine ⟨free, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem h0_notin, Finset.card_map, mul_add, mul_one,
          hfree'_card, hdim_H, show Module.finrank F V = a from hta, add_comm]
      · intro h
        constructor
        · intro hh i hi
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · exact absurd (Finset.mem_insert_self 0 _) hi
          · have hi' : i' ∉ free' := fun hmem =>
              hi (Finset.mem_insert_of_mem (Finset.mem_map_of_mem (Fin.succEmb m) hmem))
            exact (hfree'_iff (tail h)).mp (Submodule.mem_map_of_mem hh) i' hi'
        · intro hcond
          have htail_in : tail h ∈ H' := by
            refine (hfree'_iff (tail h)).mpr fun i' hi' => ?_
            have hi : i'.succ ∉ free := by
              intro hmem
              rcases Finset.mem_insert.mp hmem with h0z | hmap
              · exact Fin.succ_ne_zero i' h0z
              · obtain ⟨j, hj, hj_eq⟩ := Finset.mem_map.mp hmap
                exact hi' (Fin.succ_injective _ hj_eq ▸ hj)
            exact hcond i'.succ hi
          obtain ⟨h1, hh1, h1tail⟩ := Submodule.mem_map.mp htail_in
          have hdiff : h - h1 = Pi.single (0 : Fin (m + 1)) (h 0 - h1 0) := by
            ext i j
            rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
            · rw [Pi.sub_apply, Pi.single_eq_same]
            · have heq : tail h1 i' = tail h i' := congrFun h1tail i'
              have hj : tail h1 i' j = tail h i' j := congrFun heq j
              change h1 i'.succ j = h i'.succ j at hj
              rw [Pi.sub_apply, Pi.sub_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i'), Pi.zero_apply,
                hj, sub_self]
          have hadd : h = h1 + Pi.single (0 : Fin (m + 1)) (h 0 - h1 0) := by
            rw [← hdiff]; abel
          rw [hadd]
          exact H.add_mem hh1 (h0_free (h 0 - h1 0))

lemma sgn_eq_bool (a b : Bool) : (if a = b then (2 : ℝ) else 0) - 1 = sgn a * sgn b := by
  cases a <;> cases b <;> norm_num

noncomputable def biasR {a m r : ℕ} (send : (Fin m → Fin a → ZMod 2) → Fin ((2 ^ a) ^ (m - r)))
    (left right : (Fin m → Fin a → ZMod 2) → Bool)
    (read : Fin ((2 ^ a) ^ (m - r)) → (Fin m → Fin a → ZMod 2) → Bool) : ℝ :=
  (∑ x : Fin m → Fin a → ZMod 2, ∑ y : Fin m → Fin a → ZMod 2,
    sgn (read (send x) y) * sgn (left x) * sgn (right y) * chi x y) / (((2 : ℝ) ^ a) ^ m) ^ 2

lemma bias_cast_eq {a m r : ℕ} (send : (Fin m → Fin a → ZMod 2) → Fin ((2 ^ a) ^ (m - r)))
    (left right : (Fin m → Fin a → ZMod 2) → Bool)
    (read : Fin ((2 ^ a) ^ (m - r)) → (Fin m → Fin a → ZMod 2) → Bool) :
    let W := Fin m → Fin a → ZMod 2
    let q : ℕ := 2 ^ a
    let correct := ((Finset.univ : Finset (W × W)).filter (fun z =>
      read (send z.1) z.2 = xor (xor (left z.1) (right z.2))
        (((Finset.univ : Finset (Fin m)).filter (fun i => z.1 i = z.2 i)).card % 2 == 1))).card
    ((2 * (correct : ℚ) / (((q : ℚ) ^ m) ^ 2) - 1 : ℚ) : ℝ) = biasR send left right read := by
  intro W q correct
  have hWcard : (Fintype.card (W × W) : ℝ) = (((2 : ℝ) ^ a) ^ m) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card]
    push_cast
    ring
  have hden0 : (((2 : ℝ) ^ a) ^ m) ^ 2 ≠ 0 := by positivity
  have hcast : ((2 * (correct : ℚ) / ((q : ℚ) ^ m) ^ 2 - 1 : ℚ) : ℝ) =
      (2 * (correct : ℝ) - (((2 : ℝ) ^ a) ^ m) ^ 2) / (((2 : ℝ) ^ a) ^ m) ^ 2 := by
    push_cast [q]
    field_simp [hden0]
  rw [hcast]
  unfold biasR
  congr 1
  rw [← hWcard]
  have hsum1 : (2 * (correct : ℝ) - (Fintype.card (W × W) : ℝ)) =
      ∑ z : W × W, ((if read (send z.1) z.2 = xor (xor (left z.1) (right z.2))
        (((Finset.univ.filter (fun i : Fin m => z.1 i = z.2 i)).card % 2) == 1) then (2 : ℝ) else 0) - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1
    dsimp [correct]
    rw [Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> norm_num
  rw [hsum1]
  have hterm : ∀ z : W × W,
      (if read (send z.1) z.2 = xor (xor (left z.1) (right z.2))
        (((Finset.univ.filter (fun i : Fin m => z.1 i = z.2 i)).card % 2) == 1) then (2 : ℝ) else 0) - 1 =
      sgn (read (send z.1) z.2) * sgn (left z.1) * sgn (right z.2) * chi z.1 z.2 := by
    intro z
    rw [sgn_eq_bool, sgn_xor, sgn_xor, chi_eq_sgn]
    ring
  simp_rw [hterm]
  exact Fintype.sum_prod_type _

lemma cell_bound {a m : ℕ} (ha : 3 ≤ a)
    (C : Finset (Fin m → Fin a → ZMod 2)) (x0 : Fin m → Fin a → ZMod 2) (hx0 : x0 ∈ C)
    (H : Submodule (ZMod 2) (Fin m → Fin a → ZMod 2))
    (hC : ∀ y : Fin m → Fin a → ZMod 2, y ∈ C ↔ y - x0 ∈ H)
    (left right read_l : (Fin m → Fin a → ZMod 2) → Bool) :
    let W := Fin m → Fin a → ZMod 2
    let q : ℝ := (2 : ℝ) ^ a
    let c : ℝ := 1 - 2 / q
    let B := ∑ x ∈ C, ∑ y : W, sgn (read_l y) * sgn (left x) * sgn (right y) * chi x y
    |B| ≤ q ^ m * (C.card : ℝ) * c ^ ((Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) ∧
    (B = q ^ m * (C.card : ℝ) * c ^ ((Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) →
      Phi a m H = c ^ (2 * (Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) ∧
      ∀ u ∈ C, left u = left x0) := by
  intro W q c B
  have hq8 : (8 : ℝ) ≤ q := by
    have hpow : (8 : ℕ) ≤ 2 ^ a := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    calc (8 : ℝ) = ((8 : ℕ) : ℝ) := by norm_num
      _ ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast hpow
      _ = q := by push_cast [q]; rfl
  have hq0 : 0 < q := by linarith
  have hc_pos : 0 < c := by
    change 0 < 1 - 2 / q
    rw [sub_pos, div_lt_one hq0]
    linarith
  let ρ : ℝ := 1 - 4 / q
  have hρ_pos : 0 < ρ := by
    change 0 < 1 - 4 / q
    rw [sub_pos, div_lt_one hq0]
    linarith
  letI : DecidablePred (· ∈ H) := Classical.decPred _
  let Hset := Finset.univ.filter (fun h : W => h ∈ H)
  have hC_card : (C.card : ℝ) = (Hset.card : ℝ) := by
    have hbij : C.card = Hset.card := by
      refine Finset.card_bij (fun y _ => y - x0) ?_ ?_ ?_
      · intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hC y).mp hy⟩
      · intro y1 _ y2 _ heq
        exact sub_left_injective heq
      · intro h hh
        refine ⟨h + x0, (hC (h + x0)).mpr (by simpa using (Finset.mem_filter.mp hh).2), by simp⟩
    exact_mod_cast hbij
  have hC_pos : (0 : ℝ) < C.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x0, hx0⟩
  let S : W → ℝ := fun y => ∑ x ∈ C, sgn (left x) * chi x y
  have hB_eq : B = ∑ y : W, (sgn (read_l y) * sgn (right y)) * S y := by
    dsimp [B, S]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hB_abs : |B| ≤ ∑ y : W, (1 : ℝ) * |S y| := by
    rw [hB_eq]
    calc |∑ y : W, (sgn (read_l y) * sgn (right y)) * S y|
        ≤ ∑ y : W, |(sgn (read_l y) * sgn (right y)) * S y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y : W, (1 : ℝ) * |S y| := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [abs_mul, abs_mul, abs_sgn, abs_sgn, mul_one, one_mul]
  have hCS : (∑ y : W, (1 : ℝ) * |S y|) ^ 2 ≤ (q ^ m) * ∑ y : W, (S y) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : W => (1 : ℝ)) (fun y : W => |S y|)
    have h1 : ∑ _ : W, (1 : ℝ) ^ 2 = q ^ m := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin, ZMod.card, nsmul_eq_mul]
      push_cast [q]
      ring
    have h2 : ∑ y : W, |S y| ^ 2 = ∑ y : W, (S y) ^ 2 := by
      refine Finset.sum_congr rfl fun y _ => sq_abs _
    rwa [h1, h2] at h
  have hS_sq : ∑ y : W, (S y) ^ 2 =
      q ^ m * ∑ x ∈ C, ∑ x' ∈ C, sgn (left x) * sgn (left x') * ρ ^ wt (x - x') := by
    have h1 : ∀ y : W, (S y) ^ 2 = ∑ x ∈ C, ∑ x' ∈ C, (sgn (left x) * sgn (left x')) * (chi x y * chi x' y) := by
      intro y
      dsimp [S]
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x' _ => ?_
      ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : (∑ x ∈ C, ∑ y : W, ∑ x' ∈ C, (sgn (left x) * sgn (left x')) * (chi x y * chi x' y)) =
        ∑ x ∈ C, ∑ x' ∈ C, (sgn (left x) * sgn (left x')) * ∑ y : W, (chi x y * chi x' y) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [← Finset.mul_sum]
    rw [h2]
    have h3 : ∀ x ∈ C, ∀ x' ∈ C,
        (sgn (left x) * sgn (left x')) * (∑ y : W, chi x y * chi x' y) =
          q ^ m * (sgn (left x) * sgn (left x') * ρ ^ wt (x - x')) := by
      intro x _ x' _
      rw [chi_inner x x']
      change (sgn (left x) * sgn (left x')) * (q ^ m * ρ ^ wt (x - x')) = _
      ring
    have h4 : (∑ x ∈ C, ∑ x' ∈ C, (sgn (left x) * sgn (left x')) * ∑ y : W, (chi x y * chi x' y)) =
        ∑ x ∈ C, ∑ x' ∈ C, q ^ m * (sgn (left x) * sgn (left x') * ρ ^ wt (x - x')) := by
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun x' hx' => h3 x hx x' hx'
    rw [h4]
    simp_rw [← Finset.mul_sum]
  have hterm_le : ∀ x x' : W, sgn (left x) * sgn (left x') * ρ ^ wt (x - x') ≤ ρ ^ wt (x - x') := by
    intro x x'
    have hs : sgn (left x) * sgn (left x') ≤ 1 := by
      rw [← sgn_xor]
      exact sgn_le_one _
    have hp : 0 ≤ ρ ^ wt (x - x') := pow_nonneg hρ_pos.le _
    nlinarith
  have hinner_le : (∑ x ∈ C, ∑ x' ∈ C, sgn (left x) * sgn (left x') * ρ ^ wt (x - x')) ≤
      ∑ x ∈ C, ∑ x' ∈ C, ρ ^ wt (x - x') :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => hterm_le x x'
  have hsum_phi : (∑ x ∈ C, ∑ x' ∈ C, ρ ^ wt (x - x')) = (C.card : ℝ) ^ 2 * Phi a m H := by
    have hfix : ∀ x ∈ C, (∑ x' ∈ C, ρ ^ wt (x - x')) = ∑ h ∈ Hset, ρ ^ wt h := by
      intro x hx
      refine Finset.sum_bij (fun x' _ => x' - x) ?_ ?_ ?_ ?_
      · intro x' hx'
        have hx0' : x' - x0 ∈ H := (hC x').mp hx'
        have hx0x : x - x0 ∈ H := (hC x).mp hx
        have hsub : x' - x = (x' - x0) - (x - x0) := by abel
        rw [hsub]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, H.sub_mem hx0' hx0x⟩
      · intro y1 _ y2 _ heq
        exact sub_left_injective heq
      · intro h hh
        have hhH : h ∈ H := (Finset.mem_filter.mp hh).2
        have hxH : x - x0 ∈ H := (hC x).mp hx
        have hx' : x + h ∈ C := (hC (x + h)).mpr (by
          have : x + h - x0 = (x - x0) + h := by abel
          rw [this]
          exact H.add_mem hxH hhH)
        exact ⟨x + h, hx', by simp⟩
      · intro x' _
        have hneg : x - x' = -(x' - x) := by abel
        rw [hneg, zmod2_neg_eq]
    rw [Finset.sum_congr rfl hfix, Finset.sum_const, nsmul_eq_mul]
    have hHsum : (∑ h ∈ Hset, ρ ^ wt h) = (C.card : ℝ) * Phi a m H := by
      unfold Phi
      rw [← Finset.sum_filter, hC_card]
      have hHpos : (0 : ℝ) < Hset.card := by linarith [hC_card, hC_pos]
      change (∑ h ∈ Hset, ρ ^ wt h) = (Hset.card : ℝ) * ((∑ h ∈ Hset, ρ ^ wt h) / (Hset.card : ℝ))
      field_simp [hHpos.ne']
    rw [hHsum]
    ring
  have hPhi := Phi_ind a ha m H
  have hPhi_nn : 0 ≤ Phi a m H := by
    unfold Phi
    refine div_nonneg (Finset.sum_nonneg fun h _ => ?_) (Nat.cast_nonneg _)
    split_ifs
    · exact pow_nonneg hρ_pos.le _
    · exact le_rfl
  let target := q ^ m * (C.card : ℝ) * c ^ ((Module.finrank (ZMod 2) H : ℝ) / (a : ℝ))
  have htarget_nn : 0 ≤ target := by positivity
  have hB_sq_le : |B| ^ 2 ≤ (q ^ m * (C.card : ℝ)) ^ 2 * Phi a m H := by
    calc |B| ^ 2 ≤ (∑ y : W, (1 : ℝ) * |S y|) ^ 2 := sq_le_sq' (by linarith [abs_nonneg B]) hB_abs
      _ ≤ q ^ m * ∑ y : W, (S y) ^ 2 := hCS
      _ = (q ^ m) ^ 2 * ∑ x ∈ C, ∑ x' ∈ C, sgn (left x) * sgn (left x') * ρ ^ wt (x - x') := by
          rw [hS_sq]; ring
      _ ≤ (q ^ m) ^ 2 * ∑ x ∈ C, ∑ x' ∈ C, ρ ^ wt (x - x') :=
          mul_le_mul_of_nonneg_left hinner_le (sq_nonneg _)
      _ = (q ^ m * (C.card : ℝ)) ^ 2 * Phi a m H := by
          rw [hsum_phi]; ring
  have htarget_sq : target ^ 2 = (q ^ m * (C.card : ℝ)) ^ 2 * c ^ (2 * (Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) := by
    have hpow : (c ^ ((Module.finrank (ZMod 2) H : ℝ) / (a : ℝ))) ^ 2 =
        c ^ (2 * (Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc_pos.le]
      congr 1
      ring
    dsimp [target]
    rw [mul_pow, hpow]
  have hB_sq_target : |B| ^ 2 ≤ target ^ 2 := by
    calc |B| ^ 2 ≤ (q ^ m * (C.card : ℝ)) ^ 2 * Phi a m H := hB_sq_le
      _ ≤ (q ^ m * (C.card : ℝ)) ^ 2 * c ^ (2 * (Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) :=
          mul_le_mul_of_nonneg_left hPhi.1 (sq_nonneg _)
      _ = target ^ 2 := htarget_sq.symm
  have hB_le : |B| ≤ target := by
    nlinarith [abs_nonneg B, htarget_nn]
  refine ⟨hB_le, ?_⟩
  intro hBeq
  have hsq_eq : |B| ^ 2 = target ^ 2 := by rw [hBeq, abs_of_nonneg htarget_nn]
  have hqmC_pos : 0 < (q ^ m * (C.card : ℝ)) ^ 2 := sq_pos_of_pos (mul_pos (pow_pos hq0 m) hC_pos)
  have hPhi_eq : Phi a m H = c ^ (2 * (Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) := by
    have hle_t : (q ^ m * (C.card : ℝ)) ^ 2 * Phi a m H ≤ target ^ 2 := by
      rw [htarget_sq]
      exact mul_le_mul_of_nonneg_left hPhi.1 (sq_nonneg _)
    have h1 : (q ^ m * (C.card : ℝ)) ^ 2 * Phi a m H =
        (q ^ m * (C.card : ℝ)) ^ 2 * c ^ (2 * (Module.finrank (ZMod 2) H : ℝ) / (a : ℝ)) := by
      linarith [hB_sq_le, htarget_sq, hsq_eq, hle_t]
    exact mul_left_cancel₀ hqmC_pos.ne' h1
  refine ⟨hPhi_eq, ?_⟩
  have hsum_eq : (∑ x ∈ C, ∑ x' ∈ C, sgn (left x) * sgn (left x') * ρ ^ wt (x - x')) =
      ∑ x ∈ C, ∑ x' ∈ C, ρ ^ wt (x - x') := by
    have hq2pos : 0 < (q ^ m) ^ 2 := sq_pos_of_pos (pow_pos hq0 m)
    have h1 : (q ^ m) ^ 2 * ∑ x ∈ C, ∑ x' ∈ C, sgn (left x) * sgn (left x') * ρ ^ wt (x - x') =
        (q ^ m) ^ 2 * ∑ x ∈ C, ∑ x' ∈ C, ρ ^ wt (x - x') := by
      have hA : |B| ^ 2 ≤ (q ^ m) ^ 2 * ∑ x ∈ C, ∑ x' ∈ C, sgn (left x) * sgn (left x') * ρ ^ wt (x - x') := by
        calc |B| ^ 2 ≤ (∑ y : W, (1 : ℝ) * |S y|) ^ 2 := sq_le_sq' (by linarith [abs_nonneg B]) hB_abs
          _ ≤ q ^ m * ∑ y : W, (S y) ^ 2 := hCS
          _ = _ := by rw [hS_sq]; ring
      have hB' : (q ^ m) ^ 2 * ∑ x ∈ C, ∑ x' ∈ C, ρ ^ wt (x - x') = target ^ 2 := by
        rw [hsum_phi, hPhi_eq, htarget_sq]
        ring
      linarith [hA, hB', hsq_eq, mul_le_mul_of_nonneg_left hinner_le hq2pos.le]
    exact mul_left_cancel₀ hq2pos.ne' h1
  intro u hu
  have hout := (Finset.sum_eq_sum_iff_of_le (fun x _ => Finset.sum_le_sum fun x' _ => hterm_le x x')).mp hsum_eq u hu
  have hin := (Finset.sum_eq_sum_iff_of_le (fun x' _ => hterm_le u x')).mp hout x0 hx0
  have hρw : 0 < ρ ^ wt (u - x0) := pow_pos hρ_pos _
  have hsgn_eq : sgn (left u) * sgn (left x0) = 1 := by
    calc sgn (left u) * sgn (left x0)
        = (sgn (left u) * sgn (left x0) * ρ ^ wt (u - x0)) / ρ ^ wt (u - x0) := by
            field_simp [hρw.ne']
      _ = ρ ^ wt (u - x0) / ρ ^ wt (u - x0) := by rw [hin]
      _ = 1 := div_self hρw.ne'
  cases hlu : left u <;> cases hlx : left x0 <;> simp_all [sgn] <;> norm_num at hsgn_eq

lemma bias_abs_le_and_eq {a m r : ℕ} (ha : 3 ≤ a) (hr : r ≤ m)
    (send : (Fin m → Fin a → ZMod 2) → Fin ((2 ^ a) ^ (m - r)))
    (haff : ∀ x : Fin m → Fin a → ZMod 2,
      ∃ H : Submodule (ZMod 2) (Fin m → Fin a → ZMod 2),
        ∀ y : Fin m → Fin a → ZMod 2, send y = send x ↔ y - x ∈ H)
    (left right : (Fin m → Fin a → ZMod 2) → Bool)
    (read : Fin ((2 ^ a) ^ (m - r)) → (Fin m → Fin a → ZMod 2) → Bool) :
    let q : ℝ := (2 : ℝ) ^ a
    let c : ℝ := 1 - 2 / q
    |biasR send left right read| ≤ c ^ r ∧
    (biasR send left right read = c ^ r →
      ∀ label : Fin ((2 ^ a) ^ (m - r)),
        ∃ (center : Fin m → Fin a → ZMod 2) (free : Finset (Fin m)),
          free.card = r ∧
          (∀ u : Fin m → Fin a → ZMod 2, send u = label ↔ ∀ i : Fin m, i ∉ free → u i = center i) ∧
          (∀ u : Fin m → Fin a → ZMod 2, send u = label → left u = left center)) := by
  intro q c
  let F := ZMod 2
  let W := Fin m → Fin a → F
  let N := (2 ^ a) ^ (m - r)
  let M := Fin N
  have hNpos : 0 < N := pow_pos (pow_pos (by norm_num) a) (m - r)
  have hq8 : (8 : ℝ) ≤ q := by
    have hpow : (8 : ℕ) ≤ 2 ^ a := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    calc (8 : ℝ) = ((8 : ℕ) : ℝ) := by norm_num
      _ ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast hpow
      _ = q := by push_cast [q]; rfl
  have hq0 : 0 < q := by linarith
  have hc_pos : 0 < c := by
    change 0 < 1 - 2 / q
    rw [sub_pos, div_lt_one hq0]
    linarith
  have hc_ge34 : (3 : ℝ) / 4 ≤ c := by
    change 3 / 4 ≤ 1 - 2 / q
    have : 2 / q ≤ 2 / 8 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq8
    linarith
  have hc_lt1 : c < 1 := by
    change 1 - 2 / q < 1
    linarith [div_pos (by norm_num : (0 : ℝ) < 2) hq0]
  have ha_pos : (0 : ℝ) < a := by positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogc_neg : Real.log c < 0 := Real.log_neg hc_pos hc_lt1
  let β : ℝ := -Real.log c / ((a : ℝ) * Real.log 2)
  let p : ℝ := 1 - β
  have hβ0 : 0 < β := div_pos (neg_pos.mpr hlogc_neg) (mul_pos ha_pos hlog2_pos)
  have hβ1 : β < 1 := by
    dsimp [β]
    rw [div_lt_one (mul_pos ha_pos hlog2_pos)]
    have hexp_lt : Real.exp (-(a : ℝ) * Real.log 2) < c := by
      have h1 : Real.exp (-(a : ℝ) * Real.log 2) = 1 / q := by
        rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), one_div]
      rw [h1]
      have h2 : 1 / q ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hq8
      linarith
    have hlog := Real.log_lt_log (Real.exp_pos _) hexp_lt
    rw [Real.log_exp] at hlog
    linarith
  have hp0 : 0 < p := sub_pos.mpr hβ1
  have hp1 : p < 1 := sub_lt_self 1 hβ0
  have hc_rpow : c = (2 : ℝ) ^ (-(a : ℝ) * β) := by
    have h1 : Real.log c = Real.log ((2 : ℝ) ^ (-(a : ℝ) * β)) := by
      rw [Real.log_rpow (by norm_num)]
      dsimp [β]
      field_simp [ha_pos.ne', hlog2_pos.ne']
    exact Real.log_injOn_pos hc_pos (Real.rpow_pos_of_pos (by norm_num) _) h1
  let C : M → Finset W := fun ℓ => Finset.univ.filter (fun x : W => send x = ℓ)
  let B : M → ℝ := fun ℓ => ∑ x ∈ C ℓ, ∑ y : W, sgn (read ℓ y) * sgn (left x) * sgn (right y) * chi x y
  have hbias_sum : biasR send left right read = (∑ ℓ : M, B ℓ) / (q ^ m) ^ 2 := by
    unfold biasR
    congr 1
    have hfib : (∑ x : W, ∑ y : W, sgn (read (send x) y) * sgn (left x) * sgn (right y) * chi x y) =
        ∑ ℓ : M, ∑ x ∈ C ℓ, ∑ y : W, sgn (read (send x) y) * sgn (left x) * sgn (right y) * chi x y := by
      have h1 := sum_fib Finset.univ Finset.univ send (fun _ _ => Finset.mem_univ _)
        (fun x => ∑ y : W, sgn (read (send x) y) * sgn (left x) * sgn (right y) * chi x y)
      exact h1
    rw [hfib]
    refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun x hx => ?_
    have hxℓ : send x = ℓ := (Finset.mem_filter.mp hx).2
    simp_rw [hxℓ]
  let x : M → ℝ := fun ℓ => ((C ℓ).card : ℝ) / q ^ m
  have hx_nn : ∀ ℓ : M, 0 ≤ x ℓ := fun ℓ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0.le m)
  have hx_sum : ∑ ℓ : M, x ℓ = 1 := by
    dsimp [x]
    rw [← Finset.sum_div]
    have hcard_sum : ∑ ℓ : M, ((C ℓ).card : ℝ) = (Fintype.card W : ℝ) := by
      have h1 := sum_fib Finset.univ Finset.univ send (fun _ _ => Finset.mem_univ _) (fun _ : W => (1 : ℝ))
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
      exact h1.symm
    have hWcard : (Fintype.card W : ℝ) = q ^ m := by
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card]
      push_cast [q]; ring
    rw [hcard_sum, hWcard, div_self (pow_ne_zero m hq0.ne')]
  have hcell_id : ∀ (ℓ : M) (H : Submodule F W),
      (C ℓ).card = 2 ^ Module.finrank F H →
      q ^ m * ((C ℓ).card : ℝ) * c ^ ((Module.finrank F H : ℝ) / (a : ℝ)) =
        (q ^ m) ^ 2 * c ^ m * (x ℓ) ^ p := by
    intro ℓ H hcard_eq
    have hC_pos : 0 < ((C ℓ).card : ℝ) := by rw [hcard_eq]; positivity
    have hx_pow : x ℓ = (2 : ℝ) ^ ((Module.finrank F H : ℝ) - (a : ℝ) * (m : ℝ)) := by
      dsimp [x]; rw [hcard_eq]
      have h2am : q ^ m = (2 : ℝ) ^ ((a : ℝ) * (m : ℝ)) := by
        change ((2 : ℝ) ^ a) ^ m = _
        rw [← Real.rpow_natCast (2 : ℝ) a, ← Real.rpow_natCast _ m, ← Real.rpow_mul (by norm_num)]
      have h2d : ((2 ^ Module.finrank F H : ℕ) : ℝ) = (2 : ℝ) ^ (Module.finrank F H : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
      rw [h2am, h2d, Real.rpow_sub (by norm_num)]
    have hxpos : 0 < x ℓ := by rw [hx_pow]; exact Real.rpow_pos_of_pos (by norm_num) _
    have hlog_eq : Real.log ((C ℓ).card : ℝ) + ((Module.finrank F H : ℝ) / (a : ℝ)) * Real.log c =
        Real.log (q ^ m) + (m : ℝ) * Real.log c + p * Real.log (x ℓ) := by
      have hClog : Real.log ((C ℓ).card : ℝ) = (Module.finrank F H : ℝ) * Real.log 2 := by
        rw [hcard_eq, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      have hqlog : Real.log (q ^ m) = (m : ℝ) * (a : ℝ) * Real.log 2 := by
        change Real.log (((2 : ℝ) ^ a) ^ m) = _
        rw [Real.log_pow, Real.log_pow]; ring
      have hxlog : Real.log (x ℓ) = ((Module.finrank F H : ℝ) - (a : ℝ) * (m : ℝ)) * Real.log 2 := by
        rw [hx_pow, Real.log_rpow (by norm_num)]
      have hclog : Real.log c = -β * (a : ℝ) * Real.log 2 := by
        dsimp [β]; field_simp [ha_pos.ne', hlog2_pos.ne']
      rw [hClog, hqlog, hxlog, hclog]
      dsimp [p]; field_simp [ha_pos.ne']; ring
    have hprod_eq : ((C ℓ).card : ℝ) * c ^ ((Module.finrank F H : ℝ) / (a : ℝ)) =
        q ^ m * c ^ m * (x ℓ) ^ p := by
      have hLpos : 0 < ((C ℓ).card : ℝ) * c ^ ((Module.finrank F H : ℝ) / (a : ℝ)) :=
        mul_pos hC_pos (Real.rpow_pos_of_pos hc_pos _)
      have hRpos : 0 < q ^ m * c ^ m * (x ℓ) ^ p := by
        exact mul_pos (mul_pos (pow_pos hq0 m) (pow_pos hc_pos m)) (Real.rpow_pos_of_pos hxpos p)
      refine Real.log_injOn_pos hLpos hRpos ?_
      have hc_rpos : 0 < c ^ ((Module.finrank F H : ℝ) / (a : ℝ)) := Real.rpow_pos_of_pos hc_pos _
      have hxp_pos : 0 < (x ℓ) ^ p := Real.rpow_pos_of_pos hxpos p
      have h1 : Real.log (((C ℓ).card : ℝ) * c ^ ((Module.finrank F H : ℝ) / (a : ℝ))) =
          Real.log ((C ℓ).card : ℝ) + ((Module.finrank F H : ℝ) / (a : ℝ)) * Real.log c := by
        rw [Real.log_mul hC_pos.ne' hc_rpos.ne', Real.log_rpow hc_pos]
      have h2 : Real.log (q ^ m * c ^ m * (x ℓ) ^ p) =
          Real.log (q ^ m) + (m : ℝ) * Real.log c + p * Real.log (x ℓ) := by
        have hqm_c : q ^ m * c ^ m ≠ 0 := (mul_pos (pow_pos hq0 m) (pow_pos hc_pos m)).ne'
        have hqm0 : q ^ m ≠ 0 := (pow_pos hq0 m).ne'
        have hcm0 : c ^ m ≠ 0 := (pow_pos hc_pos m).ne'
        rw [Real.log_mul hqm_c hxp_pos.ne', Real.log_mul hqm0 hcm0, Real.log_pow, Real.log_pow,
          Real.log_pow, Real.log_rpow hxpos]
      change Real.log (((C ℓ).card : ℝ) * c ^ ((Module.finrank F H : ℝ) / (a : ℝ))) =
        Real.log (q ^ m * c ^ m * (x ℓ) ^ p)
      rw [h1, h2]
      exact hlog_eq
    calc q ^ m * ((C ℓ).card : ℝ) * c ^ ((Module.finrank F H : ℝ) / (a : ℝ))
        = q ^ m * (((C ℓ).card : ℝ) * c ^ ((Module.finrank F H : ℝ) / (a : ℝ))) := by ring
      _ = q ^ m * (q ^ m * c ^ m * (x ℓ) ^ p) := by rw [hprod_eq]
      _ = (q ^ m) ^ 2 * c ^ m * (x ℓ) ^ p := by ring
  have hcell : ∀ ℓ : M, |B ℓ| ≤ (q ^ m) ^ 2 * c ^ m * (x ℓ) ^ p := by
    intro ℓ
    by_cases hne : (C ℓ).Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      obtain ⟨H, hH⟩ := haff x0
      have hC_iff : ∀ y : W, y ∈ C ℓ ↔ y - x0 ∈ H := by
        intro y
        have h1 : send x0 = ℓ := (Finset.mem_filter.mp hx0).2
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, ← h1]
        exact hH y
      have hcb := (cell_bound ha (C ℓ) x0 hx0 H hC_iff left right (read ℓ)).1
      letI : DecidablePred (· ∈ H) := Classical.decPred _
      have hcard_eq : (C ℓ).card = 2 ^ Module.finrank F H := by
        have hbij : (C ℓ).card = (Finset.univ.filter (fun h : W => h ∈ H)).card := by
          refine Finset.card_bij (fun y _ => y - x0) ?_ ?_ ?_
          · intro y hy; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hC_iff y).mp hy⟩
          · intro y1 _ y2 _ heq; exact sub_left_injective heq
          · intro h hh; exact ⟨h + x0, (hC_iff (h + x0)).mpr (by simpa using (Finset.mem_filter.mp hh).2), by simp⟩
        rw [hbij, submodule_card_eq_pow H]
      exact hcb.trans_eq (hcell_id ℓ H hcard_eq)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hB0 : B ℓ = 0 := by simp [B, hne]
      have hx0 : x ℓ = 0 := by simp [x, hne]
      rw [hB0, abs_zero, hx0, Real.zero_rpow hp0.ne', mul_zero]
  have hpow_N : c ^ m * (N : ℝ) ^ (1 - p) = c ^ r := by
    have h1p : 1 - p = β := by dsimp [p]; ring
    rw [h1p]
    have hN_rpow : (N : ℝ) ^ β = c ^ (-((m - r : ℕ) : ℝ)) := by
      have hN_eq : (N : ℝ) = (2 : ℝ) ^ ((a : ℝ) * ((m - r : ℕ) : ℝ)) := by
        dsimp [N]
        push_cast
        rw [← Real.rpow_natCast (2 : ℝ) a, ← Real.rpow_natCast _ (m - r), ← Real.rpow_mul (by norm_num)]
      rw [hN_eq, ← Real.rpow_mul (by norm_num), hc_rpow, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [hN_rpow, ← Real.rpow_natCast c m, ← Real.rpow_add hc_pos]
    have hmr : (m : ℝ) + -((m - r : ℕ) : ℝ) = (r : ℝ) := by
      have : ((m - r : ℕ) : ℝ) = (m : ℝ) - (r : ℝ) := Nat.cast_sub hr
      linarith
    rw [hmr, Real.rpow_natCast]
  have hsum_bound : (∑ ℓ : M, |B ℓ|) ≤ (q ^ m) ^ 2 * c ^ r := by
    have h1 : (∑ ℓ : M, |B ℓ|) ≤ ∑ ℓ : M, (q ^ m) ^ 2 * c ^ m * (x ℓ) ^ p :=
      Finset.sum_le_sum fun ℓ _ => hcell ℓ
    rw [← Finset.mul_sum] at h1
    have h2 := sum_rpow_le N hNpos p hp0 hp1 x hx_nn hx_sum
    calc (∑ ℓ : M, |B ℓ|) ≤ (q ^ m) ^ 2 * c ^ m * ∑ ℓ : M, (x ℓ) ^ p := h1
      _ ≤ (q ^ m) ^ 2 * c ^ m * (N : ℝ) ^ (1 - p) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg _) (pow_nonneg hc_pos.le _))
      _ = (q ^ m) ^ 2 * (c ^ m * (N : ℝ) ^ (1 - p)) := by ring
      _ = (q ^ m) ^ 2 * c ^ r := by rw [hpow_N]
  have hden0 : (q ^ m) ^ 2 ≠ 0 := pow_ne_zero 2 (pow_ne_zero m hq0.ne')
  have hden_pos : 0 < (q ^ m) ^ 2 := sq_pos_of_pos (pow_pos hq0 m)
  have hbias_le : |biasR send left right read| ≤ c ^ r := by
    rw [hbias_sum, abs_div, abs_of_pos hden_pos, div_le_iff₀ hden_pos]
    calc |∑ ℓ : M, B ℓ| ≤ ∑ ℓ : M, |B ℓ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (q ^ m) ^ 2 * c ^ r := hsum_bound
      _ = c ^ r * (q ^ m) ^ 2 := by ring
  refine ⟨hbias_le, ?_⟩
  intro heq
  have hsum_B_eq : (∑ ℓ : M, B ℓ) = (q ^ m) ^ 2 * c ^ r := by
    rw [hbias_sum] at heq
    exact (div_eq_iff hden0).mp heq |>.trans (by ring)
  have hsum_abs_eq : (∑ ℓ : M, |B ℓ|) = (q ^ m) ^ 2 * c ^ r := by
    have h1 : (∑ ℓ : M, B ℓ) ≤ ∑ ℓ : M, |B ℓ| := Finset.sum_le_sum fun ℓ _ => le_abs_self _
    linarith [hsum_bound, hsum_B_eq]
  have hx_rpow_eq : ∑ ℓ : M, (x ℓ) ^ p = (N : ℝ) ^ (1 - p) := by
    have h1 : (∑ ℓ : M, |B ℓ|) ≤ (q ^ m) ^ 2 * c ^ m * ∑ ℓ : M, (x ℓ) ^ p := by
      have h : (∑ ℓ : M, |B ℓ|) ≤ ∑ ℓ : M, (q ^ m) ^ 2 * c ^ m * (x ℓ) ^ p :=
        Finset.sum_le_sum fun ℓ _ => hcell ℓ
      rwa [← Finset.mul_sum] at h
    have h2 : (q ^ m) ^ 2 * c ^ m * ∑ ℓ : M, (x ℓ) ^ p ≤ (q ^ m) ^ 2 * c ^ r := by
      calc (q ^ m) ^ 2 * c ^ m * ∑ ℓ : M, (x ℓ) ^ p
          ≤ (q ^ m) ^ 2 * c ^ m * (N : ℝ) ^ (1 - p) :=
            mul_le_mul_of_nonneg_left (sum_rpow_le N hNpos p hp0 hp1 x hx_nn hx_sum)
              (mul_nonneg (sq_nonneg _) (pow_nonneg hc_pos.le _))
        _ = (q ^ m) ^ 2 * c ^ r := by rw [← hpow_N]; ring
    have hmul_eq : (q ^ m) ^ 2 * c ^ m * ∑ ℓ : M, (x ℓ) ^ p = (q ^ m) ^ 2 * c ^ m * (N : ℝ) ^ (1 - p) := by
      have : (q ^ m) ^ 2 * c ^ m * (N : ℝ) ^ (1 - p) = (q ^ m) ^ 2 * c ^ r := by rw [← hpow_N]; ring
      linarith [h1, h2, hsum_abs_eq]
    exact mul_left_cancel₀ (mul_ne_zero hden0 (pow_ne_zero m hc_pos.ne')) hmul_eq
  have hx_val : ∀ ℓ : M, x ℓ = 1 / (N : ℝ) := (sum_rpow_eq_iff N hNpos p hp0 hp1 x hx_nn hx_sum).mp hx_rpow_eq
  have hB_eq_cell : ∀ ℓ : M, B ℓ = (q ^ m) ^ 2 * c ^ m * (x ℓ) ^ p := by
    have hsum_all : ∑ ℓ : M, B ℓ = ∑ ℓ : M, (q ^ m) ^ 2 * c ^ m * (x ℓ) ^ p := by
      rw [← Finset.mul_sum, hx_rpow_eq, hsum_B_eq]
      calc (q ^ m) ^ 2 * c ^ r = (q ^ m) ^ 2 * (c ^ m * (N : ℝ) ^ (1 - p)) := by rw [hpow_N]
        _ = (q ^ m) ^ 2 * c ^ m * (N : ℝ) ^ (1 - p) := by ring
    exact fun ℓ => (Finset.sum_eq_sum_iff_of_le (fun ℓ' _ => (le_abs_self (B ℓ')).trans (hcell ℓ'))).mp hsum_all ℓ (Finset.mem_univ ℓ)
  intro label
  have hx_pos_ℓ : 0 < x label := by
    rw [hx_val label]
    positivity
  have hC_pos_ℓ : 0 < (C label).card := by
    have : (0 : ℝ) < ((C label).card : ℝ) := by
      have hCeq : ((C label).card : ℝ) = x label * q ^ m := by
        dsimp [x]
        rw [div_mul_cancel₀ _ (pow_ne_zero m hq0.ne')]
      rw [hCeq]
      exact mul_pos hx_pos_ℓ (pow_pos hq0 m)
    exact_mod_cast this
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hC_pos_ℓ
  obtain ⟨H, hH⟩ := haff x0
  have hC_iff : ∀ y : W, y ∈ C label ↔ y - x0 ∈ H := by
    intro y
    have h1 : send x0 = label := (Finset.mem_filter.mp hx0).2
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, ← h1]
    exact hH y
  letI : DecidablePred (· ∈ H) := Classical.decPred _
  have hcard_eq : (C label).card = 2 ^ Module.finrank F H := by
    have hbij : (C label).card = (Finset.univ.filter (fun h : W => h ∈ H)).card := by
      refine Finset.card_bij (fun y _ => y - x0) ?_ ?_ ?_
      · intro y hy; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hC_iff y).mp hy⟩
      · intro y1 _ y2 _ heq; exact sub_left_injective heq
      · intro h hh; exact ⟨h + x0, (hC_iff (h + x0)).mpr (by simpa using (Finset.mem_filter.mp hh).2), by simp⟩
    rw [hbij, submodule_card_eq_pow H]
  have hdim_eq : Module.finrank F H = a * r := by
    have h1 : ((C label).card : ℝ) = (2 : ℝ) ^ (a * r) := by
      have h2 : x label * q ^ m = (2 : ℝ) ^ (a * r) := by
        rw [hx_val label]
        have hN_eq : (N : ℝ) = (2 : ℝ) ^ (a * (m - r)) := by
          dsimp [N]; push_cast; rw [← pow_mul]
        have hqm_eq : q ^ m = (2 : ℝ) ^ (a * m) := by
          dsimp [q]; rw [← pow_mul]
        rw [hN_eq, hqm_eq, one_div_mul_eq_div, div_eq_iff (by positivity), ← pow_add]
        congr 1
        have : a * (m - r) = a * m - a * r := Nat.mul_sub_left_distrib a m r
        have har : a * r ≤ a * m := Nat.mul_le_mul_left a hr
        omega
      have h3 : ((C label).card : ℝ) = x label * q ^ m := by
        dsimp [x]
        rw [div_mul_cancel₀ _ (pow_ne_zero m hq0.ne')]
      rw [h3, h2]
    have h1_nat : (C label).card = 2 ^ (a * r) := by exact_mod_cast h1
    rw [hcard_eq] at h1_nat
    exact Nat.pow_right_injective (by norm_num) h1_nat
  have hB_target : B label = q ^ m * ((C label).card : ℝ) * c ^ ((Module.finrank F H : ℝ) / (a : ℝ)) :=
    (hB_eq_cell label).trans (hcell_id label H hcard_eq).symm
  have hcb_eq := (cell_bound ha (C label) x0 hx0 H hC_iff left right (read label)).2 hB_target
  obtain ⟨free, hfree_mul, hfree_iff⟩ := (Phi_ind a ha m H).2 hcb_eq.1
  have hfree_card : free.card = r := by
    have : a * free.card = a * r := hfree_mul.trans hdim_eq
    exact Nat.mul_left_cancel (by omega) this
  refine ⟨x0, free, hfree_card, ?_, ?_⟩
  · intro u
    rw [show send u = label ↔ u ∈ C label from by simp [C], hC_iff u, hfree_iff (u - x0)]
    constructor
    · intro h i hi
      exact sub_eq_zero.mp (h i hi)
    · intro h i hi
      exact sub_eq_zero.mpr (h i hi)
  · intro u hu
    exact hcb_eq.2 u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)

lemma cylinders_attains {a m r : ℕ} (ha : 3 ≤ a) (hr : r ≤ m)
    (send : (Fin m → Fin a → ZMod 2) → Fin ((2 ^ a) ^ (m - r)))
    (left right : (Fin m → Fin a → ZMod 2) → Bool)
    (hcyl : ∀ label : Fin ((2 ^ a) ^ (m - r)),
      ∃ (center : Fin m → Fin a → ZMod 2) (free : Finset (Fin m)),
        free.card = r ∧
        (∀ u : Fin m → Fin a → ZMod 2, send u = label ↔ ∀ i : Fin m, i ∉ free → u i = center i) ∧
        (∀ u : Fin m → Fin a → ZMod 2, send u = label → left u = left center)) :
    ∃ read : Fin ((2 ^ a) ^ (m - r)) → (Fin m → Fin a → ZMod 2) → Bool,
      biasR send left right read = (1 - 2 / (2 : ℝ) ^ a) ^ r := by
  let W := Fin m → Fin a → ZMod 2
  let q : ℝ := (2 : ℝ) ^ a
  let M := Fin ((2 ^ a) ^ (m - r))
  let center : M → W := fun ℓ => Classical.choose (hcyl ℓ)
  let free : M → Finset (Fin m) := fun ℓ => Classical.choose (Classical.choose_spec (hcyl ℓ))
  have hspec : ∀ ℓ : M, (free ℓ).card = r ∧
      (∀ u : W, send u = ℓ ↔ ∀ i : Fin m, i ∉ free ℓ → u i = center ℓ i) ∧
      (∀ u : W, send u = ℓ → left u = left (center ℓ)) :=
    fun ℓ => Classical.choose_spec (Classical.choose_spec (hcyl ℓ))
  let read : M → W → Bool := fun ℓ y =>
    xor (xor (left (center ℓ)) (right y))
      (((Finset.univ.filter (fun i : Fin m => i ∉ free ℓ ∧ center ℓ i = y i)).card % 2) == 1)
  refine ⟨read, ?_⟩
  unfold biasR
  have hq0 : q ≠ 0 := by positivity
  have hfib : (∑ x : W, ∑ y : W, sgn (read (send x) y) * sgn (left x) * sgn (right y) * chi x y) =
      ∑ ℓ : M, ∑ x ∈ Finset.univ.filter (fun u : W => send u = ℓ),
        ∑ y : W, sgn (read ℓ y) * sgn (left x) * sgn (right y) * chi x y := by
    have h1 := sum_fib Finset.univ Finset.univ send (fun _ _ => Finset.mem_univ _)
      (fun x => ∑ y : W, sgn (read (send x) y) * sgn (left x) * sgn (right y) * chi x y)
    rw [h1]
    refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun x hx => ?_
    have hxℓ : send x = ℓ := (Finset.mem_filter.mp hx).2
    simp_rw [hxℓ]
  rw [hfib]
  have hcell_val : ∀ ℓ : M,
      (∑ x ∈ Finset.univ.filter (fun u : W => send u = ℓ),
        ∑ y : W, sgn (read ℓ y) * sgn (left x) * sgn (right y) * chi x y) =
      (q ^ r) * (q ^ (m - r) * (q - 2) ^ r) := by
    intro ℓ
    have hcard_cell : (Finset.univ.filter (fun u : W => send u = ℓ)).card = (2 ^ a) ^ r := by
      let Fixed := {i : Fin m // i ∉ free ℓ}
      let Free := {i : Fin m // i ∈ free ℓ}
      have hfree_card : Fintype.card Free = r := by
        rw [Fintype.card_coe, (hspec ℓ).1]
      have hcard_free_fun : Fintype.card (Free → Fin a → ZMod 2) = (2 ^ a) ^ r := by
        rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ZMod.card, hfree_card]
      rw [← hcard_free_fun]
      refine Finset.card_bij (fun u _ i => u i.1) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro u1 hu1 u2 hu2 heq
        ext i j
        by_cases hi : i ∈ free ℓ
        · exact congrFun (congrFun heq ⟨i, hi⟩) j
        · have h1 := ((hspec ℓ).2.1 u1).mp (Finset.mem_filter.mp hu1).2 i hi
          have h2 := ((hspec ℓ).2.1 u2).mp (Finset.mem_filter.mp hu2).2 i hi
          rw [h1, h2]
      · intro g _
        let u : W := fun i => if hi : i ∈ free ℓ then g ⟨i, hi⟩ else center ℓ i
        refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hspec ℓ).2.1 u).mpr fun i hi => ?_⟩, ?_⟩
        · simp [u, hi]
        · ext ⟨i, hi⟩ j; simp [u, hi]
    have hinner : ∀ x ∈ Finset.univ.filter (fun u : W => send u = ℓ),
        (∑ y : W, sgn (read ℓ y) * sgn (left x) * sgn (right y) * chi x y) = q ^ (m - r) * (q - 2) ^ r := by
      intro x hx
      have hxℓ : send x = ℓ := (Finset.mem_filter.mp hx).2
      have hfix_x : ∀ i : Fin m, i ∉ free ℓ → x i = center ℓ i := ((hspec ℓ).2.1 x).mp hxℓ
      have hleft_x : left x = left (center ℓ) := (hspec ℓ).2.2 x hxℓ
      have hterm : ∀ y : W,
          sgn (read ℓ y) * sgn (left x) * sgn (right y) * chi x y =
          ∏ i : Fin m, (if i ∈ free ℓ then (if x i = y i then (-1 : ℝ) else 1) else 1) := by
        intro y
        have hread : sgn (read ℓ y) = sgn (left (center ℓ)) * sgn (right y) *
            sgn (((Finset.univ.filter (fun i : Fin m => i ∉ free ℓ ∧ center ℓ i = y i)).card % 2) == 1) := by
          dsimp [read]
          rw [sgn_xor, sgn_xor]
        have hflt : Finset.univ.filter (fun i : Fin m => i ∉ free ℓ ∧ center ℓ i = y i) =
            Finset.univ.filter (fun i : Fin m => i ∉ free ℓ ∧ x i = y i) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hi, heq⟩; exact ⟨hi, (hfix_x i hi).trans heq⟩
          · rintro ⟨hi, heq⟩; exact ⟨hi, (hfix_x i hi).symm.trans heq⟩
        have hsgn_fix : sgn (((Finset.univ.filter (fun i : Fin m => i ∉ free ℓ ∧ center ℓ i = y i)).card % 2) == 1) =
            ∏ i : Fin m, (if i ∉ free ℓ then (if x i = y i then (-1 : ℝ) else 1) else 1) := by
          rw [hflt, sgn_mod2_eq_one]
          have hprod_split : (∏ i : Fin m, (if i ∉ free ℓ then (if x i = y i then (-1 : ℝ) else 1) else 1)) =
              ∏ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ free ℓ ∧ x i = y i), (-1 : ℝ) := by
            rw [← Finset.prod_filter]
            have hsub : (Finset.univ.filter fun i : Fin m => i ∉ free ℓ) =
                (Finset.univ.filter fun i : Fin m => i ∉ free ℓ ∧ x i = y i) ∪
                (Finset.univ.filter fun i : Fin m => i ∉ free ℓ ∧ x i ≠ y i) := by
              ext i; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]; tauto
            have hdisj : Disjoint (Finset.univ.filter fun i : Fin m => i ∉ free ℓ ∧ x i = y i)
                (Finset.univ.filter fun i : Fin m => i ∉ free ℓ ∧ x i ≠ y i) := by
              rw [Finset.disjoint_left]
              intro i hi1 hi2
              exact (Finset.mem_filter.mp hi2).2.2 (Finset.mem_filter.mp hi1).2.2
            rw [hsub, Finset.prod_union hdisj]
            have h1 : ∏ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ free ℓ ∧ x i = y i),
                (if x i = y i then (-1 : ℝ) else 1) =
                ∏ _ ∈ Finset.univ.filter (fun i : Fin m => i ∉ free ℓ ∧ x i = y i), (-1 : ℝ) :=
              Finset.prod_congr rfl fun i hi => if_pos (Finset.mem_filter.mp hi).2.2
            have h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ free ℓ ∧ x i ≠ y i),
                (if x i = y i then (-1 : ℝ) else 1) = 1 :=
              Finset.prod_eq_one fun i hi => if_neg (Finset.mem_filter.mp hi).2.2
            rw [h1, h2, mul_one]
          rw [hprod_split, Finset.prod_const]
        have hchi_split : chi x y =
            (∏ i : Fin m, (if i ∉ free ℓ then (if x i = y i then (-1 : ℝ) else 1) else 1)) *
            (∏ i : Fin m, (if i ∈ free ℓ then (if x i = y i then (-1 : ℝ) else 1) else 1)) := by
          unfold chi
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          by_cases hi : i ∈ free ℓ <;> simp [hi]
        rw [hread, hleft_x, hsgn_fix, hchi_split]
        have hsq1 : sgn (left (center ℓ)) * sgn (left (center ℓ)) = 1 := sgn_sq _
        have hsq2 : sgn (right y) * sgn (right y) = 1 := sgn_sq _
        have hsq3 : (∏ i : Fin m, (if i ∉ free ℓ then (if x i = y i then (-1 : ℝ) else 1) else 1)) *
            (∏ i : Fin m, (if i ∉ free ℓ then (if x i = y i then (-1 : ℝ) else 1) else 1)) = 1 := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_eq_one fun i _ => ?_
          split_ifs <;> norm_num
        calc (sgn (left (center ℓ)) * sgn (right y) *
              ∏ i : Fin m, if i ∉ free ℓ then if x i = y i then (-1 : ℝ) else 1 else 1) *
              sgn (left (center ℓ)) * sgn (right y) *
              ((∏ i : Fin m, if i ∉ free ℓ then if x i = y i then (-1 : ℝ) else 1 else 1) *
               ∏ i : Fin m, if i ∈ free ℓ then if x i = y i then (-1 : ℝ) else 1 else 1)
            = (sgn (left (center ℓ)) * sgn (left (center ℓ))) * (sgn (right y) * sgn (right y)) *
              ((∏ i : Fin m, if i ∉ free ℓ then if x i = y i then (-1 : ℝ) else 1 else 1) *
               (∏ i : Fin m, if i ∉ free ℓ then if x i = y i then (-1 : ℝ) else 1 else 1)) *
              ∏ i : Fin m, if i ∈ free ℓ then if x i = y i then (-1 : ℝ) else 1 else 1 := by ring
          _ = 1 * 1 * 1 * ∏ i : Fin m, if i ∈ free ℓ then if x i = y i then (-1 : ℝ) else 1 else 1 := by
              rw [hsq1, hsq2, hsq3]
          _ = _ := by ring
      simp_rw [hterm]
      rw [← Fintype.prod_sum (fun i z => if i ∈ free ℓ then (if x i = z then (-1 : ℝ) else 1) else 1)]
      have hcoord : ∀ i : Fin m,
          (∑ z : Fin a → ZMod 2, (if i ∈ free ℓ then (if x i = z then (-1 : ℝ) else 1) else 1)) =
            if i ∈ free ℓ then (q - 2) else q := by
        intro i
        have hcard : (Fintype.card (Fin a → ZMod 2) : ℝ) = q := by
          rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]; push_cast; rfl
        by_cases hi : i ∈ free ℓ
        · simp_rw [if_pos hi]
          have hsplit : ∑ z : Fin a → ZMod 2, (if x i = z then (-1 : ℝ) else 1) =
              ∑ z : Fin a → ZMod 2, ((1 : ℝ) + (if z = x i then -2 else 0)) := by
            refine Finset.sum_congr rfl fun z _ => ?_
            by_cases hzx : z = x i <;> simp [hzx, eq_comm] <;> norm_num
          rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            mul_one, hcard, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
          ring
        · simp_rw [if_neg hi]
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
      simp_rw [hcoord]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      have hcard_free : (Finset.univ.filter fun i : Fin m => i ∈ free ℓ).card = r := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter, (hspec ℓ).1]
      have hcard_fix : (Finset.univ.filter fun i : Fin m => i ∉ free ℓ).card = m - r := by
        have hcomp : (Finset.univ.filter fun i : Fin m => i ∉ free ℓ) = Finset.univ \ free ℓ := by
          ext i; simp
        rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, (hspec ℓ).1]
      rw [hcard_free, hcard_fix]
      ring
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, hcard_cell]
    push_cast [q]
    ring
  dsimp [M]
  simp_rw [hcell_val]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hM : (((2 ^ a) ^ (m - r) : ℕ) : ℝ) = q ^ (m - r) := by push_cast [q]; rfl
  rw [hM]
  have hadd : r + (m - r) = m := Nat.add_sub_cancel' hr
  have hpow_m : q ^ r * q ^ (m - r) = q ^ m := by
    rw [← pow_add, hadd]
  have hdiv_pow : (q - 2) ^ r / q ^ r = (1 - 2 / q) ^ r := by
    rw [← div_pow]
    congr 1
    field_simp [hq0]
  calc (q ^ (m - r) * (q ^ r * (q ^ (m - r) * (q - 2) ^ r))) / (q ^ m) ^ 2
      = ((q ^ r * q ^ (m - r)) * q ^ (m - r) * (q - 2) ^ r) / (q ^ m * q ^ m) := by ring
    _ = (q ^ m * q ^ (m - r) * (q - 2) ^ r) / (q ^ m * (q ^ r * q ^ (m - r))) := by rw [hpow_m]
    _ = (q - 2) ^ r / q ^ r := by field_simp [hq0]
    _ = (1 - 2 / q) ^ r := hdiv_pow

end PEqualNP.Outside.L_lib_887_aux

open PEqualNP.Outside.L_lib_887_aux in
theorem PEqualNP.Outside.L_lib_887 : (∀ (a m r : Nat), 3 ≤ a → r ≤ m →
  let F := ZMod 2
  let W := Fin m → Fin a → F
  let q := 2^a
  let M := Fin (q^(m-r))
  let affine := fun (send : W → M) =>
    ∀ x : W, ∃ H : Submodule F W, ∀ y : W, send y = send x ↔ y-x ∈ H
  let cylinders := fun (send : W → M) (left : W → Bool) =>
    ∀ label : M, ∃ (center : W) (free : Finset (Fin m)),
      free.card = r ∧
      (∀ u : W, send u = label ↔ ∀ i : Fin m, i ∉ free → u i = center i) ∧
      (∀ u : W, send u = label → left u = left center)
  let bias := fun (send : W → M) (left right : W → Bool) (read : M → W → Bool) =>
    let correct := ((Finset.univ : Finset (W × W)).filter (fun z =>
      let parity := ((Finset.univ : Finset (Fin m)).filter (fun i => z.1 i = z.2 i)).card % 2 == 1
      read (send z.1) z.2 = xor (xor (left z.1) (right z.2)) parity)).card
    2*(correct : ℚ) / ((q : ℚ)^m)^2 - 1
  let cap : ℚ := (1-2/(q : ℚ))^r
  (∃ send : W → M, affine send ∧ cylinders send (fun _ => false)) ∧
    ∀ send : W → M, affine send → ∀ left right : W → Bool,
      (∀ read : M → W → Bool, |bias send left right read| ≤ cap) ∧
      ((∃ read : M → W → Bool, bias send left right read = cap) ↔ cylinders send left)) := by
  intro a m r ha hr F W q M affine cylinders bias cap
  refine ⟨exists_affine_cylinder a m r hr, ?_⟩
  intro send haff left right
  refine ⟨?_, ?_⟩
  · intro read
    have hle := (bias_abs_le_and_eq ha hr send haff left right read).1
    have hcast : ((|bias send left right read| : ℚ) : ℝ) ≤ ((cap : ℚ) : ℝ) := by
      dsimp only [bias, cap]
      rw [Rat.cast_abs, bias_cast_eq send left right read]
      simpa [q] using hle
    exact Rat.cast_le.mp hcast
  · constructor
    · rintro ⟨read, hEq⟩
      have hEqR : biasR send left right read = (1 - 2 / (2 : ℝ) ^ a) ^ r := by
        have h1 : ((bias send left right read : ℚ) : ℝ) = ((cap : ℚ) : ℝ) := congrArg Rat.cast hEq
        dsimp only [bias, cap] at h1
        rw [bias_cast_eq send left right read] at h1
        simpa [q] using h1
      exact (bias_abs_le_and_eq ha hr send haff left right read).2 hEqR
    · intro hcyl
      obtain ⟨read, hEqR⟩ := cylinders_attains ha hr send left right hcyl
      refine ⟨read, ?_⟩
      have hcast : ((bias send left right read : ℚ) : ℝ) = ((cap : ℚ) : ℝ) := by
        dsimp only [bias, cap]
        rw [bias_cast_eq send left right read]
        simpa [q] using hEqR
      exact Rat.cast_injective hcast
