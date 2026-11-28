import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_920_aux

open scoped BigOperators

lemma descFactorial_eval_eq (k u : ℕ) :
    (∏ j ∈ Finset.range k, ((u : ℚ) - (j : ℚ))) = (u.descFactorial k : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
    by_cases h : k ≤ u
    · rw [Nat.cast_mul, Nat.cast_sub h]; ring
    · have hu : u.descFactorial k = 0 := by
        rw [Nat.descFactorial_eq_zero_iff_lt]; omega
      simp [hu]

lemma choose_poly_eval (k u : ℕ) :
    ((Polynomial.C ((Nat.factorial k : ℚ)⁻¹) *
      ∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C (j : ℚ))).eval (u : ℚ)) =
      (Nat.choose u k : ℚ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [descFactorial_eval_eq, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hfac : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp [hfac]

lemma natDegree_prod_X_sub_C_nat (S : Finset ℕ) :
    (∏ j ∈ S, (Polynomial.X - Polynomial.C (j : ℚ))).natDegree = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 : (Polynomial.X - Polynomial.C (a : ℚ)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
    have h2 : (∏ j ∈ s, (Polynomial.X - Polynomial.C (j : ℚ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => Polynomial.X_sub_C_ne_zero _)
    rw [Polynomial.natDegree_mul h1 h2, Polynomial.natDegree_X_sub_C, ih, add_comm]

lemma choose_poly_natDegree (k : ℕ) :
    (Polynomial.C ((Nat.factorial k : ℚ)⁻¹) *
      ∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C (j : ℚ))).natDegree = k := by
  have hfac : (Nat.factorial k : ℚ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  rw [Polynomial.natDegree_C_mul hfac, natDegree_prod_X_sub_C_nat, Finset.card_range]

lemma choose_poly_leadingCoeff (k : ℕ) :
    (Polynomial.C ((Nat.factorial k : ℚ)⁻¹) *
      ∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C (j : ℚ))).leadingCoeff =
      (Nat.factorial k : ℚ)⁻¹ := by
  have hmon : (∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C (j : ℚ))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C (j : ℚ))
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hmon.leadingCoeff, mul_one]

lemma eval_sum_eq_zero_of_choose {d : ℕ} {S : Finset ℕ} (c : ℕ → ℚ)
    (h : ∀ k ≤ d, ∑ u ∈ S, c u * (Nat.choose u k : ℚ) = 0) :
    ∀ k ≤ d, ∀ P : Polynomial ℚ, P.natDegree ≤ k → ∑ u ∈ S, c u * P.eval (u : ℚ) = 0 := by
  intro k
  induction k with
  | zero =>
    intro hk P hdeg
    have hP : P = Polynomial.C (P.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hdeg)
    rw [hP]
    simp only [Polynomial.eval_C]
    have h0 := h 0 hk
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one] at h0
    calc ∑ u ∈ S, c u * P.coeff 0 = (∑ u ∈ S, c u) * P.coeff 0 := (Finset.sum_mul ..).symm
      _ = 0 := by rw [h0, zero_mul]
  | succ k ih =>
    intro hk P hdeg
    by_cases hlt : P.natDegree ≤ k
    · exact ih (Nat.le_of_succ_le hk) P hlt
    · have hdeq : P.natDegree = k + 1 := by omega
      let B : Polynomial ℚ := Polynomial.C ((Nat.factorial (k + 1) : ℚ)⁻¹) *
        ∏ j ∈ Finset.range (k + 1), (Polynomial.X - Polynomial.C (j : ℚ))
      have hBdeg : B.natDegree = k + 1 := choose_poly_natDegree (k + 1)
      have hBlc : B.leadingCoeff = (Nat.factorial (k + 1) : ℚ)⁻¹ :=
        choose_poly_leadingCoeff (k + 1)
      let a : ℚ := P.leadingCoeff * (Nat.factorial (k + 1) : ℚ)
      let Q : Polynomial ℚ := P - Polynomial.C a * B
      have hQdeg : Q.natDegree ≤ k := by
        by_cases hQ0 : Q = 0
        · simp [hQ0]
        · have hle : Q.natDegree ≤ k + 1 := by
            refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le hdeg ?_)
            refine le_trans Polynomial.natDegree_mul_le ?_
            simp [hBdeg]
          have hcoeff : Q.coeff (k + 1) = 0 := by
            simp only [Q, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
            have hp1 : P.coeff (k + 1) = P.leadingCoeff := by rw [← hdeq]; rfl
            have hb1 : B.coeff (k + 1) = B.leadingCoeff := by rw [← hBdeg]; rfl
            rw [hp1, hb1, hBlc]
            have hfac : (Nat.factorial (k + 1) : ℚ) ≠ 0 :=
              Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
            dsimp only [a]
            field_simp [hfac]
            ring
          have hne : Q.natDegree ≠ k + 1 := by
            intro heq
            have hlc : Q.leadingCoeff = 0 := by
              rw [Polynomial.leadingCoeff, heq]; exact hcoeff
            exact hQ0 (Polynomial.leadingCoeff_eq_zero.mp hlc)
          omega
      have hPQ : P = Q + Polynomial.C a * B := by simp [Q]
      rw [hPQ]
      have hsumQ := ih (Nat.le_of_succ_le hk) Q hQdeg
      have hsumB : ∑ u ∈ S, c u * B.eval (u : ℚ) = 0 := by
        have := h (k + 1) hk
        convert this using 2 with u
        rw [choose_poly_eval]
      calc ∑ u ∈ S, c u * (Q + Polynomial.C a * B).eval (u : ℚ)
          = ∑ u ∈ S, (c u * Q.eval (u : ℚ) + a * (c u * B.eval (u : ℚ))) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
              ring
        _ = (∑ u ∈ S, c u * Q.eval (u : ℚ)) + a * (∑ u ∈ S, c u * B.eval (u : ℚ)) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = 0 := by rw [hsumQ, hsumB, mul_zero, add_zero]

lemma binomial_vandermonde {d : ℕ} {S : Finset ℕ} (hS : S.card ≤ d + 1) (c : ℕ → ℚ)
    (h : ∀ k ≤ d, ∑ u ∈ S, c u * (Nat.choose u k : ℚ) = 0) :
    ∀ u ∈ S, c u = 0 := by
  intro u₀ hu₀
  let P : Polynomial ℚ := ∏ v ∈ S.erase u₀, (Polynomial.X - Polynomial.C (v : ℚ))
  have hdeg : P.natDegree ≤ d := by
    have h1 : P.natDegree = (S.erase u₀).card := natDegree_prod_X_sub_C_nat _
    rw [h1, Finset.card_erase_of_mem hu₀]
    omega
  have hsum := eval_sum_eq_zero_of_choose c h d (le_refl d) P hdeg
  have hsingle : ∑ u ∈ S, c u * P.eval (u : ℚ) = c u₀ * P.eval (u₀ : ℚ) := by
    refine Finset.sum_eq_single u₀ ?_ (fun h => absurd hu₀ h)
    intro u hu hne
    have hmem : u ∈ S.erase u₀ := Finset.mem_erase.mpr ⟨hne, hu⟩
    have hev : P.eval (u : ℚ) = 0 := by
      dsimp only [P]
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero hmem (by simp)
    rw [hev, mul_zero]
  rw [hsingle] at hsum
  have hne : P.eval (u₀ : ℚ) ≠ 0 := by
    dsimp only [P]
    rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun v hv => ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hvu : v ≠ u₀ := (Finset.mem_erase.mp hv).1
    exact sub_ne_zero.mpr (by exact_mod_cast hvu.symm)
  exact (mul_eq_zero.mp hsum).resolve_right hne

abbrev TruncPoly (d : ℕ) := Polynomial ℚ ⧸ Ideal.span {(Polynomial.X : Polynomial ℚ) ^ (d + 1)}

noncomputable def truncMk (d : ℕ) : Polynomial ℚ →+* TruncPoly d :=
  Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial ℚ) ^ (d + 1)})

noncomputable def truncS (d : ℕ) : TruncPoly d := truncMk d Polynomial.X

lemma truncS_pow_eq_zero (d : ℕ) : truncS d ^ (d + 1) = 0 := by
  rw [truncS, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

lemma truncMk_eq_zero_iff (d : ℕ) (P : Polynomial ℚ) :
    truncMk d P = 0 ↔ ∀ k ≤ d, P.coeff k = 0 := by
  rw [truncMk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h k hk; exact h k (Nat.lt_succ_of_le hk)
  · intro h k hk; exact h k (Nat.lt_succ_iff.mp hk)

lemma truncMk_C_injective (d : ℕ) : Function.Injective (fun q : ℚ => truncMk d (Polynomial.C q)) := by
  intro q1 q2 h
  dsimp only at h
  have h0 : truncMk d (Polynomial.C (q1 - q2)) = 0 := by
    rw [map_sub, map_sub, h, sub_self]
  have hc := (truncMk_eq_zero_iff d _).mp h0 0 (Nat.zero_le d)
  simp only [Polynomial.coeff_C_zero] at hc
  linarith

lemma coeff_sum_poly {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  rw [← Polynomial.lcoeff_apply, map_sum]
  rfl

lemma coeff_one_add_X_pow (u k : ℕ) :
    ((1 + Polynomial.X : Polynomial ℚ) ^ u).coeff k = (Nat.choose u k : ℚ) := by
  rw [add_comm, add_pow, coeff_sum_poly]
  simp only [one_pow, mul_one, Polynomial.coeff_X_pow_mul', Polynomial.coeff_natCast_ite]
  by_cases h : k ≤ u
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hbk
      by_cases hle : b ≤ k
      · simp [hle, show k - b ≠ 0 by omega]
      · simp [hle]
    · intro hk; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le h)) hk
  · rw [Finset.sum_eq_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · intro b hb
      rw [Finset.mem_range] at hb
      have hle : b ≤ k := by omega
      simp [hle, show k - b ≠ 0 by omega]

lemma trunc_lin_indep {d : ℕ} {S : Finset ℕ} (hS : S.card ≤ d + 1) (c : ℕ → ℚ)
    (h : ∑ u ∈ S, truncMk d (Polynomial.C (c u)) * (1 + truncS d) ^ u = 0) :
    ∀ u ∈ S, c u = 0 := by
  let P : Polynomial ℚ := ∑ u ∈ S, Polynomial.C (c u) * (1 + Polynomial.X) ^ u
  have hP0 : truncMk d P = 0 := by
    simp only [P, map_sum, map_mul, map_pow, map_add, map_one]
    exact h
  have hcoeff := (truncMk_eq_zero_iff d P).mp hP0
  refine binomial_vandermonde hS c fun k hk => ?_
  have := hcoeff k hk
  dsimp only [P] at this
  rw [coeff_sum_poly] at this
  simp only [Polynomial.coeff_C_mul, coeff_one_add_X_pow] at this
  exact this

def IsHighOrder {R : Type*} [CommRing R] (L : ℕ) (f : PowerSeries R) : Prop :=
  PowerSeries.constantCoeff f = 1 ∧ ∀ m, 0 < m → m < L → PowerSeries.coeff m f = 0

lemma isHighOrder_one {R : Type*} [CommRing R] (L : ℕ) :
    IsHighOrder L (1 : PowerSeries R) := by
  refine ⟨by simp, fun m hm _ => ?_⟩
  simp [PowerSeries.coeff_one, Nat.ne_of_gt hm]

lemma isHighOrder_mul {R : Type*} [CommRing R] {L : ℕ} {f g : PowerSeries R}
    (hf : IsHighOrder L f) (hg : IsHighOrder L g) (hL : 0 < L) :
    IsHighOrder L (f * g) ∧
      PowerSeries.coeff L (f * g) = PowerSeries.coeff L f + PowerSeries.coeff L g := by
  refine ⟨⟨by simp [hf.1, hg.1], fun m hm hmL => ?_⟩, ?_⟩
  · rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hsum : x.1 + x.2 = m := by simpa using hx
    rcases Nat.eq_zero_or_pos x.1 with h1 | h1
    · have h2 : x.2 = m := by omega
      rw [h2, hg.2 m hm hmL, mul_zero]
    · have h1L : x.1 < L := by omega
      rw [hf.2 x.1 h1 h1L, zero_mul]
  · rw [PowerSeries.coeff_mul]
    let A := Finset.HasAntidiagonal.antidiagonal L
    have hmem1 : (0, L) ∈ A := by simp [A]
    have hmem2 : (L, 0) ∈ A := by simp [A]
    have hne : (0, L) ≠ (L, 0) := by intro h; cases h; omega
    have hsplit : ∑ x ∈ A, PowerSeries.coeff x.1 f * PowerSeries.coeff x.2 g =
        PowerSeries.coeff 0 f * PowerSeries.coeff L g +
        PowerSeries.coeff L f * PowerSeries.coeff 0 g := by
      rw [← Finset.add_sum_erase _ _ hmem1]
      have hmem2' : (L, 0) ∈ A.erase (0, L) := Finset.mem_erase.mpr ⟨hne.symm, hmem2⟩
      rw [← Finset.add_sum_erase _ _ hmem2']
      have hrest : ∑ x ∈ (A.erase (0, L)).erase (L, 0),
          PowerSeries.coeff x.1 f * PowerSeries.coeff x.2 g = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx1 := Finset.mem_erase.mp hx
        have hx2 := Finset.mem_erase.mp hx1.2
        have hsum : x.1 + x.2 = L := by simpa [A] using hx2.2
        have hpos1 : 0 < x.1 := by
          by_contra h
          have : x.1 = 0 := by omega
          have : x.2 = L := by omega
          exact hx2.1 (Prod.ext ‹x.1 = 0› ‹x.2 = L›)
        have hlt1 : x.1 < L := by
          by_contra h
          have : x.1 = L := by omega
          have : x.2 = 0 := by omega
          exact hx1.1 (Prod.ext ‹x.1 = L› ‹x.2 = 0›)
        rw [hf.2 x.1 hpos1 hlt1, zero_mul]
      rw [hrest, add_zero]
    change ∑ x ∈ A, PowerSeries.coeff x.1 f * PowerSeries.coeff x.2 g = _
    rw [hsplit]
    have hc0f : PowerSeries.coeff 0 f = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
    have hc0g : PowerSeries.coeff 0 g = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact hg.1
    rw [hc0f, hc0g, one_mul, mul_one, add_comm]

lemma isHighOrder_inv {R : Type*} [CommRing R] {L : ℕ} (hL : 0 < L)
    (u : (PowerSeries R)ˣ) (hf : IsHighOrder L (u : PowerSeries R)) :
    IsHighOrder L ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) ∧
      PowerSeries.coeff L ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) =
        -PowerSeries.coeff L (u : PowerSeries R) := by
  have hmul1 : (u : PowerSeries R) * ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) = 1 := u.mul_inv
  have hc0 : PowerSeries.constantCoeff ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) = 1 := by
    have := congrArg (PowerSeries.constantCoeff (R := R)) hmul1
    rw [map_mul, map_one, hf.1, one_mul] at this
    exact this
  have hzero : ∀ m, 0 < m → m < L →
      PowerSeries.coeff m ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro hm hmL
      have h1 := congrArg (PowerSeries.coeff (R := R) m) hmul1
      rw [PowerSeries.coeff_one, ite_eq_right_iff.mpr (fun heq => absurd heq (Nat.ne_of_gt hm)),
        PowerSeries.coeff_mul] at h1
      let A := Finset.HasAntidiagonal.antidiagonal m
      have hmem : (0, m) ∈ A := by simp [A]
      change ∑ x ∈ A, PowerSeries.coeff x.1 (u : PowerSeries R) *
          PowerSeries.coeff x.2 ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) = 0 at h1
      rw [← Finset.add_sum_erase _ _ hmem] at h1
      have hrest : ∑ x ∈ A.erase (0, m),
          PowerSeries.coeff x.1 (u : PowerSeries R) *
            PowerSeries.coeff x.2 ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx1 := Finset.mem_erase.mp hx
        have hsum : x.1 + x.2 = m := by simpa [A] using hx1.2
        have hpos1 : 0 < x.1 := by
          by_contra h
          have : x.1 = 0 := by omega
          have : x.2 = m := by omega
          exact hx1.1 (Prod.ext ‹x.1 = 0› ‹x.2 = m›)
        rw [hf.2 x.1 hpos1 (by omega), zero_mul]
      rw [hrest, add_zero] at h1
      have hc0u : PowerSeries.coeff 0 (u : PowerSeries R) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
      rw [hc0u, one_mul] at h1
      exact h1
  have hinv_ho : IsHighOrder L ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) := ⟨hc0, hzero⟩
  have hLsum := (isHighOrder_mul hf hinv_ho hL).2
  rw [hmul1, PowerSeries.coeff_one,
    ite_eq_right_iff.mpr (fun heq => absurd heq (Nat.ne_of_gt hL))] at hLsum
  exact ⟨hinv_ho, eq_neg_of_add_eq_zero_right hLsum.symm⟩

lemma isHighOrder_pow {R : Type*} [CommRing R] {L : ℕ} (hL : 0 < L) {f : PowerSeries R}
    (hf : IsHighOrder L f) (k : ℕ) :
    IsHighOrder L (f ^ k) ∧ PowerSeries.coeff L (f ^ k) = (k : R) * PowerSeries.coeff L f := by
  induction k with
  | zero =>
    refine ⟨isHighOrder_one L, ?_⟩
    rw [pow_zero, PowerSeries.coeff_one,
      ite_eq_right_iff.mpr (fun heq => absurd heq (Nat.ne_of_gt hL)), Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ]
    obtain ⟨h1, h2⟩ := isHighOrder_mul ih.1 hf hL
    refine ⟨h1, ?_⟩
    rw [h2, ih.2, Nat.cast_succ]
    ring

lemma isHighOrder_zpow {R : Type*} [CommRing R] {L : ℕ} (hL : 0 < L)
    (u : (PowerSeries R)ˣ) (hf : IsHighOrder L (u : PowerSeries R)) (e : ℤ) :
    IsHighOrder L ((u ^ e : (PowerSeries R)ˣ) : PowerSeries R) ∧
      PowerSeries.coeff L ((u ^ e : (PowerSeries R)ˣ) : PowerSeries R) =
        (e : R) * PowerSeries.coeff L (u : PowerSeries R) := by
  cases e with
  | ofNat n =>
    have hval : ((u ^ Int.ofNat n : (PowerSeries R)ˣ) : PowerSeries R) =
        (u : PowerSeries R) ^ n := by
      change ((u ^ (n : ℤ) : (PowerSeries R)ˣ) : PowerSeries R) = _
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hval, Int.ofNat_eq_natCast, Int.cast_natCast]
    exact isHighOrder_pow hL hf n
  | negSucc n =>
    have hval : ((u ^ Int.negSucc n : (PowerSeries R)ˣ) : PowerSeries R) =
        ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) ^ (n + 1) := by
      rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    rw [hval, Int.cast_negSucc]
    obtain ⟨hi1, hi2⟩ := isHighOrder_inv hL u hf
    obtain ⟨hp1, hp2⟩ := isHighOrder_pow hL hi1 (n + 1)
    refine ⟨hp1, ?_⟩
    rw [hp2, hi2, Nat.cast_add, Nat.cast_one]
    ring

lemma isHighOrder_prod {ι R : Type*} [CommRing R] {L : ℕ} (hL : 0 < L)
    (s : Finset ι) (g : ι → PowerSeries R) (hg : ∀ i ∈ s, IsHighOrder L (g i)) :
    IsHighOrder L (∏ i ∈ s, g i) ∧
      PowerSeries.coeff L (∏ i ∈ s, g i) = ∑ i ∈ s, PowerSeries.coeff L (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨isHighOrder_one L, ?_⟩
    rw [Finset.prod_empty, Finset.sum_empty, PowerSeries.coeff_one,
      ite_eq_right_iff.mpr (fun heq => absurd heq (Nat.ne_of_gt hL))]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    obtain ⟨h1, h2⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    obtain ⟨hm1, hm2⟩ := isHighOrder_mul (hg a (Finset.mem_insert_self a s)) h1 hL
    exact ⟨hm1, by rw [hm2, h2]⟩

lemma coeff_C_mul_X_pow_ps {R : Type*} [CommRing R] (c : R) (M m : ℕ) :
    PowerSeries.coeff m (PowerSeries.C c * (PowerSeries.X : PowerSeries R) ^ M) =
      if m = M then c else 0 := by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  split_ifs <;> simp

lemma isHighOrder_one_add_C_X_pow {R : Type*} [CommRing R] {L M : ℕ} (hL : 0 < L) (hLM : L ≤ M)
    (c : R) :
    IsHighOrder L (1 + PowerSeries.C c * (PowerSeries.X : PowerSeries R) ^ M) ∧
      PowerSeries.coeff L (1 + PowerSeries.C c * (PowerSeries.X : PowerSeries R) ^ M) =
        if M = L then c else 0 := by
  have hM0 : M ≠ 0 := by omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [PowerSeries.constantCoeff_X, hM0]
  · intro m hm hmL
    rw [map_add, PowerSeries.coeff_one,
      ite_eq_right_iff.mpr (fun heq => absurd heq (Nat.ne_of_gt hm)), zero_add,
      coeff_C_mul_X_pow_ps, ite_eq_right_iff.mpr (by omega)]
  · rw [map_add, PowerSeries.coeff_one,
      ite_eq_right_iff.mpr (fun heq => absurd heq (Nat.ne_of_gt hL)), zero_add,
      coeff_C_mul_X_pow_ps]
    by_cases hEq : L = M
    · simp [hEq]
    · simp [hEq, Ne.symm hEq]

noncomputable def unitOfConstOne {R : Type*} [CommRing R] (f : PowerSeries R)
    (h : PowerSeries.constantCoeff f = 1) : (PowerSeries R)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [h]; exact isUnit_one)).unit

lemma unitOfConstOne_val {R : Type*} [CommRing R] (f : PowerSeries R)
    (h : PowerSeries.constantCoeff f = 1) :
    (unitOfConstOne f h : PowerSeries R) = f :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [h]; exact isUnit_one)).unit_spec

lemma val_prod_units {ι R : Type*} [CommMonoid R] (s : Finset ι) (f : ι → Rˣ) :
    ((∏ i ∈ s, f i : Rˣ) : R) = ∏ i ∈ s, (f i : R) := by
  rw [← Units.coeHom_apply, map_prod]
  rfl

lemma bool_sign_prod {K : Type*} [CommRing K] {n : ℕ} (s : Fin n → Bool) (w : Fin n → ℕ) :
    (∏ i : Fin n, ((1 : K) + (if s i then (-1 : K) else 1) * (-1 : K) ^ (w i))) =
      if (∀ i : Fin n, w i % 2 = (s i).toNat) then (2 : K) ^ n else 0 := by
  by_cases h : ∀ i : Fin n, w i % 2 = (s i).toNat
  · rw [if_pos h]
    calc ∏ i : Fin n, ((1 : K) + (if s i then (-1 : K) else 1) * (-1 : K) ^ (w i))
        = ∏ _i : Fin n, (2 : K) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            have hi := h i
            rcases Nat.even_or_odd (w i) with ⟨k, hk⟩ | ⟨k, hk⟩
            · have hs : s i = false := by cases hsi : s i <;> simp [hsi, hk] at hi ⊢ <;> omega
              rw [hs, if_neg Bool.false_ne_true, one_mul, hk, ← two_mul, pow_mul]
              norm_num
            · have hs : s i = true := by cases hsi : s i <;> simp [hsi, hk] at hi ⊢ <;> omega
              rw [hs, if_pos rfl, hk, pow_succ, pow_mul]
              norm_num
      _ = (2 : K) ^ n := by simp
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rcases Nat.even_or_odd (w i) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hs : s i = true := by cases hsi : s i <;> simp [hsi, hk] at hi ⊢ <;> omega
      rw [hs, if_pos rfl, hk, ← two_mul, pow_mul]
      norm_num
    · have hs : s i = false := by cases hsi : s i <;> simp [hsi, hk] at hi ⊢ <;> omega
      rw [hs, if_neg Bool.false_ne_true, one_mul, hk, pow_succ, pow_mul]
      norm_num

lemma sum_bool_pow {K : Type*} [CommRing K] {α : Type*} [Fintype α] [DecidableEq α] (x : K) :
    ∑ f : α → Bool, x ^ (Finset.univ.filter (fun h : α => f h = true)).card =
      (1 + x) ^ Fintype.card α := by
  have h1 : ∀ f : α → Bool,
      x ^ (Finset.univ.filter (fun h : α => f h = true)).card =
        ∏ h : α, (if f h = true then x else 1) := by
    intro f
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  simp_rw [h1]
  have hps := Fintype.prod_sum (fun (_ : α) (b : Bool) => if b = true then x else (1 : K))
  rw [← hps]
  calc ∏ _h : α, (∑ b : Bool, if b = true then x else 1)
      = ∏ _h : α, (1 + x) := by
          refine Finset.prod_congr rfl fun _ _ => ?_
          simp [Fintype.sum_bool, add_comm]
    _ = (1 + x) ^ Fintype.card α := by simp

lemma sum_block_pair {K : Type*} [CommRing K] {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (sg : Bool) (x y : K) :
    ∑ q : (α → Bool) × (β → Bool),
        (x ^ (Finset.univ.filter (fun h : α => q.1 h = true)).card *
         y ^ (Finset.univ.filter (fun h : β => q.2 h = true)).card +
         (if sg then (-1 : K) else 1) *
         (-x) ^ (Finset.univ.filter (fun h : α => q.1 h = true)).card *
         (-y) ^ (Finset.univ.filter (fun h : β => q.2 h = true)).card) =
      (1 + x) ^ Fintype.card α * (1 + y) ^ Fintype.card β +
        (if sg then (-1 : K) else 1) * (1 - x) ^ Fintype.card α * (1 - y) ^ Fintype.card β := by
  rw [Finset.sum_add_distrib]
  have hs1 : ∑ q : (α → Bool) × (β → Bool),
      x ^ (Finset.univ.filter (fun h : α => q.1 h = true)).card *
      y ^ (Finset.univ.filter (fun h : β => q.2 h = true)).card =
      (1 + x) ^ Fintype.card α * (1 + y) ^ Fintype.card β := by
    rw [Fintype.sum_prod_type]
    calc ∑ f : α → Bool, ∑ g : β → Bool,
            x ^ (Finset.univ.filter (fun h : α => f h = true)).card *
            y ^ (Finset.univ.filter (fun h : β => g h = true)).card
        = ∑ f : α → Bool, (x ^ (Finset.univ.filter (fun h : α => f h = true)).card *
            ∑ g : β → Bool, y ^ (Finset.univ.filter (fun h : β => g h = true)).card) := by
            refine Finset.sum_congr rfl fun f _ => (Finset.mul_sum ..).symm
      _ = (∑ f : α → Bool, x ^ (Finset.univ.filter (fun h : α => f h = true)).card) *
            (∑ g : β → Bool, y ^ (Finset.univ.filter (fun h : β => g h = true)).card) :=
            (Finset.sum_mul ..).symm
      _ = (1 + x) ^ Fintype.card α * (1 + y) ^ Fintype.card β := by
            rw [sum_bool_pow, sum_bool_pow]
  have hs2 : ∑ q : (α → Bool) × (β → Bool),
      (if sg then (-1 : K) else 1) *
      (-x) ^ (Finset.univ.filter (fun h : α => q.1 h = true)).card *
      (-y) ^ (Finset.univ.filter (fun h : β => q.2 h = true)).card =
      (if sg then (-1 : K) else 1) * (1 - x) ^ Fintype.card α * (1 - y) ^ Fintype.card β := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    have hinner : ∑ f : α → Bool, ∑ g : β → Bool,
        (-x) ^ (Finset.univ.filter (fun h : α => f h = true)).card *
        (-y) ^ (Finset.univ.filter (fun h : β => g h = true)).card =
        (1 - x) ^ Fintype.card α * (1 - y) ^ Fintype.card β := by
      calc ∑ f : α → Bool, ∑ g : β → Bool,
              (-x) ^ (Finset.univ.filter (fun h : α => f h = true)).card *
              (-y) ^ (Finset.univ.filter (fun h : β => g h = true)).card
          = ∑ f : α → Bool, ((-x) ^ (Finset.univ.filter (fun h : α => f h = true)).card *
              ∑ g : β → Bool, (-y) ^ (Finset.univ.filter (fun h : β => g h = true)).card) := by
              refine Finset.sum_congr rfl fun f _ => (Finset.mul_sum ..).symm
        _ = (∑ f : α → Bool, (-x) ^ (Finset.univ.filter (fun h : α => f h = true)).card) *
              (∑ g : β → Bool, (-y) ^ (Finset.univ.filter (fun h : β => g h = true)).card) :=
              (Finset.sum_mul ..).symm
        _ = (1 - x) ^ Fintype.card α * (1 - y) ^ Fintype.card β := by
              rw [sum_bool_pow, sum_bool_pow]; simp only [← sub_eq_add_neg]
    exact congrArg ((if sg then (-1 : K) else 1) * ·) hinner
  rw [hs1, hs2]

set_option maxHeartbeats 800000 in
lemma hist_genfun_ring {K : Type*} [CommRing K] {A B m f : ℕ}
    (red : Fin A → Fin m) (blue : Fin B → Fin m) (s : Fin m → Bool) (x y : K) :
    let a := fun i : Fin m => (Finset.univ.filter (fun h : Fin A => red h = i)).card
    let b := fun i : Fin m => (Finset.univ.filter (fun h : Fin B => blue h = i)).card
    let X := (Fin A → Bool) × (Fin B → Bool)
    let hist := fun u v : ℕ =>
      2 ^ f * ((Finset.univ : Finset X).filter (fun p =>
        (Finset.univ.filter (fun h : Fin A => p.1 h = true)).card = u ∧
        (Finset.univ.filter (fun h : Fin B => p.2 h = true)).card = v ∧
        ∀ i : Fin m,
          ((Finset.univ.filter (fun h : Fin A => red h = i ∧ p.1 h = true)).card +
           (Finset.univ.filter (fun h : Fin B => blue h = i ∧ p.2 h = true)).card) % 2 =
          (s i).toNat)).card
    (2 : K) ^ m * ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
        (hist u v : K) * x ^ u * y ^ v =
      (2 : K) ^ f * ∏ i : Fin m, ((1 + x) ^ a i * (1 + y) ^ b i +
        (if s i then (-1 : K) else 1) * (1 - x) ^ a i * (1 - y) ^ b i) := by
  intro a b X hist
  let wtA : (Fin A → Bool) → ℕ := fun p => (Finset.univ.filter (fun h : Fin A => p h = true)).card
  let wtB : (Fin B → Bool) → ℕ := fun p => (Finset.univ.filter (fun h : Fin B => p h = true)).card
  let wtAi : Fin m → (Fin A → Bool) → ℕ :=
    fun i p => (Finset.univ.filter (fun h : Fin A => red h = i ∧ p h = true)).card
  let wtBi : Fin m → (Fin B → Bool) → ℕ :=
    fun i p => (Finset.univ.filter (fun h : Fin B => blue h = i ∧ p h = true)).card
  let ok : X → Prop := fun p => ∀ i : Fin m, (wtAi i p.1 + wtBi i p.2) % 2 = (s i).toNat
  have hsum_uv : ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
      (hist u v : K) * x ^ u * y ^ v =
      (2 : K) ^ f * ∑ p : X, if ok p then x ^ wtA p.1 * y ^ wtB p.2 else 0 := by
    have hinner : ∀ u v : ℕ,
        (hist u v : K) * x ^ u * y ^ v =
          (2 : K) ^ f * ∑ p : X, if wtA p.1 = u ∧ wtB p.2 = v ∧ ok p then
            x ^ wtA p.1 * y ^ wtB p.2 else 0 := by
      intro u v
      have hcard : ((Finset.univ : Finset X).filter
            (fun p => wtA p.1 = u ∧ wtB p.2 = v ∧ ok p)).card • (x ^ u * y ^ v) =
          ∑ p ∈ (Finset.univ : Finset X).filter (fun p => wtA p.1 = u ∧ wtB p.2 = v ∧ ok p),
            x ^ wtA p.1 * y ^ wtB p.2 := by
        rw [Finset.sum_congr rfl (fun p hp => by
          have h := (Finset.mem_filter.mp hp).2
          rw [h.1, h.2.1])]
        simp
      simp only [hist, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
      rw [← Finset.sum_filter, ← hcard, nsmul_eq_mul]
    simp_rw [hinner, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    calc ∑ v ∈ Finset.range (B + 1), ∑ u ∈ Finset.range (A + 1),
            ∑ p : X, (if wtA p.1 = u ∧ wtB p.2 = v ∧ ok p then x ^ wtA p.1 * y ^ wtB p.2 else 0)
        = ∑ p : X, ∑ v ∈ Finset.range (B + 1), ∑ u ∈ Finset.range (A + 1),
            (if wtA p.1 = u ∧ wtB p.2 = v ∧ ok p then x ^ wtA p.1 * y ^ wtB p.2 else 0) := by
            rw [Finset.sum_congr rfl (fun v _ => Finset.sum_comm), Finset.sum_comm]
      _ = ∑ p : X, if ok p then x ^ wtA p.1 * y ^ wtB p.2 else 0 := by
            refine Finset.sum_congr rfl fun p _ => ?_
            have hA : wtA p.1 ∈ Finset.range (A + 1) := by
              rw [Finset.mem_range]
              exact Nat.lt_succ_of_le (le_trans (Finset.card_filter_le _ _) (by simp))
            have hB : wtB p.2 ∈ Finset.range (B + 1) := by
              rw [Finset.mem_range]
              exact Nat.lt_succ_of_le (le_trans (Finset.card_filter_le _ _) (by simp))
            rw [Finset.sum_eq_single (wtB p.2)]
            · rw [Finset.sum_eq_single (wtA p.1)]
              · simp
              · intro u _ hu; simp [Ne.symm hu]
              · intro h; exact absurd hA h
            · intro v _ hv
              refine Finset.sum_eq_zero fun u _ => by simp [Ne.symm hv]
            · intro h; exact absurd hB h
  rw [hsum_uv, ← mul_assoc, mul_comm ((2 : K) ^ m), mul_assoc]
  congr 1
  have hind : (2 : K) ^ m * ∑ p : X, (if ok p then x ^ wtA p.1 * y ^ wtB p.2 else 0) =
      ∑ p : X, (∏ i : Fin m, ((1 : K) + (if s i then (-1 : K) else 1) *
          (-1 : K) ^ (wtAi i p.1 + wtBi i p.2))) * (x ^ wtA p.1 * y ^ wtB p.2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [bool_sign_prod s (fun i => wtAi i p.1 + wtBi i p.2)]
    split_ifs <;> simp
  rw [hind]
  have hwtA_sum : ∀ p : Fin A → Bool, wtA p = ∑ i : Fin m, wtAi i p := by
    intro p
    have hdisj : (Finset.univ.filter (fun h : Fin A => p h = true)) =
        Finset.univ.biUnion
          (fun i : Fin m => Finset.univ.filter (fun h : Fin A => red h = i ∧ p h = true)) := by
      ext h; simp
    dsimp only [wtA]
    rw [hdisj, Finset.card_biUnion]
    intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro h h1 h2
    exact hij ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
  have hwtB_sum : ∀ p : Fin B → Bool, wtB p = ∑ i : Fin m, wtBi i p := by
    intro p
    have hdisj : (Finset.univ.filter (fun h : Fin B => p h = true)) =
        Finset.univ.biUnion
          (fun i : Fin m => Finset.univ.filter (fun h : Fin B => blue h = i ∧ p h = true)) := by
      ext h; simp
    dsimp only [wtB]
    rw [hdisj, Finset.card_biUnion]
    intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro h h1 h2
    exact hij ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
  have hterm : ∀ p : X,
      (∏ i : Fin m, ((1 : K) + (if s i then (-1 : K) else 1) *
          (-1 : K) ^ (wtAi i p.1 + wtBi i p.2))) * (x ^ wtA p.1 * y ^ wtB p.2) =
      ∏ i : Fin m, (x ^ wtAi i p.1 * y ^ wtBi i p.2 +
        (if s i then (-1 : K) else 1) * (-x) ^ wtAi i p.1 * (-y) ^ wtBi i p.2) := by
    intro p
    rw [hwtA_sum p.1, hwtB_sum p.2, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_add, neg_eq_neg_one_mul x, neg_eq_neg_one_mul y, mul_pow, mul_pow]
    ring
  simp_rw [hterm]
  let eX : X ≃ ∀ i : Fin m, ({h : Fin A // red h = i} → Bool) × ({h : Fin B // blue h = i} → Bool) :=
    { toFun := fun p i => (fun h => p.1 h.1, fun h => p.2 h.1)
      invFun := fun q => (fun h => (q (red h)).1 ⟨h, rfl⟩, fun h => (q (blue h)).2 ⟨h, rfl⟩)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun q => by
        funext i
        ext ⟨h, hh⟩ <;> subst hh <;> rfl }
  have hwtAi_eq : ∀ (p : X) (i : Fin m),
      wtAi i p.1 = (Finset.univ.filter (fun h : {h : Fin A // red h = i} => (eX p i).1 h = true)).card := by
    intro p i
    refine Finset.card_bij (fun h hh => ⟨h, (Finset.mem_filter.mp hh).2.1⟩) ?_ ?_ ?_
    · intro h hh; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2.2⟩
    · intro h1 _ h2 _ heq; exact congrArg Subtype.val heq
    · intro ⟨h, hh⟩ hmem
      exact ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, (Finset.mem_filter.mp hmem).2⟩, rfl⟩
  have hwtBi_eq : ∀ (p : X) (i : Fin m),
      wtBi i p.2 = (Finset.univ.filter (fun h : {h : Fin B // blue h = i} => (eX p i).2 h = true)).card := by
    intro p i
    refine Finset.card_bij (fun h hh => ⟨h, (Finset.mem_filter.mp hh).2.1⟩) ?_ ?_ ?_
    · intro h hh; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2.2⟩
    · intro h1 _ h2 _ heq; exact congrArg Subtype.val heq
    · intro ⟨h, hh⟩ hmem
      exact ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, (Finset.mem_filter.mp hmem).2⟩, rfl⟩
  let blk : ∀ i : Fin m, (({h : Fin A // red h = i} → Bool) × ({h : Fin B // blue h = i} → Bool)) → K :=
    fun i q =>
      x ^ (Finset.univ.filter (fun h => q.1 h = true)).card *
      y ^ (Finset.univ.filter (fun h => q.2 h = true)).card +
      (if s i then (-1 : K) else 1) *
      (-x) ^ (Finset.univ.filter (fun h => q.1 h = true)).card *
      (-y) ^ (Finset.univ.filter (fun h => q.2 h = true)).card
  calc ∑ p : X, ∏ i : Fin m, (x ^ wtAi i p.1 * y ^ wtBi i p.2 +
          (if s i then (-1 : K) else 1) * (-x) ^ wtAi i p.1 * (-y) ^ wtBi i p.2)
      = ∑ q : ∀ i : Fin m, ({h : Fin A // red h = i} → Bool) × ({h : Fin B // blue h = i} → Bool),
          ∏ i : Fin m, blk i (q i) := by
          refine Fintype.sum_equiv eX _ _ fun p => ?_
          refine Finset.prod_congr rfl fun i _ => ?_
          dsimp only [blk]
          rw [hwtAi_eq p i, hwtBi_eq p i]
    _ = ∏ i : Fin m, ∑ q : ({h : Fin A // red h = i} → Bool) × ({h : Fin B // blue h = i} → Bool),
          blk i q := (Fintype.prod_sum blk).symm
    _ = ∏ i : Fin m, ((1 + x) ^ a i * (1 + y) ^ b i +
          (if s i then (-1 : K) else 1) * (1 - x) ^ a i * (1 - y) ^ b i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          have hcardA : Fintype.card {h : Fin A // red h = i} = a i := Fintype.card_subtype _
          have hcardB : Fintype.card {h : Fin B // blue h = i} = b i := Fintype.card_subtype _
          rw [sum_block_pair (s i) x y, hcardA, hcardB]

lemma bivar_poly_eq_of_pos_rat {A B : ℕ} (c₁ c₂ : ℕ → ℕ → ℚ)
    (h : ∀ x y : ℚ, 0 < x → 0 < y →
      ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1), c₁ u v * x ^ u * y ^ v =
      ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1), c₂ u v * x ^ u * y ^ v) :
    ∀ u ≤ A, ∀ v ≤ B, c₁ u v = c₂ u v := by
  have hpoly : ∀ (n : ℕ) (f : ℕ → ℚ),
      (∀ x : ℚ, 0 < x → ∑ i ∈ Finset.range (n + 1), f i * x ^ i = 0) →
      ∀ i ≤ n, f i = 0 := by
    intro n f hf
    let P : Polynomial ℚ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (f i) * Polynomial.X ^ i
    have hroots : ∀ k : ℕ, P.IsRoot ((k + 1 : ℕ) : ℚ) := by
      intro k
      rw [Polynomial.IsRoot]
      change (Polynomial.evalRingHom ((k + 1 : ℕ) : ℚ)) P = 0
      dsimp only [P]
      rw [map_sum]
      simp only [map_mul, map_pow, Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X]
      exact hf _ (by positivity)
    have hP0 : P = 0 := by
      by_contra hne
      have hsub : (Finset.range (P.natDegree + 1)).image (fun k : ℕ => ((k + 1 : ℕ) : ℚ)) ⊆
          P.roots.toFinset := by
        intro q hq
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr (hroots k))
      have hcard1 : ((Finset.range (P.natDegree + 1)).image (fun k : ℕ => ((k + 1 : ℕ) : ℚ))).card =
          P.natDegree + 1 := by
        rw [Finset.card_image_of_injective _ (fun a b hab => by
          have : a + 1 = b + 1 := by exact_mod_cast hab
          omega), Finset.card_range]
      have hcard2 := Finset.card_le_card hsub
      have hcard3 : P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      have hcard4 : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
      omega
    intro i hi
    have hc := congrArg (fun Q : Polynomial ℚ => Q.coeff i) hP0
    dsimp only [P] at hc
    rw [coeff_sum_poly, Polynomial.coeff_zero] at hc
    simp only [Polynomial.coeff_C_mul_X_pow] at hc
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))] at hc
    exact hc
  have h1 : ∀ y : ℚ, 0 < y → ∀ u ≤ A,
      ∑ v ∈ Finset.range (B + 1), (c₁ u v - c₂ u v) * y ^ v = 0 := by
    intro y hy
    refine hpoly A (fun u => ∑ v ∈ Finset.range (B + 1), (c₁ u v - c₂ u v) * y ^ v) fun x hx => ?_
    have heq := h x y hx hy
    have : ∑ u ∈ Finset.range (A + 1),
          (∑ v ∈ Finset.range (B + 1), (c₁ u v - c₂ u v) * y ^ v) * x ^ u =
        (∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1), c₁ u v * x ^ u * y ^ v) -
        (∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1), c₂ u v * x ^ u * y ^ v) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [this, heq, sub_self]
  intro u hu v hv
  have := hpoly B (fun v => c₁ u v - c₂ u v) (fun y hy => h1 y hy u hu) v hv
  linarith

lemma genfun_moment_expansion {R : Type*} [CommRing R] {A B d : ℕ}
    (hist : ℕ → ℕ → ℕ) (hhist0 : ∀ u v, B < v → hist u v = 0)
    (Y t : R) (ht : t ^ (d + 1) = 0) :
    let moment := fun h L : ℕ =>
      ∑ u ∈ Finset.range (A + 1), if u ≤ L then Nat.choose u h * hist u (L - u) else 0
    ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
        (hist u v : R) * (Y * (1 + t)) ^ u * Y ^ v =
      ∑ h ∈ Finset.range (d + 1), ∑ L ∈ Finset.range (A + B + 1),
        (moment h L : R) * Y ^ L * t ^ h := by
  intro moment
  have hpow : ∀ u : ℕ, (1 + t) ^ u = ∑ h ∈ Finset.range (d + 1), (Nat.choose u h : R) * t ^ h := by
    intro u
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one]
    have htrunc : ∀ h : ℕ, d + 1 ≤ h → t ^ h = 0 := by
      intro h hh
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hh
      rw [pow_add, ht, zero_mul]
    by_cases hdu : u ≤ d
    · rw [Finset.sum_subset (Finset.range_mono (show u + 1 ≤ d + 1 by omega))]
      · refine Finset.sum_congr rfl fun h _ => mul_comm _ _
      · intro h hh hnot
        rw [Finset.mem_range] at hh hnot
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    · rw [← Finset.sum_subset (Finset.range_mono (show d + 1 ≤ u + 1 by omega))]
      · refine Finset.sum_congr rfl fun h _ => mul_comm _ _
      · intro h hh hnot
        rw [Finset.mem_range] at hh hnot
        rw [htrunc h (by omega), zero_mul]
  calc ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
          (hist u v : R) * (Y * (1 + t)) ^ u * Y ^ v
      = ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
          ∑ h ∈ Finset.range (d + 1),
            ((Nat.choose u h * hist u v : ℕ) : R) * Y ^ (u + v) * t ^ h := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          rw [mul_pow, hpow u, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Nat.cast_mul, pow_add]; ring
    _ = ∑ h ∈ Finset.range (d + 1), ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
          ((Nat.choose u h * hist u v : ℕ) : R) * Y ^ (u + v) * t ^ h := by
          rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm), Finset.sum_comm]
    _ = ∑ h ∈ Finset.range (d + 1), ∑ L ∈ Finset.range (A + B + 1),
          (moment h L : R) * Y ^ L * t ^ h := by
          refine Finset.sum_congr rfl fun h _ => ?_
          have hL : ∀ u ∈ Finset.range (A + 1),
              ∑ v ∈ Finset.range (B + 1),
                ((Nat.choose u h * hist u v : ℕ) : R) * Y ^ (u + v) * t ^ h =
              ∑ L ∈ Finset.range (A + B + 1),
                ((if u ≤ L then Nat.choose u h * hist u (L - u) else 0 : ℕ) : R) * Y ^ L * t ^ h := by
            intro u hu
            rw [Finset.mem_range] at hu
            calc ∑ v ∈ Finset.range (B + 1),
                    ((Nat.choose u h * hist u v : ℕ) : R) * Y ^ (u + v) * t ^ h
                = ∑ L ∈ (Finset.range (B + 1)).image (fun v => u + v),
                    ((if u ≤ L then Nat.choose u h * hist u (L - u) else 0 : ℕ) : R) * Y ^ L * t ^ h := by
                    rw [Finset.sum_image (fun a _ b _ hab => Nat.add_left_cancel hab)]
                    refine Finset.sum_congr rfl fun v _ => by simp
              _ = ∑ L ∈ Finset.range (A + B + 1),
                    ((if u ≤ L then Nat.choose u h * hist u (L - u) else 0 : ℕ) : R) * Y ^ L * t ^ h := by
                    refine Finset.sum_subset ?_ ?_
                    · intro L hLmem
                      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hLmem
                      rw [Finset.mem_range] at hv ⊢; omega
                    · intro L _ hnot
                      by_cases huL : u ≤ L
                      · have hgt : B < L - u := by
                          by_contra hle
                          exact hnot (Finset.mem_image.mpr
                            ⟨L - u, Finset.mem_range.mpr (by omega), by omega⟩)
                        rw [if_pos huL, hhist0 u (L - u) hgt, mul_zero, Nat.cast_zero,
                          zero_mul, zero_mul]
                      · simp [huL]
          rw [Finset.sum_congr rfl hL, Finset.sum_comm]
          refine Finset.sum_congr rfl fun L _ => ?_
          simp only [moment, Nat.cast_sum, Finset.sum_mul]

lemma fiber_card_sum {A m : ℕ} (f : Fin A → Fin m) :
    ∑ i : Fin m, (Finset.univ.filter (fun h : Fin A => f h = i)).card = A := by
  have h1 : (Finset.univ : Finset (Fin A)) =
      Finset.univ.biUnion (fun i : Fin m => Finset.univ.filter (fun h : Fin A => f h = i)) := by
    ext h; simp
  have h2 := congrArg Finset.card h1
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_biUnion] at h2
  · exact h2.symm
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro h h1 h2
    exact hij ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

lemma prod_fiber_nested {G : Type*} [CommGroup G] {m : ℕ}
    (P : Fin m → Prop) [DecidablePred P]
    (keyL keyU : Fin m → ℕ) (Ls : Finset ℕ) (supp : ℕ → Finset ℕ)
    (hL : ∀ i, P i → keyL i ∈ Ls) (hU : ∀ i, P i → keyU i ∈ supp (keyL i))
    (U : ℕ → ℕ → G) :
    ∏ i ∈ Finset.univ.filter P, U (keyL i) (keyU i) =
      ∏ L ∈ Ls, ∏ u ∈ supp L,
        (U L u) ^ (Finset.univ.filter (fun i : Fin m => keyU i = u ∧ keyL i = L ∧ P i)).card := by
  classical
  have h1 : ∏ L ∈ Ls, ∏ u ∈ supp L,
        (U L u) ^ (Finset.univ.filter (fun i : Fin m => keyU i = u ∧ keyL i = L ∧ P i)).card =
      ∏ L ∈ Ls, ∏ u ∈ supp L,
        ∏ i ∈ Finset.univ.filter (fun i : Fin m => keyU i = u ∧ keyL i = L ∧ P i),
          U (keyL i) (keyU i) := by
    refine Finset.prod_congr rfl fun L _ => Finset.prod_congr rfl fun u _ => ?_
    rw [Finset.prod_congr rfl (fun i hi => by
      have h := (Finset.mem_filter.mp hi).2
      rw [h.1, h.2.1]), Finset.prod_const]
  rw [h1]
  have h2 : ∀ L ∈ Ls,
      ∏ u ∈ supp L, ∏ i ∈ Finset.univ.filter (fun i : Fin m => keyU i = u ∧ keyL i = L ∧ P i),
        U (keyL i) (keyU i) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin m => keyL i = L ∧ P i), U (keyL i) (keyU i) := by
    intro L _
    rw [← Finset.prod_biUnion]
    · congr 1
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨u, _, _, h2, h3⟩; exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩; exact ⟨keyU i, h2 ▸ hU i h3, rfl, h2, h3⟩
    · intro u1 _ u2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro i h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
  rw [Finset.prod_congr rfl h2, ← Finset.prod_biUnion]
  · congr 1
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h3; exact ⟨keyL i, hL i h3, rfl, h3⟩
    · rintro ⟨L, _, _, h3⟩; exact h3
  · intro L1 _ L2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro i h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)

lemma prod_blocks_neg {G : Type*} [CommGroup G] {m : ℕ}
    (a b : Fin m → ℕ) (s : Fin m → Bool)
    (Ls : Finset ℕ) (supp : ℕ → Finset ℕ)
    (hL1 : ∀ i, a i + b i ∈ Ls) (hS1 : ∀ i, a i ∈ supp (a i + b i))
    (hL2 : ∀ i, s i = false → 2 * (a i + b i) ∈ Ls)
    (hS2 : ∀ i, s i = false → 2 * a i ∈ supp (2 * (a i + b i)))
    (U : ℕ → ℕ → G) :
    (∏ i : Fin m, if s i = true then U (a i + b i) (a i)
                  else U (2 * (a i + b i)) (2 * a i) * (U (a i + b i) (a i))⁻¹) =
      ∏ L ∈ Ls, ∏ u ∈ supp L,
        (U L u) ^ (((Finset.univ.filter (fun i : Fin m => a i = u ∧ a i + b i = L ∧ s i = true)).card : ℤ) -
                   ((Finset.univ.filter (fun i : Fin m => a i = u ∧ a i + b i = L ∧ s i = false)).card : ℤ) +
                   ((Finset.univ.filter (fun i : Fin m => 2 * a i = u ∧ 2 * (a i + b i) = L ∧ s i = false)).card : ℤ)) := by
  classical
  rw [Finset.prod_ite]
  have hcomp : Finset.univ.filter (fun i : Fin m => ¬s i = true) =
      Finset.univ.filter (fun i : Fin m => s i = false) := by
    ext i; cases s i <;> simp
  rw [hcomp, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [prod_fiber_nested (fun i => s i = true) (fun i => a i + b i) a Ls supp (fun i _ => hL1 i) (fun i _ => hS1 i) U]
  rw [prod_fiber_nested (fun i => s i = false) (fun i => 2 * (a i + b i)) (fun i => 2 * a i) Ls supp hL2 hS2 U]
  rw [prod_fiber_nested (fun i => s i = false) (fun i => a i + b i) a Ls supp (fun i _ => hL1 i) (fun i _ => hS1 i) U]
  simp only [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun L _ => Finset.prod_congr rfl fun u _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add, ← zpow_add]
  congr 1; ring

lemma prod_blocks_pm {G : Type*} [CommGroup G] {m : ℕ}
    (a b : Fin m → ℕ) (s : Fin m → Bool)
    (Ls : Finset ℕ) (supp : ℕ → Finset ℕ)
    (hL1 : ∀ i, a i + b i ∈ Ls) (hS1 : ∀ i, a i ∈ supp (a i + b i))
    (Uneg Upos : ℕ → ℕ → G) :
    (∏ i : Fin m, if s i = true then Uneg (a i + b i) (a i) else Upos (a i + b i) (a i)) =
      ∏ L ∈ Ls, ∏ u ∈ supp L,
        (Uneg L u) ^ (Finset.univ.filter (fun i : Fin m => a i = u ∧ a i + b i = L ∧ s i = true)).card *
        (Upos L u) ^ (Finset.univ.filter (fun i : Fin m => a i = u ∧ a i + b i = L ∧ s i = false)).card := by
  classical
  rw [Finset.prod_ite]
  have hcomp : Finset.univ.filter (fun i : Fin m => ¬s i = true) =
      Finset.univ.filter (fun i : Fin m => s i = false) := by
    ext i; cases s i <;> simp
  rw [hcomp]
  rw [prod_fiber_nested (fun i => s i = true) (fun i => a i + b i) a Ls supp (fun i _ => hL1 i) (fun i _ => hS1 i) Uneg]
  rw [prod_fiber_nested (fun i => s i = false) (fun i => a i + b i) a Ls supp (fun i _ => hL1 i) (fun i _ => hS1 i) Upos]
  simp only [← Finset.prod_mul_distrib]

set_option maxHeartbeats 800000 in
lemma recover_common_false {A B d : ℕ} {m : Bool → ℕ}
    (a b : (j : Bool) → Fin (m j) → ℕ) (s : (j : Bool) → Fin (m j) → Bool)
    (hpos : ∀ j i, 0 < a j i + b j i)
    (hleA : ∀ j i, a j i ≤ A) (hleB : ∀ j i, b j i ≤ B)
    (support : ℕ → Finset ℕ)
    (hS1 : ∀ j i, a j i ∈ support (a j i + b j i))
    (hS2 : ∀ j i, s j i = false → 2 * a j i ∈ support (2 * (a j i + b j i)))
    (hsupp : ∀ L, (support L).card ≤ d + 1)
    (hFps :
      ∏ i : Fin (m false), (1 + (if s false i then (-1 : PowerSeries (TruncPoly d)) else 1) *
        PowerSeries.C ((1 + truncS d) ^ (a false i)) *
        (PowerSeries.X : PowerSeries (TruncPoly d)) ^ (a false i + b false i)) =
      ∏ i : Fin (m true), (1 + (if s true i then (-1 : PowerSeries (TruncPoly d)) else 1) *
        PowerSeries.C ((1 + truncS d) ^ (a true i)) *
        (PowerSeries.X : PowerSeries (TruncPoly d)) ^ (a true i + b true i))) :
    ∀ U V : ℚ, |U| < 1 → |V| < 1 →
      ∏ i : Fin (m false), ((1 : ℚ) + (if s false i then (-1 : ℚ) else 1) * U ^ a false i * V ^ b false i) =
      ∏ i : Fin (m true), ((1 : ℚ) + (if s true i then (-1 : ℚ) else 1) * U ^ a true i * V ^ b true i) := by
  classical
  let R := TruncPoly d
  let PS := PowerSeries R
  let sR : R := truncS d
  let w : PS := PowerSeries.X
  let psC : R →+* PS := PowerSeries.C (R := R)
  let Mmax := 2 * (A + B)
  let Ls := Finset.Icc 1 Mmax
  have hmemL : ∀ (j : Bool) (i : Fin (m j)), a j i + b j i ∈ Ls := fun j i =>
    Finset.mem_Icc.mpr ⟨hpos j i, by have := hleA j i; have := hleB j i; omega⟩
  have hmem2L : ∀ (j : Bool) (i : Fin (m j)), s j i = false → 2 * (a j i + b j i) ∈ Ls := fun j i _ =>
    Finset.mem_Icc.mpr ⟨by have := hpos j i; omega, by have := hleA j i; have := hleB j i; omega⟩
  let e : Bool → ℕ → ℕ → ℤ := fun j L u =>
    ((Finset.univ.filter (fun i : Fin (m j) => a j i = u ∧ a j i + b j i = L ∧ s j i = true)).card : ℤ) -
    ((Finset.univ.filter (fun i : Fin (m j) => a j i = u ∧ a j i + b j i = L ∧ s j i = false)).card : ℤ) +
    ((Finset.univ.filter (fun i : Fin (m j) => 2 * a j i = u ∧ 2 * (a j i + b j i) = L ∧ s j i = false)).card : ℤ)
  let Uneg : ℕ → ℕ → PSˣ := fun L u =>
    if hL : 0 < L then
      unitOfConstOne (1 - psC ((1 + sR) ^ u) * w ^ L) (by simp [w, Nat.ne_of_gt hL])
    else 1
  have hUneg_val : ∀ L, 0 < L → ∀ u, (Uneg L u : PS) = 1 - psC ((1 + sR) ^ u) * w ^ L := by
    intro L hL u; simp only [Uneg, dif_pos hL, unitOfConstOne_val]
  have hFps_unit : ∀ j : Bool,
      ((∏ L ∈ Ls, ∏ u ∈ support L, (Uneg L u) ^ (e j L u) : PSˣ) : PS) =
      ∏ i : Fin (m j), (1 + (if s j i then (-1 : PS) else 1) *
        psC ((1 + sR) ^ (a j i)) * w ^ (a j i + b j i)) := by
    intro j
    rw [← prod_blocks_neg (a j) (b j) (s j) Ls support (hmemL j) (hS1 j) (hmem2L j) (hS2 j) Uneg]
    rw [val_prod_units]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hsi
    · rw [hUneg_val _ (hpos j i)]; ring
    · rw [Units.val_mul]
      have hu := (Uneg (a j i + b j i) (a j i)).isUnit
      apply hu.mul_right_cancel
      rw [mul_assoc, Units.inv_mul, mul_one,
        hUneg_val _ (by have := hpos j i; omega), hUneg_val _ (hpos j i)]
      rw [show 2 * a j i = a j i + a j i by omega,
        show 2 * (a j i + b j i) = (a j i + b j i) + (a j i + b j i) by omega,
        pow_add (1 + sR), pow_add w, map_mul]
      ring
  have hratio_one :
      (∏ L ∈ Ls, ∏ u ∈ support L, (Uneg L u) ^ (e false L u - e true L u) : PSˣ) = 1 := by
    have h1u : (∏ L ∈ Ls, ∏ u ∈ support L, (Uneg L u) ^ (e false L u) : PSˣ) =
        (∏ L ∈ Ls, ∏ u ∈ support L, (Uneg L u) ^ (e true L u) : PSˣ) := by
      apply Units.ext
      rw [hFps_unit false, hFps_unit true]
      exact hFps
    have h2 : (∏ L ∈ Ls, ∏ u ∈ support L, (Uneg L u) ^ (e false L u - e true L u) : PSˣ) =
        (∏ L ∈ Ls, ∏ u ∈ support L, (Uneg L u) ^ (e false L u) : PSˣ) *
        (∏ L ∈ Ls, ∏ u ∈ support L, (Uneg L u) ^ (e true L u) : PSˣ)⁻¹ := by
      refine eq_mul_inv_iff_mul_eq.mpr ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun L _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun u _ => by rw [← zpow_add, sub_add_cancel]
    rw [h2, h1u, mul_inv_cancel]
  have he_eq : ∀ L ∈ Ls, ∀ u ∈ support L, e false L u = e true L u := by
    intro L
    induction L using Nat.strong_induction_on with
    | ind L ih =>
      intro hLmem
      have hLpos : 0 < L := (Finset.mem_Icc.mp hLmem).1
      have hfac_ho : ∀ L' ∈ Ls, ∀ u ∈ support L',
          IsHighOrder L (((Uneg L' u) ^ (e false L' u - e true L' u) : PSˣ) : PS) ∧
          PowerSeries.coeff L (((Uneg L' u) ^ (e false L' u - e true L' u) : PSˣ) : PS) =
            if L' = L then -((e false L u - e true L u : ℤ) : R) * (1 + sR) ^ u else 0 := by
        intro L' hL'mem u hu
        by_cases hlt : L' < L
        · have heq := ih L' hlt hL'mem u hu
          rw [heq, sub_self, zpow_zero, Units.val_one, if_neg (Nat.ne_of_lt hlt)]
          exact ⟨isHighOrder_one L, by rw [PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hLpos)]⟩
        · have hle : L ≤ L' := by omega
          have hL'pos : 0 < L' := (Finset.mem_Icc.mp hL'mem).1
          have hU_eq : (Uneg L' u : PS) = 1 + psC (-((1 + sR) ^ u)) * w ^ L' := by
            rw [hUneg_val L' hL'pos u, map_neg]; ring
          have hhoU := isHighOrder_one_add_C_X_pow (R := R) hLpos hle (-((1 + sR) ^ u))
          rw [← hU_eq] at hhoU
          obtain ⟨hz1, hz2⟩ := isHighOrder_zpow hLpos (Uneg L' u) hhoU.1 (e false L' u - e true L' u)
          refine ⟨hz1, ?_⟩
          rw [hz2, hhoU.2]
          split_ifs with hEq
          · subst hEq; ring
          · ring
      have hinner_ho : ∀ L' ∈ Ls,
          IsHighOrder L (∏ u ∈ support L', (((Uneg L' u) ^ (e false L' u - e true L' u) : PSˣ) : PS)) ∧
          PowerSeries.coeff L (∏ u ∈ support L', (((Uneg L' u) ^ (e false L' u - e true L' u) : PSˣ) : PS)) =
            if L' = L then ∑ u ∈ support L, -((e false L u - e true L u : ℤ) : R) * (1 + sR) ^ u else 0 := by
        intro L' hL'mem
        obtain ⟨h1, h2⟩ := isHighOrder_prod hLpos (support L') _ (fun u hu => (hfac_ho L' hL'mem u hu).1)
        refine ⟨h1, ?_⟩
        rw [h2, Finset.sum_congr rfl (fun u hu => (hfac_ho L' hL'mem u hu).2)]
        split_ifs with hEq
        · subst hEq; rfl
        · simp
      have houter := isHighOrder_prod hLpos Ls _ (fun L' hL' => (hinner_ho L' hL').1)
      have hprod_one :
          (∏ L' ∈ Ls, ∏ u ∈ support L', (((Uneg L' u) ^ (e false L' u - e true L' u) : PSˣ) : PS)) = 1 := by
        have := congrArg (Units.val (α := PS)) hratio_one
        simp only [val_prod_units, Units.val_one] at this
        exact this
      have hcL := houter.2
      rw [hprod_one, PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hLpos)] at hcL
      rw [Finset.sum_congr rfl (fun L' hL' => (hinner_ho L' hL').2),
        Finset.sum_ite_eq' Ls L, if_pos hLmem] at hcL
      have hlin : ∑ u ∈ support L,
          truncMk d (Polynomial.C (-((e false L u - e true L u : ℤ) : ℚ))) * (1 + truncS d) ^ u = 0 := by
        convert hcL.symm using 2 with u
        simp only [map_neg, map_intCast, sR]
      have hzero := trunc_lin_indep (hsupp L) (fun u => -((e false L u - e true L u : ℤ) : ℚ)) hlin
      intro u hu
      have hqu := hzero u hu
      have hzi : (e false L u - e true L u : ℤ) = 0 := by exact_mod_cast (neg_eq_zero.mp hqu)
      omega
  intro U V hU hV
  have hne1 : ∀ L u, 0 < L → u ≤ L → (1 : ℚ) - U ^ u * V ^ (L - u) ≠ 0 := by
    intro L u hL hu
    have habs : |U ^ u * V ^ (L - u)| < 1 := by
      rw [abs_mul, abs_pow, abs_pow]
      have hU0 : 0 ≤ |U| := abs_nonneg U
      have hV0 : 0 ≤ |V| := abs_nonneg V
      have hVle : |V| ^ (L - u) ≤ 1 := pow_le_one₀ hV0 (le_of_lt hV)
      rcases Nat.eq_zero_or_pos u with rfl | hu0
      · simpa using pow_lt_one₀ hV0 hV (show L - 0 ≠ 0 by omega)
      · have hUlt : |U| ^ u < 1 := pow_lt_one₀ hU0 hU (Nat.ne_of_gt hu0)
        calc |U| ^ u * |V| ^ (L - u) ≤ |U| ^ u * 1 := mul_le_mul_of_nonneg_left hVle (pow_nonneg hU0 _)
          _ < 1 := by linarith
    intro heq
    have h1 : U ^ u * V ^ (L - u) = 1 := by linarith
    rw [h1] at habs
    norm_num at habs
  let Qneg : ℕ → ℕ → ℚˣ := fun L u =>
    if h : 0 < L ∧ u ≤ L then Units.mk0 (1 - U ^ u * V ^ (L - u)) (hne1 L u h.1 h.2) else 1
  have hQneg_val : ∀ L u, 0 < L → u ≤ L → (Qneg L u : ℚ) = 1 - U ^ u * V ^ (L - u) := by
    intro L u hL hu; simp [Qneg, hL, hu]
  have hQ_factor : ∀ j : Bool,
      ∏ i : Fin (m j), ((1 : ℚ) + (if s j i then (-1 : ℚ) else 1) * U ^ a j i * V ^ b j i) =
        ((∏ L ∈ Ls, ∏ u ∈ support L, (Qneg L u) ^ (e j L u) : ℚˣ) : ℚ) := by
    intro j
    rw [← prod_blocks_neg (a j) (b j) (s j) Ls support (hmemL j) (hS1 j) (hmem2L j) (hS2 j) Qneg]
    rw [val_prod_units]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hsi
    · rw [hQneg_val _ _ (hpos j i) (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; ring
    · rw [Units.val_mul]
      have h2pos : 0 < 2 * (a j i + b j i) := by have := hpos j i; omega
      have h2le : 2 * a j i ≤ 2 * (a j i + b j i) := by omega
      have hval1 : (Qneg (a j i + b j i) (a j i) : ℚ) = 1 - U ^ a j i * V ^ b j i := by
        rw [hQneg_val _ _ (hpos j i) (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      have hval2 : (Qneg (2 * (a j i + b j i)) (2 * a j i) : ℚ) =
          1 - U ^ (2 * a j i) * V ^ (2 * b j i) := by
        rw [hQneg_val _ _ h2pos h2le, show 2 * (a j i + b j i) - 2 * a j i = 2 * b j i by omega]
      apply mul_right_cancel₀ (Qneg (a j i + b j i) (a j i)).ne_zero
      have hinv : ((Qneg (a j i + b j i) (a j i))⁻¹ : ℚˣ).val * (Qneg (a j i + b j i) (a j i)).val = 1 :=
        (Qneg (a j i + b j i) (a j i)).inv_mul
      rw [mul_assoc (Qneg (2 * (a j i + b j i)) (2 * a j i) : ℚ), hinv, mul_one, hval1, hval2]
      rw [show 2 * a j i = a j i + a j i by omega, show 2 * b j i = b j i + b j i by omega,
        pow_add U, pow_add V]
      ring
  rw [hQ_factor false, hQ_factor true]
  congr 1
  refine Finset.prod_congr rfl fun L hL => Finset.prod_congr rfl fun u hu => ?_
  rw [he_eq L hL u hu]

set_option maxHeartbeats 800000 in
lemma recover_common_true {A B d : ℕ} {m : Bool → ℕ}
    (a b : (j : Bool) → Fin (m j) → ℕ) (s : (j : Bool) → Fin (m j) → Bool)
    (hpos : ∀ j i, 0 < a j i + b j i)
    (hleA : ∀ j i, a j i ≤ A) (hleB : ∀ j i, b j i ≤ B)
    (hcount : ∀ u v,
      (Finset.univ.filter (fun i : Fin (m false) => a false i = u ∧ b false i = v)).card =
      (Finset.univ.filter (fun i : Fin (m true) => a true i = u ∧ b true i = v)).card)
    (support : ℕ → Finset ℕ)
    (hS_le : ∀ L u, u ∈ support L → u ≤ L)
    (hS1 : ∀ j i, a j i ∈ support (a j i + b j i))
    (hsupp : ∀ L, (support L).card ≤ d + 1)
    (hFps :
      ∏ i : Fin (m false), (1 + (if s false i then (-1 : PowerSeries (TruncPoly d)) else 1) *
        PowerSeries.C ((1 + truncS d) ^ (a false i)) *
        (PowerSeries.X : PowerSeries (TruncPoly d)) ^ (a false i + b false i)) =
      ∏ i : Fin (m true), (1 + (if s true i then (-1 : PowerSeries (TruncPoly d)) else 1) *
        PowerSeries.C ((1 + truncS d) ^ (a true i)) *
        (PowerSeries.X : PowerSeries (TruncPoly d)) ^ (a true i + b true i))) :
    ∀ U V : ℚ, |U| < 1 → |V| < 1 →
      ∏ i : Fin (m false), ((1 : ℚ) + (if s false i then (-1 : ℚ) else 1) * U ^ a false i * V ^ b false i) =
      ∏ i : Fin (m true), ((1 : ℚ) + (if s true i then (-1 : ℚ) else 1) * U ^ a true i * V ^ b true i) := by
  classical
  let R := TruncPoly d
  let PS := PowerSeries R
  let sR : R := truncS d
  let w : PS := PowerSeries.X
  let psC : R →+* PS := PowerSeries.C (R := R)
  let Mmax := A + B
  let Ls := Finset.Icc 1 Mmax
  have hmemL : ∀ (j : Bool) (i : Fin (m j)), a j i + b j i ∈ Ls := fun j i =>
    Finset.mem_Icc.mpr ⟨hpos j i, by have := hleA j i; have := hleB j i; omega⟩
  let cMinus : Bool → ℕ → ℕ → ℕ := fun j L u =>
    (Finset.univ.filter (fun i : Fin (m j) => a j i = u ∧ a j i + b j i = L ∧ s j i = true)).card
  let cPlus : Bool → ℕ → ℕ → ℕ := fun j L u =>
    (Finset.univ.filter (fun i : Fin (m j) => a j i = u ∧ a j i + b j i = L ∧ s j i = false)).card
  have hsum_pm : ∀ L u, u ≤ L →
      cMinus false L u + cPlus false L u = cMinus true L u + cPlus true L u := by
    intro L u hu
    have hsplit : ∀ j : Bool, cMinus j L u + cPlus j L u =
        (Finset.univ.filter (fun i : Fin (m j) => a j i = u ∧ b j i = L - u)).card := by
      intro j
      dsimp only [cMinus, cPlus]
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext i
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases s j i <;> constructor <;> intro h <;> simp_all <;> omega
      · rw [Finset.disjoint_left]
        intro i h1 h2
        have h1' := (Finset.mem_filter.mp h1).2.2.2
        have h2' := (Finset.mem_filter.mp h2).2.2.2
        rw [h1'] at h2'; exact Bool.noConfusion h2'
    rw [hsplit false, hsplit true, hcount u (L - u)]
  let Uneg : ℕ → ℕ → PSˣ := fun L u =>
    if hL : 0 < L then
      unitOfConstOne (1 - psC ((1 + sR) ^ u) * w ^ L) (by simp [w, Nat.ne_of_gt hL])
    else 1
  let Upos : ℕ → ℕ → PSˣ := fun L u =>
    if hL : 0 < L then
      unitOfConstOne (1 + psC ((1 + sR) ^ u) * w ^ L) (by simp [w, Nat.ne_of_gt hL])
    else 1
  have hUneg_val : ∀ L, 0 < L → ∀ u, (Uneg L u : PS) = 1 - psC ((1 + sR) ^ u) * w ^ L := by
    intro L hL u; simp only [Uneg, dif_pos hL, unitOfConstOne_val]
  have hUpos_val : ∀ L, 0 < L → ∀ u, (Upos L u : PS) = 1 + psC ((1 + sR) ^ u) * w ^ L := by
    intro L hL u; simp only [Upos, dif_pos hL, unitOfConstOne_val]
  have hFps_unit : ∀ j : Bool,
      ((∏ L ∈ Ls, ∏ u ∈ support L,
        (Uneg L u) ^ (cMinus j L u) * (Upos L u) ^ (cPlus j L u) : PSˣ) : PS) =
      ∏ i : Fin (m j), (1 + (if s j i then (-1 : PS) else 1) *
        psC ((1 + sR) ^ (a j i)) * w ^ (a j i + b j i)) := by
    intro j
    rw [← prod_blocks_pm (a j) (b j) (s j) Ls support (hmemL j) (hS1 j) Uneg Upos]
    rw [val_prod_units]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hsi
    · rw [hUneg_val _ (hpos j i)]; ring
    · rw [hUpos_val _ (hpos j i)]; ring
  let Urat : ℕ → ℕ → PSˣ := fun L u => Uneg L u * (Upos L u)⁻¹
  let delta : ℕ → ℕ → ℤ := fun L u => (cMinus false L u : ℤ) - (cMinus true L u : ℤ)
  have hratio_one : (∏ L ∈ Ls, ∏ u ∈ support L, (Urat L u) ^ (delta L u) : PSˣ) = 1 := by
    have h1u : (∏ L ∈ Ls, ∏ u ∈ support L,
          (Uneg L u) ^ (cMinus false L u) * (Upos L u) ^ (cPlus false L u) : PSˣ) =
        (∏ L ∈ Ls, ∏ u ∈ support L,
          (Uneg L u) ^ (cMinus true L u) * (Upos L u) ^ (cPlus true L u) : PSˣ) := by
      apply Units.ext
      rw [hFps_unit false, hFps_unit true]
      exact hFps
    have h2 : (∏ L ∈ Ls, ∏ u ∈ support L, (Urat L u) ^ (delta L u) : PSˣ) =
        (∏ L ∈ Ls, ∏ u ∈ support L,
          (Uneg L u) ^ (cMinus false L u) * (Upos L u) ^ (cPlus false L u) : PSˣ) *
        (∏ L ∈ Ls, ∏ u ∈ support L,
          (Uneg L u) ^ (cMinus true L u) * (Upos L u) ^ (cPlus true L u) : PSˣ)⁻¹ := by
      refine eq_mul_inv_iff_mul_eq.mpr ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun L _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun u hu => ?_
      have huL : u ≤ L := hS_le L u hu
      have hsp := hsum_pm L u huL
      have hdp : (cPlus false L u : ℤ) - (cPlus true L u : ℤ) = -((cMinus false L u : ℤ) - (cMinus true L u : ℤ)) := by
        omega
      dsimp only [Urat, delta]
      have hinvp : (Upos L u)⁻¹ ^ ((cMinus false L u : ℤ) - (cMinus true L u : ℤ)) =
          (Upos L u) ^ ((cPlus false L u : ℤ) - (cPlus true L u : ℤ)) := by
        rw [hdp, zpow_neg, inv_zpow]
      calc (Uneg L u * (Upos L u)⁻¹) ^ ((cMinus false L u : ℤ) - (cMinus true L u : ℤ)) *
            (Uneg L u ^ cMinus true L u * Upos L u ^ cPlus true L u)
          = (Uneg L u ^ ((cMinus false L u : ℤ) - (cMinus true L u : ℤ)) *
              Uneg L u ^ (cMinus true L u : ℤ)) *
            (Upos L u ^ ((cPlus false L u : ℤ) - (cPlus true L u : ℤ)) *
              Upos L u ^ (cPlus true L u : ℤ)) := by
              rw [(Commute.all (Uneg L u) (Upos L u)⁻¹).mul_zpow, hinvp,
                zpow_natCast, zpow_natCast]
              apply Units.ext
              simp only [Units.val_mul]
              ring
        _ = Uneg L u ^ (cMinus false L u : ℤ) * Upos L u ^ (cPlus false L u : ℤ) := by
              rw [← zpow_add, ← zpow_add, sub_add_cancel, sub_add_cancel]
        _ = Uneg L u ^ cMinus false L u * Upos L u ^ cPlus false L u := by
              rw [zpow_natCast, zpow_natCast]
    rw [h2, h1u, mul_inv_cancel]
  have hdelta_zero : ∀ L ∈ Ls, ∀ u ∈ support L, delta L u = 0 := by
    intro L
    induction L using Nat.strong_induction_on with
    | ind L ih =>
      intro hLmem
      have hLpos : 0 < L := (Finset.mem_Icc.mp hLmem).1
      have hfac_ho : ∀ L' ∈ Ls, ∀ u ∈ support L',
          IsHighOrder L (((Urat L' u) ^ (delta L' u) : PSˣ) : PS) ∧
          PowerSeries.coeff L (((Urat L' u) ^ (delta L' u) : PSˣ) : PS) =
            if L' = L then -((2 * delta L u : ℤ) : R) * (1 + sR) ^ u else 0 := by
        intro L' hL'mem u hu
        by_cases hlt : L' < L
        · have heq := ih L' hlt hL'mem u hu
          rw [heq, zpow_zero, Units.val_one, if_neg (Nat.ne_of_lt hlt)]
          exact ⟨isHighOrder_one L, by rw [PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hLpos)]⟩
        · have hle : L ≤ L' := by omega
          have hL'pos : 0 < L' := (Finset.mem_Icc.mp hL'mem).1
          have hUn_eq : (Uneg L' u : PS) = 1 + psC (-((1 + sR) ^ u)) * w ^ L' := by
            rw [hUneg_val L' hL'pos u, map_neg]; ring
          have hUp_eq : (Upos L' u : PS) = 1 + psC ((1 + sR) ^ u) * w ^ L' := by
            rw [hUpos_val L' hL'pos u]
          have hhoN := isHighOrder_one_add_C_X_pow (R := R) hLpos hle (-((1 + sR) ^ u))
          have hhoP := isHighOrder_one_add_C_X_pow (R := R) hLpos hle ((1 + sR) ^ u)
          rw [← hUn_eq] at hhoN
          rw [← hUp_eq] at hhoP
          obtain ⟨hPi1, hPi2⟩ := isHighOrder_inv hLpos (Upos L' u) hhoP.1
          obtain ⟨hR1, hR2⟩ := isHighOrder_mul hhoN.1 hPi1 hLpos
          have hRval : (Urat L' u : PS) = (Uneg L' u : PS) * (((Upos L' u)⁻¹ : PSˣ) : PS) := rfl
          rw [← hRval] at hR1 hR2
          obtain ⟨hz1, hz2⟩ := isHighOrder_zpow hLpos (Urat L' u) hR1 (delta L' u)
          refine ⟨hz1, ?_⟩
          rw [hz2, hR2, hhoN.2, hPi2, hhoP.2]
          split_ifs with hEq
          · subst hEq; push_cast; ring
          · ring
      have hinner_ho : ∀ L' ∈ Ls,
          IsHighOrder L (∏ u ∈ support L', (((Urat L' u) ^ (delta L' u) : PSˣ) : PS)) ∧
          PowerSeries.coeff L (∏ u ∈ support L', (((Urat L' u) ^ (delta L' u) : PSˣ) : PS)) =
            if L' = L then ∑ u ∈ support L, -((2 * delta L u : ℤ) : R) * (1 + sR) ^ u else 0 := by
        intro L' hL'mem
        obtain ⟨h1, h2⟩ := isHighOrder_prod hLpos (support L') _ (fun u hu => (hfac_ho L' hL'mem u hu).1)
        refine ⟨h1, ?_⟩
        rw [h2, Finset.sum_congr rfl (fun u hu => (hfac_ho L' hL'mem u hu).2)]
        split_ifs with hEq
        · subst hEq; rfl
        · simp
      have houter := isHighOrder_prod hLpos Ls _ (fun L' hL' => (hinner_ho L' hL').1)
      have hprod_one :
          (∏ L' ∈ Ls, ∏ u ∈ support L', (((Urat L' u) ^ (delta L' u) : PSˣ) : PS)) = 1 := by
        have := congrArg (Units.val (α := PS)) hratio_one
        simp only [val_prod_units, Units.val_one] at this
        exact this
      have hcL := houter.2
      rw [hprod_one, PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hLpos)] at hcL
      rw [Finset.sum_congr rfl (fun L' hL' => (hinner_ho L' hL').2),
        Finset.sum_ite_eq' Ls L, if_pos hLmem] at hcL
      have hlin : ∑ u ∈ support L,
          truncMk d (Polynomial.C (-((2 * delta L u : ℤ) : ℚ))) * (1 + truncS d) ^ u = 0 := by
        convert hcL.symm using 2 with u
        simp only [map_neg, map_intCast, sR]
      have hzero := trunc_lin_indep (hsupp L) (fun u => -((2 * delta L u : ℤ) : ℚ)) hlin
      intro u hu
      have hqu := hzero u hu
      have hzi : (2 * delta L u : ℤ) = 0 := by exact_mod_cast (neg_eq_zero.mp hqu)
      omega
  intro U V hU hV
  have hne_pm : ∀ (sg : Bool) (L u : ℕ), 0 < L → u ≤ L →
      (1 : ℚ) + (if sg then (-1 : ℚ) else 1) * U ^ u * V ^ (L - u) ≠ 0 := by
    intro sg L u hL hu
    have habs : |U ^ u * V ^ (L - u)| < 1 := by
      rw [abs_mul, abs_pow, abs_pow]
      have hU0 : 0 ≤ |U| := abs_nonneg U
      have hV0 : 0 ≤ |V| := abs_nonneg V
      have hVle : |V| ^ (L - u) ≤ 1 := pow_le_one₀ hV0 (le_of_lt hV)
      rcases Nat.eq_zero_or_pos u with rfl | hu0
      · simpa using pow_lt_one₀ hV0 hV (show L - 0 ≠ 0 by omega)
      · have hUlt : |U| ^ u < 1 := pow_lt_one₀ hU0 hU (Nat.ne_of_gt hu0)
        calc |U| ^ u * |V| ^ (L - u) ≤ |U| ^ u * 1 := mul_le_mul_of_nonneg_left hVle (pow_nonneg hU0 _)
          _ < 1 := by linarith
    have hlt1 := (abs_lt.mp habs).2
    have hgt1 := (abs_lt.mp habs).1
    cases sg <;> simp <;> linarith
  let Qneg : ℕ → ℕ → ℚˣ := fun L u =>
    if h : 0 < L ∧ u ≤ L then
      Units.mk0 (1 + (-1 : ℚ) * U ^ u * V ^ (L - u)) (hne_pm true L u h.1 h.2)
    else 1
  let Qpos : ℕ → ℕ → ℚˣ := fun L u =>
    if h : 0 < L ∧ u ≤ L then
      Units.mk0 (1 + (1 : ℚ) * U ^ u * V ^ (L - u)) (hne_pm false L u h.1 h.2)
    else 1
  have hQ_factor : ∀ j : Bool,
      ∏ i : Fin (m j), ((1 : ℚ) + (if s j i then (-1 : ℚ) else 1) * U ^ a j i * V ^ b j i) =
        ((∏ L ∈ Ls, ∏ u ∈ support L,
          (Qneg L u) ^ (cMinus j L u) * (Qpos L u) ^ (cPlus j L u) : ℚˣ) : ℚ) := by
    intro j
    rw [← prod_blocks_pm (a j) (b j) (s j) Ls support (hmemL j) (hS1 j) Qneg Qpos]
    rw [val_prod_units]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hsi
    · simp [Qneg, hpos j i, Nat.le_add_right, Nat.add_sub_cancel_left]
    · simp [Qpos, hpos j i, Nat.le_add_right, Nat.add_sub_cancel_left]
  rw [hQ_factor false, hQ_factor true]
  congr 1
  refine Finset.prod_congr rfl fun L hL => Finset.prod_congr rfl fun u hu => ?_
  have hd := hdelta_zero L hL u hu
  have hcm : cMinus false L u = cMinus true L u := by dsimp only [delta] at hd; omega
  have huL : u ≤ L := hS_le L u hu
  have hcp : cPlus false L u = cPlus true L u := by
    have := hsum_pm L u huL; omega
  rw [hcm, hcp]

end PEqualNP.Outside.L_lib_920_aux

set_option maxHeartbeats 800000 in
open PEqualNP.Outside.L_lib_920_aux in
theorem PEqualNP.Outside.L_lib_920 : (∀ (A B d : ℕ) (common : Bool) (m f : Bool → ℕ)
  (red : (j : Bool) → Fin A → Fin (m j)) (blue : (j : Bool) → Fin B → Fin (m j))
  (s : (j : Bool) → Fin (m j) → Bool),
  let a := fun (j : Bool) (i : Fin (m j)) =>
    (Finset.univ.filter (fun h : Fin A => red j h = i)).card
  let b := fun (j : Bool) (i : Fin (m j)) =>
    (Finset.univ.filter (fun h : Fin B => blue j h = i)).card
  (∀ j i, 0 < a j i + b j i) →
  let X := (Fin A → Bool) × (Fin B → Bool)
  let hist := fun (j : Bool) (u v : ℕ) =>
    2^(f j) * ((Finset.univ : Finset X).filter (fun x =>
      (Finset.univ.filter (fun h : Fin A => x.1 h = true)).card = u ∧
      (Finset.univ.filter (fun h : Fin B => x.2 h = true)).card = v ∧
      ∀ i : Fin (m j),
        ((Finset.univ.filter (fun h : Fin A => red j h = i ∧ x.1 h = true)).card +
         (Finset.univ.filter (fun h : Fin B => blue j h = i ∧ x.2 h = true)).card) % 2 =
        (s j i).toNat)).card
  let count := fun (j : Bool) (u v : ℕ) =>
    (Finset.univ.filter (fun i : Fin (m j) => a j i = u ∧ b j i = v)).card
  (common = true → ∀ u v, count false u v = count true u v) →
  let support := fun (L : ℕ) => (Finset.range (L+1)).filter (fun u =>
    ∃ j : Bool, ∃ i : Fin (m j),
      (a j i = u ∧ a j i + b j i = L) ∨
      (common = false ∧ s j i = false ∧ 2*a j i = u ∧ 2*(a j i + b j i) = L))
  (∀ L, (support L).card ≤ d+1) →
  let moment := fun (j : Bool) (h L : ℕ) =>
    ∑ u ∈ Finset.range (A+1), if u ≤ L then Nat.choose u h * hist j u (L-u) else 0
  (∀ u v, hist false u v = hist true u v) ↔
    ∀ h, h ≤ d → ∀ L, moment false h L = moment true h L) := by
  classical
  intro A B d common m f red blue s a b hpos X hist count hcommon support hsupp moment
  constructor
  · intro heq h _ L
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> simp [heq]
  · intro hmom
    have hsumA : ∀ j : Bool, ∑ i : Fin (m j), a j i = A := fun j => fiber_card_sum (red j)
    have hsumB : ∀ j : Bool, ∑ i : Fin (m j), b j i = B := fun j => fiber_card_sum (blue j)
    have hleA : ∀ j i, a j i ≤ A := fun j i => le_trans (Finset.card_filter_le _ _) (by simp)
    have hleB : ∀ j i, b j i ≤ B := fun j i => le_trans (Finset.card_filter_le _ _) (by simp)
    have hhist0A : ∀ j u v, A < u → hist j u v = 0 := by
      intro j u v hu
      simp only [hist, mul_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      right
      intro x _ hx
      have hle : (Finset.univ.filter (fun h : Fin A => x.1 h = true)).card ≤ A :=
        le_trans (Finset.card_filter_le _ _) (by simp)
      omega
    have hhist0B : ∀ j u v, B < v → hist j u v = 0 := by
      intro j u v hv
      simp only [hist, mul_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      right
      intro x _ hx
      have hle : (Finset.univ.filter (fun h : Fin B => x.2 h = true)).card ≤ B :=
        le_trans (Finset.card_filter_le _ _) (by simp)
      omega
    let R := TruncPoly d
    let PS := PowerSeries R
    let sR : R := truncS d
    let w : PS := PowerSeries.X
    let psC : R →+* PS := PowerSeries.C (R := R)
    have hU1c : PowerSeries.constantCoeff (1 + w) = 1 := by simp [w]
    have hV1c : PowerSeries.constantCoeff (1 - w) = 1 := by simp [w]
    have hU2c : PowerSeries.constantCoeff (1 + psC (1 + sR) * w) = 1 := by simp [w]
    have hV2c : PowerSeries.constantCoeff (1 - psC (1 + sR) * w) = 1 := by simp [w]
    let U1 : PSˣ := unitOfConstOne (1 + w) hU1c
    let V1 : PSˣ := unitOfConstOne (1 - w) hV1c
    let U2 : PSˣ := unitOfConstOne (1 + psC (1 + sR) * w) hU2c
    let V2 : PSˣ := unitOfConstOne (1 - psC (1 + sR) * w) hV2c
    have hU1v : (U1 : PS) = 1 + w := unitOfConstOne_val _ _
    have hV1v : (V1 : PS) = 1 - w := unitOfConstOne_val _ _
    have hU2v : (U2 : PS) = 1 + psC (1 + sR) * w := unitOfConstOne_val _ _
    have hV2v : (V2 : PS) = 1 - psC (1 + sR) * w := unitOfConstOne_val _ _
    let Xps : PS := (V2 : PS) * ((U2⁻¹ : PSˣ) : PS)
    let Yps : PS := (V1 : PS) * ((U1⁻¹ : PSˣ) : PS)
    let UY : PSˣ := V1 * U1⁻¹
    have hUYv : (UY : PS) = Yps := rfl
    let tps : PS := (Xps - Yps) * ((UY⁻¹ : PSˣ) : PS)
    have hXeq : Xps = Yps * (1 + tps) := by
      have h1 : Yps * tps = Xps - Yps := by
        calc Yps * tps = (UY : PS) * ((Xps - Yps) * ((UY⁻¹ : PSˣ) : PS)) := rfl
          _ = (Xps - Yps) * ((UY : PS) * ((UY⁻¹ : PSˣ) : PS)) := by ring
          _ = Xps - Yps := by rw [UY.mul_inv, mul_one]
      calc Xps = Yps + (Xps - Yps) := by ring
        _ = Yps + Yps * tps := by rw [h1]
        _ = Yps * (1 + tps) := by ring
    have hXYsub : Xps - Yps = psC sR * (-2 * w * ((U1⁻¹ : PSˣ) : PS) * ((U2⁻¹ : PSˣ) : PS)) := by
      have hmul : (Xps - Yps) * ((U1 : PS) * (U2 : PS)) = -2 * psC sR * w := by
        dsimp only [Xps, Yps]
        have h1 : (V2 : PS) * ((U2⁻¹ : PSˣ) : PS) * ((U1 : PS) * (U2 : PS)) = (V2 : PS) * (U1 : PS) := by
          calc (V2 : PS) * ((U2⁻¹ : PSˣ) : PS) * ((U1 : PS) * (U2 : PS))
              = (V2 : PS) * (U1 : PS) * (((U2⁻¹ : PSˣ) : PS) * (U2 : PS)) := by ring
            _ = (V2 : PS) * (U1 : PS) := by rw [U2.inv_mul, mul_one]
        have h2 : (V1 : PS) * ((U1⁻¹ : PSˣ) : PS) * ((U1 : PS) * (U2 : PS)) = (V1 : PS) * (U2 : PS) := by
          calc (V1 : PS) * ((U1⁻¹ : PSˣ) : PS) * ((U1 : PS) * (U2 : PS))
              = (V1 : PS) * (U2 : PS) * (((U1⁻¹ : PSˣ) : PS) * (U1 : PS)) := by ring
            _ = (V1 : PS) * (U2 : PS) := by rw [U1.inv_mul, mul_one]
        rw [sub_mul, h1, h2, hU1v, hV1v, hU2v, hV2v, map_add, map_one]
        ring
      calc Xps - Yps
          = (Xps - Yps) * ((U1 : PS) * (U2 : PS)) * (((U1⁻¹ : PSˣ) : PS) * ((U2⁻¹ : PSˣ) : PS)) := by
              calc Xps - Yps = (Xps - Yps) * 1 * 1 := by ring
                _ = (Xps - Yps) * ((U1 : PS) * ((U1⁻¹ : PSˣ) : PS)) *
                      ((U2 : PS) * ((U2⁻¹ : PSˣ) : PS)) := by rw [U1.mul_inv, U2.mul_inv]
                _ = _ := by ring
        _ = (-2 * psC sR * w) * (((U1⁻¹ : PSˣ) : PS) * ((U2⁻¹ : PSˣ) : PS)) := by rw [hmul]
        _ = psC sR * (-2 * w * ((U1⁻¹ : PSˣ) : PS) * ((U2⁻¹ : PSˣ) : PS)) := by ring
    have htpow : tps ^ (d + 1) = 0 := by
      dsimp only [tps]
      rw [hXYsub, mul_assoc, mul_pow, ← map_pow, truncS_pow_eq_zero, map_zero, zero_mul]
    let Hps : Bool → PS := fun j =>
      ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
        (hist j u v : PS) * Xps ^ u * Yps ^ v
    have hHps_eq : Hps false = Hps true := by
      dsimp only [Hps]
      rw [hXeq]
      rw [genfun_moment_expansion (hist false) (hhist0B false) Yps tps htpow,
          genfun_moment_expansion (hist true) (hhist0B true) Yps tps htpow]
      refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun L _ => ?_
      have hhd : h ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
      exact congrArg (fun n : ℕ => (n : PS) * Yps ^ L * tps ^ h) (hmom h hhd L)
    have h1pX : 1 + Xps = 2 * ((U2⁻¹ : PSˣ) : PS) := by
      dsimp only [Xps]
      calc 1 + (V2 : PS) * ((U2⁻¹ : PSˣ) : PS)
          = ((U2 : PS) + (V2 : PS)) * ((U2⁻¹ : PSˣ) : PS) := by rw [add_mul, U2.mul_inv]
        _ = 2 * ((U2⁻¹ : PSˣ) : PS) := by rw [hU2v, hV2v]; ring
    have h1mX : 1 - Xps = 2 * psC (1 + sR) * w * ((U2⁻¹ : PSˣ) : PS) := by
      dsimp only [Xps]
      calc 1 - (V2 : PS) * ((U2⁻¹ : PSˣ) : PS)
          = ((U2 : PS) - (V2 : PS)) * ((U2⁻¹ : PSˣ) : PS) := by rw [sub_mul, U2.mul_inv]
        _ = 2 * psC (1 + sR) * w * ((U2⁻¹ : PSˣ) : PS) := by rw [hU2v, hV2v]; ring
    have h1pY : 1 + Yps = 2 * ((U1⁻¹ : PSˣ) : PS) := by
      dsimp only [Yps]
      calc 1 + (V1 : PS) * ((U1⁻¹ : PSˣ) : PS)
          = ((U1 : PS) + (V1 : PS)) * ((U1⁻¹ : PSˣ) : PS) := by rw [add_mul, U1.mul_inv]
        _ = 2 * ((U1⁻¹ : PSˣ) : PS) := by rw [hU1v, hV1v]; ring
    have h1mY : 1 - Yps = 2 * w * ((U1⁻¹ : PSˣ) : PS) := by
      dsimp only [Yps]
      calc 1 - (V1 : PS) * ((U1⁻¹ : PSˣ) : PS)
          = ((U1 : PS) - (V1 : PS)) * ((U1⁻¹ : PSˣ) : PS) := by rw [sub_mul, U1.mul_inv]
        _ = 2 * w * ((U1⁻¹ : PSˣ) : PS) := by rw [hU1v, hV1v]; ring
    let Fps : Bool → PS := fun j =>
      ∏ i : Fin (m j), (1 + (if s j i then (-1 : PS) else 1) *
        psC ((1 + sR) ^ (a j i)) * w ^ (a j i + b j i))
    have hHps_prod : ∀ j : Bool,
        (2 : PS) ^ (m j) * Hps j =
          (2 : PS) ^ (f j + A + B) * ((U2⁻¹ : PSˣ) : PS) ^ A * ((U1⁻¹ : PSˣ) : PS) ^ B * Fps j := by
      intro j
      have hg := hist_genfun_ring (K := PS) (f := f j) (red j) (blue j) (s j) Xps Yps
      dsimp only at hg
      dsimp only [Hps]
      rw [hg]
      have hfac : ∀ i : Fin (m j),
          (1 + Xps) ^ a j i * (1 + Yps) ^ b j i +
            (if s j i then (-1 : PS) else 1) * (1 - Xps) ^ a j i * (1 - Yps) ^ b j i =
          ((2 : PS) ^ a j i * (2 : PS) ^ b j i *
            ((U2⁻¹ : PSˣ) : PS) ^ a j i * ((U1⁻¹ : PSˣ) : PS) ^ b j i) *
            (1 + (if s j i then (-1 : PS) else 1) *
              psC ((1 + sR) ^ (a j i)) * w ^ (a j i + b j i)) := by
        intro i
        rw [h1pX, h1mX, h1pY, h1mY, map_pow, pow_add w]
        simp only [mul_pow]
        ring
      have hprod_eq :
          ∏ i : Fin (m j), ((1 + Xps) ^ a j i * (1 + Yps) ^ b j i +
            (if s j i then (-1 : PS) else 1) * (1 - Xps) ^ a j i * (1 - Yps) ^ b j i) =
          (2 : PS) ^ A * (2 : PS) ^ B * ((U2⁻¹ : PSˣ) : PS) ^ A * ((U1⁻¹ : PSˣ) : PS) ^ B * Fps j := by
        rw [Finset.prod_congr rfl (fun i _ => hfac i)]
        simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsumA j, hsumB j]
        rfl
      change (2 : PS) ^ f j * ∏ i : Fin (m j), ((1 + Xps) ^ a j i * (1 + Yps) ^ b j i +
        (if s j i then (-1 : PS) else 1) * (1 - Xps) ^ a j i * (1 - Yps) ^ b j i) = _
      rw [hprod_eq, pow_add (2 : PS) (f j + A) B, pow_add (2 : PS) (f j) A]
      ring
    have hscale_eq :
        (2 : PS) ^ (m true + f false + A + B) * Fps false =
        (2 : PS) ^ (m false + f true + A + B) * Fps true := by
      have h1 : (2 : PS) ^ (m true) * ((2 : PS) ^ (m false) * Hps false) =
          (2 : PS) ^ (m false) * ((2 : PS) ^ (m true) * Hps true) := by
        rw [hHps_eq]; ring
      rw [hHps_prod false, hHps_prod true] at h1
      have h2 := congrArg (fun z : PS => z * ((U2 : PS) ^ A * (U1 : PS) ^ B)) h1
      have hc2 : ∀ z : PS, z * ((U2⁻¹ : PSˣ) : PS) ^ A * ((U1⁻¹ : PSˣ) : PS) ^ B *
          ((U2 : PS) ^ A * (U1 : PS) ^ B) = z := by
        intro z
        calc z * ((U2⁻¹ : PSˣ) : PS) ^ A * ((U1⁻¹ : PSˣ) : PS) ^ B * ((U2 : PS) ^ A * (U1 : PS) ^ B)
            = z * ((((U2⁻¹ : PSˣ) : PS) * (U2 : PS)) ^ A * (((U1⁻¹ : PSˣ) : PS) * (U1 : PS)) ^ B) := by
                simp only [mul_pow]; ring
          _ = z := by rw [U2.inv_mul, U1.inv_mul, one_pow, one_pow, mul_one, mul_one]
      have hL : (2 : PS) ^ m true *
            ((2 : PS) ^ (f false + A + B) * ((U2⁻¹ : PSˣ) : PS) ^ A *
              ((U1⁻¹ : PSˣ) : PS) ^ B * Fps false) * ((U2 : PS) ^ A * (U1 : PS) ^ B) =
          (2 : PS) ^ (m true + f false + A + B) * Fps false := by
        calc _ = ((2 : PS) ^ m true * (2 : PS) ^ (f false + A + B) * Fps false) *
              ((U2⁻¹ : PSˣ) : PS) ^ A * ((U1⁻¹ : PSˣ) : PS) ^ B * ((U2 : PS) ^ A * (U1 : PS) ^ B) := by ring
          _ = (2 : PS) ^ m true * (2 : PS) ^ (f false + A + B) * Fps false := hc2 _
          _ = (2 : PS) ^ (m true + (f false + A + B)) * Fps false := by
              rw [← pow_add (2 : PS) (m true) (f false + A + B)]
          _ = (2 : PS) ^ (m true + f false + A + B) * Fps false := by
              congr 2; omega
      have hR : (2 : PS) ^ m false *
            ((2 : PS) ^ (f true + A + B) * ((U2⁻¹ : PSˣ) : PS) ^ A *
              ((U1⁻¹ : PSˣ) : PS) ^ B * Fps true) * ((U2 : PS) ^ A * (U1 : PS) ^ B) =
          (2 : PS) ^ (m false + f true + A + B) * Fps true := by
        calc _ = ((2 : PS) ^ m false * (2 : PS) ^ (f true + A + B) * Fps true) *
              ((U2⁻¹ : PSˣ) : PS) ^ A * ((U1⁻¹ : PSˣ) : PS) ^ B * ((U2 : PS) ^ A * (U1 : PS) ^ B) := by ring
          _ = (2 : PS) ^ m false * (2 : PS) ^ (f true + A + B) * Fps true := hc2 _
          _ = (2 : PS) ^ (m false + (f true + A + B)) * Fps true := by
              rw [← pow_add (2 : PS) (m false) (f true + A + B)]
          _ = (2 : PS) ^ (m false + f true + A + B) * Fps true := by
              congr 2; omega
      rw [hL, hR] at h2
      exact h2
    have hFps_c0 : ∀ j : Bool, PowerSeries.constantCoeff (Fps j) = 1 := by
      intro j
      dsimp only [Fps]
      rw [map_prod]
      refine Finset.prod_eq_one fun i _ => ?_
      have hpi : a j i + b j i ≠ 0 := Nat.ne_of_gt (hpos j i)
      rw [map_add, map_one, map_mul, map_pow (PowerSeries.constantCoeff (R := R)) w,
        PowerSeries.constantCoeff_X, zero_pow hpi, mul_zero, add_zero]
    have hpow_nat : m true + f false = m false + f true := by
      have hc := congrArg (PowerSeries.constantCoeff (R := R)) hscale_eq
      rw [map_mul, map_mul, hFps_c0 false, hFps_c0 true, mul_one, mul_one, map_pow, map_pow] at hc
      have h2eq : ∀ n : ℕ, (PowerSeries.constantCoeff (2 : PS)) ^ n =
          truncMk d (Polynomial.C ((2 : ℚ) ^ n)) := by
        intro n
        rw [map_ofNat, map_pow, map_pow, map_ofNat, map_ofNat]
      rw [h2eq, h2eq] at hc
      have hq : (2 : ℚ) ^ (m true + f false + A + B) = (2 : ℚ) ^ (m false + f true + A + B) :=
        truncMk_C_injective d hc
      have hnat : (2 : ℕ) ^ (m true + f false + A + B) = (2 : ℕ) ^ (m false + f true + A + B) := by
        exact_mod_cast hq
      have hinj := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hnat
      omega
    have hFps_eq : Fps false = Fps true := by
      have h2unit : IsUnit (2 : PS) := by
        rw [PowerSeries.isUnit_iff_constantCoeff]
        have h2c : PowerSeries.constantCoeff (2 : PS) = ((truncMk d).comp Polynomial.C) (2 : ℚ) := by
          simp only [RingHom.comp_apply, map_ofNat]
        rw [h2c]
        exact (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℚ) ≠ 0)).map ((truncMk d).comp Polynomial.C)
      have hpowU : IsUnit ((2 : PS) ^ (m true + f false + A + B)) := h2unit.pow _
      have hexp : m false + f true + A + B = m true + f false + A + B := by omega
      rw [hexp] at hscale_eq
      exact hpowU.mul_left_cancel hscale_eq
    have hfinish : (∀ x y : ℚ, 0 < x → 0 < y →
        ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
          (hist false u v : ℚ) * x ^ u * y ^ v =
        ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
          (hist true u v : ℚ) * x ^ u * y ^ v) →
        ∀ u v, hist false u v = hist true u v := by
      intro hrat u v
      by_cases hu : u ≤ A
      · by_cases hv : v ≤ B
        · exact_mod_cast bivar_poly_eq_of_pos_rat
            (fun u v => (hist false u v : ℚ)) (fun u v => (hist true u v : ℚ)) hrat u hu v hv
        · rw [hhist0B false u v (by omega), hhist0B true u v (by omega)]
      · rw [hhist0A false u v (by omega), hhist0A true u v (by omega)]
    have hfrom_UV : (∀ U V : ℚ, |U| < 1 → |V| < 1 →
        ∏ i : Fin (m false), ((1 : ℚ) + (if s false i then (-1 : ℚ) else 1) * U ^ a false i * V ^ b false i) =
        ∏ i : Fin (m true), ((1 : ℚ) + (if s true i then (-1 : ℚ) else 1) * U ^ a true i * V ^ b true i)) →
        ∀ u v, hist false u v = hist true u v := by
      intro hUV
      refine hfinish fun x y hx hy => ?_
      have hx1 : (1 + x : ℚ) ≠ 0 := by linarith
      have hy1 : (1 + y : ℚ) ≠ 0 := by linarith
      let U : ℚ := (1 - x) / (1 + x)
      let V : ℚ := (1 - y) / (1 + y)
      have hUabs : |U| < 1 := by
        rw [abs_lt]; constructor <;> [rw [lt_div_iff₀ (by linarith)]; rw [div_lt_iff₀ (by linarith)]] <;> linarith
      have hVabs : |V| < 1 := by
        rw [abs_lt]; constructor <;> [rw [lt_div_iff₀ (by linarith)]; rw [div_lt_iff₀ (by linarith)]] <;> linarith
      have hP := hUV U V hUabs hVabs
      have hg0 : (2 : ℚ) ^ m false * ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
          (hist false u v : ℚ) * x ^ u * y ^ v =
          (2 : ℚ) ^ f false * ∏ i : Fin (m false), ((1 + x) ^ a false i * (1 + y) ^ b false i +
            (if s false i then (-1 : ℚ) else 1) * (1 - x) ^ a false i * (1 - y) ^ b false i) :=
        hist_genfun_ring (K := ℚ) (f := f false) (red false) (blue false) (s false) x y
      have hg1 : (2 : ℚ) ^ m true * ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1),
          (hist true u v : ℚ) * x ^ u * y ^ v =
          (2 : ℚ) ^ f true * ∏ i : Fin (m true), ((1 + x) ^ a true i * (1 + y) ^ b true i +
            (if s true i then (-1 : ℚ) else 1) * (1 - x) ^ a true i * (1 - y) ^ b true i) :=
        hist_genfun_ring (K := ℚ) (f := f true) (red true) (blue true) (s true) x y
      have hrew : ∀ j : Bool,
          ∏ i : Fin (m j), ((1 + x) ^ a j i * (1 + y) ^ b j i +
            (if s j i then (-1 : ℚ) else 1) * (1 - x) ^ a j i * (1 - y) ^ b j i) =
          (1 + x) ^ A * (1 + y) ^ B *
            ∏ i : Fin (m j), ((1 : ℚ) + (if s j i then (-1 : ℚ) else 1) * U ^ a j i * V ^ b j i) := by
        intro j
        have h1 : ∀ i : Fin (m j),
            (1 + x) ^ a j i * (1 + y) ^ b j i +
              (if s j i then (-1 : ℚ) else 1) * (1 - x) ^ a j i * (1 - y) ^ b j i =
            ((1 + x) ^ a j i * (1 + y) ^ b j i) *
              ((1 : ℚ) + (if s j i then (-1 : ℚ) else 1) * U ^ a j i * V ^ b j i) := by
          intro i
          dsimp only [U, V]
          rw [div_pow, div_pow]
          field_simp [hx1, hy1]
        simp_rw [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsumA j, hsumB j]
      rw [hrew false] at hg0
      rw [hrew true] at hg1
      have h2ne : (2 : ℚ) ^ (m false + m true) ≠ 0 := by positivity
      apply mul_left_cancel₀ h2ne
      calc (2 : ℚ) ^ (m false + m true) *
              ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1), (hist false u v : ℚ) * x ^ u * y ^ v
          = (2 : ℚ) ^ m true * ((2 : ℚ) ^ m false *
              ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1), (hist false u v : ℚ) * x ^ u * y ^ v) := by
              rw [pow_add]; ring
        _ = (2 : ℚ) ^ (m true + f false) * ((1 + x) ^ A * (1 + y) ^ B *
              ∏ i : Fin (m false), (1 + (if s false i then (-1 : ℚ) else 1) * U ^ a false i * V ^ b false i)) := by
              rw [hg0, pow_add]; ring
        _ = (2 : ℚ) ^ (m false + f true) * ((1 + x) ^ A * (1 + y) ^ B *
              ∏ i : Fin (m true), (1 + (if s true i then (-1 : ℚ) else 1) * U ^ a true i * V ^ b true i)) := by
              rw [hpow_nat, hP]
        _ = (2 : ℚ) ^ m false * ((2 : ℚ) ^ m true *
              ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1), (hist true u v : ℚ) * x ^ u * y ^ v) := by
              rw [hg1, pow_add]; ring
        _ = (2 : ℚ) ^ (m false + m true) *
              ∑ u ∈ Finset.range (A + 1), ∑ v ∈ Finset.range (B + 1), (hist true u v : ℚ) * x ^ u * y ^ v := by
              rw [pow_add]; ring
    have hS1 : ∀ j i, a j i ∈ support (a j i + b j i) := by
      intro j i
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, j, i, Or.inl ⟨rfl, rfl⟩⟩
    have hS_le : ∀ L u, u ∈ support L → u ≤ L := by
      intro L u hu
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hu).1)
    cases hcom : common with
    | false =>
      have hS2 : ∀ j i, s j i = false → 2 * a j i ∈ support (2 * (a j i + b j i)) := by
        intro j i hsi
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, j, i, Or.inr ⟨hcom, hsi, rfl, rfl⟩⟩
      exact hfrom_UV (recover_common_false a b s hpos hleA hleB support hS1 hS2 hsupp hFps_eq)
    | true =>
      exact hfrom_UV (recover_common_true a b s hpos hleA hleB (hcommon hcom) support hS_le hS1 hsupp hFps_eq)
