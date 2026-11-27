import PEqualNP.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PEqualNP.Outside.L_lib_520_aux

private noncomputable def chi (m : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (((2 * Real.pi * (k : ℝ) / (m : ℝ) : ℝ) : ℂ) * Complex.I)

private theorem norm_chi (m : ℕ) (k : ℤ) : ‖chi m k‖ = 1 := by
  unfold chi
  exact Complex.norm_exp_ofReal_mul_I _

private theorem chi_zero (m : ℕ) : chi m 0 = 1 := by
  simp [chi]

private theorem chi_add (m : ℕ) (a b : ℤ) : chi m (a + b) = chi m a * chi m b := by
  unfold chi
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem chi_neg (m : ℕ) (a : ℤ) : star (chi m a) = chi m (-a) := by
  unfold chi
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem chi_nat_mul (m a : ℕ) (b : ℤ) : chi m ((a : ℤ) * b) = (chi m b) ^ a := by
  induction a with
  | zero => simp [chi_zero]
  | succ a ih =>
    rw [Nat.cast_succ, add_mul, one_mul, chi_add, ih, pow_succ]

private theorem chi_eq_one_of_dvd (m : ℕ) (hm : 1 ≤ m) (d : ℤ) (hd : (m : ℤ) ∣ d) :
    chi m d = 1 := by
  rcases hd with ⟨q, rfl⟩
  unfold chi
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h1 : (2 * Real.pi * ((m * q : ℤ) : ℝ) / (m : ℝ)) = (q : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp [hm0]
  rw [h1]
  have h2 : (((q : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I =
      (q : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h2]
  exact Complex.exp_int_mul_two_pi_mul_I q

private theorem dvd_of_chi_eq_one (m : ℕ) (hm : 1 ≤ m) (d : ℤ) (h : chi m d = 1) :
    (m : ℤ) ∣ d := by
  have hdm : (m : ℤ) * (d / (m : ℤ)) + d % (m : ℤ) = d := Int.mul_ediv_add_emod d (m : ℤ)
  have hrem_chi : chi m (d % (m : ℤ)) = 1 := by
    have h1 : chi m ((m : ℤ) * (d / (m : ℤ)) + d % (m : ℤ)) = 1 := by rw [hdm]; exact h
    rw [chi_add, chi_eq_one_of_dvd m hm _ (dvd_mul_right (m : ℤ) _), one_mul] at h1
    exact h1
  set rem := d % (m : ℤ)
  have hrem_nn : 0 ≤ rem := Int.emod_nonneg d (by omega)
  have hrem_lt : rem < (m : ℤ) := Int.emod_lt_of_pos d (by omega)
  by_cases h0 : rem = 0
  · exact Int.dvd_of_emod_eq_zero h0
  · exfalso
    have hrem_pos : 0 < rem := by omega
    unfold chi at hrem_chi
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hrem_chi
    have hre := congrArg Complex.re hrem_chi
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re] at hre
    set θ : ℝ := 2 * Real.pi * (rem : ℝ) / (m : ℝ)
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hrem_rpos : (0 : ℝ) < (rem : ℝ) := by exact_mod_cast hrem_pos
    have hrem_rlt : (rem : ℝ) < (m : ℝ) := by exact_mod_cast hrem_lt
    have hθ_pos : 0 < θ := by positivity
    have hθ_lt : θ < 2 * Real.pi := by
      simp only [θ]
      rw [div_lt_iff₀ hm_pos]
      nlinarith
    have hlt1 : Real.cos θ < 1 := by
      by_cases hle : θ ≤ Real.pi
      · have h1 := Real.strictAntiOn_cos ⟨le_refl 0, le_of_lt hpi_pos⟩ ⟨le_of_lt hθ_pos, hle⟩ hθ_pos
        rwa [Real.cos_zero] at h1
      · have hgt : Real.pi < θ := lt_of_not_ge hle
        have hpos2 : 0 < 2 * Real.pi - θ := by linarith
        have hle2 : 2 * Real.pi - θ ≤ Real.pi := by linarith
        have h1 := Real.strictAntiOn_cos ⟨le_refl 0, le_of_lt hpi_pos⟩ ⟨le_of_lt hpos2, hle2⟩ hpos2
        rw [Real.cos_zero] at h1
        have hcos_eq : Real.cos (2 * Real.pi - θ) = Real.cos θ := by
          rw [← Real.cos_neg, neg_sub, Real.cos_sub_two_pi]
        rwa [hcos_eq] at h1
    linarith

private theorem sum_chi_range (m : ℕ) (hm : 1 ≤ m) (d : ℤ) :
    (∑ c ∈ Finset.range m, chi m ((c : ℤ) * d)) = if (m : ℤ) ∣ d then (m : ℂ) else 0 := by
  by_cases hd : (m : ℤ) ∣ d
  · simp only [hd, ↓reduceIte]
    have h1 : ∀ c ∈ Finset.range m, chi m ((c : ℤ) * d) = 1 := by
      intro c _
      exact chi_eq_one_of_dvd m hm _ (dvd_mul_of_dvd_right hd _)
    rw [Finset.sum_congr rfl h1]
    simp
  · simp only [hd, ↓reduceIte]
    have hne : chi m d ≠ 1 := fun h => hd (dvd_of_chi_eq_one m hm d h)
    have hsub : chi m d - 1 ≠ 0 := sub_ne_zero.mpr hne
    have hpow : ∀ c ∈ Finset.range m, chi m ((c : ℤ) * d) = (chi m d) ^ c :=
      fun c _ => chi_nat_mul m c d
    rw [Finset.sum_congr rfl hpow]
    have hg := geom_sum_mul (chi m d) m
    have hm1 : (chi m d) ^ m = 1 := by
      rw [← chi_nat_mul]
      exact chi_eq_one_of_dvd m hm _ (dvd_mul_right (m : ℤ) d)
    rw [hm1, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hsub

private theorem dvd_sub_iff_mod_eq (m a b : ℕ) (ha : a < m) :
    ((m : ℤ) ∣ ((b : ℤ) - (a : ℤ))) ↔ a = b % m := by
  constructor
  · rintro ⟨q, hq⟩
    have h1 : ((b : ℤ) % (m : ℤ)) = (a : ℤ) := by
      have h2 : (b : ℤ) = (a : ℤ) + (m : ℤ) * q := by omega
      rw [h2, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    have h3 : ((b % m : ℕ) : ℤ) = (a : ℤ) := by
      rw [Int.natCast_emod]
      exact h1
    exact (Int.ofNat.inj h3).symm
  · intro h
    refine ⟨(b / m : ℕ), ?_⟩
    have hdiv := Nat.div_add_mod b m
    omega

private theorem indicator_mod_eq (m a b : ℕ) (hm : 1 ≤ m) (ha : a < m) :
    (if a = b % m then (m : ℝ) else 0) =
      (∑ c ∈ Finset.range m, chi m ((c : ℤ) * ((b : ℤ) - (a : ℤ)))).re := by
  rw [sum_chi_range m hm]
  by_cases h : a = b % m
  · have hd : (m : ℤ) ∣ ((b : ℤ) - (a : ℤ)) := (dvd_sub_iff_mod_eq m a b ha).mpr h
    simp only [hd, ↓reduceIte, Complex.natCast_re]
    simp [h]
  · have hnd : ¬ ((m : ℤ) ∣ ((b : ℤ) - (a : ℤ))) := mt (dvd_sub_iff_mod_eq m a b ha).mp h
    simp only [hnd, ↓reduceIte, Complex.zero_re]
    simp [h]

private theorem sq_sum_le_card_mul_sum_sq_aux {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ a ∈ s, f a) ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, (f a) ^ 2 := by
  have hnn : 0 ≤ ∑ a ∈ s, ∑ b ∈ s, (f a - f b) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hexp : (∑ a ∈ s, ∑ b ∈ s, (f a - f b) ^ 2) =
      2 * ((s.card : ℝ) * ∑ a ∈ s, (f a) ^ 2 - (∑ a ∈ s, f a) ^ 2) := by
    have h1 : ∀ a b : α, (f a - f b) ^ 2 = (f a) ^ 2 + (f b) ^ 2 - 2 * (f a * f b) := by
      intro a b
      ring
    simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

private theorem sq_norm_sum_le {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ a ∈ s, f a‖ ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, ‖f a‖ ^ 2 := by
  have h1 : ‖∑ a ∈ s, f a‖ ≤ ∑ a ∈ s, ‖f a‖ := norm_sum_le s f
  have hnn : 0 ≤ ∑ a ∈ s, ‖f a‖ := Finset.sum_nonneg (fun a _ => norm_nonneg (f a))
  have h2 : ‖∑ a ∈ s, f a‖ ^ 2 ≤ (∑ a ∈ s, ‖f a‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ a ∈ s, f a)]
  exact h2.trans (sq_sum_le_card_mul_sum_sq_aux s (fun a => ‖f a‖))

private def dotNat {m h : ℕ} (x y : Fin h → Fin m) : ℕ :=
  ∑ j : Fin h, (x j).val * (y j).val

private theorem chi_sum {α : Type*} (m : ℕ) (s : Finset α) (f : α → ℤ) :
    chi m (∑ a ∈ s, f a) = ∏ a ∈ s, chi m (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

private theorem dvd_mul_sub_iff_mod_eq (m c a1 a2 : ℕ) (hm : 1 ≤ m) :
    ((m : ℤ) ∣ ((c : ℤ) * ((a1 : ℤ) - (a2 : ℤ)))) ↔
      a1 % (m / Nat.gcd c m) = a2 % (m / Nat.gcd c m) := by
  set g := Nat.gcd c m
  set r := m / g
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right c (by omega)
  have hgdvd_m : g ∣ m := Nat.gcd_dvd_right c m
  have hgdvd_c : g ∣ c := Nat.gcd_dvd_left c m
  set k := c / g
  have hmr : g * r = m := Nat.mul_div_cancel' hgdvd_m
  have hck : g * k = c := Nat.mul_div_cancel' hgdvd_c
  have hcop : Nat.Coprime k r := Nat.coprime_div_gcd_div_gcd hg0
  have hstep1 : ((m : ℤ) ∣ ((c : ℤ) * ((a1 : ℤ) - (a2 : ℤ)))) ↔
      ((r : ℤ) ∣ ((k : ℤ) * ((a1 : ℤ) - (a2 : ℤ)))) := by
    have hgne : (g : ℤ) ≠ 0 := by omega
    rw [← hmr, ← hck]
    push_cast
    rw [mul_assoc]
    exact mul_dvd_mul_iff_left hgne
  have hstep2 : ((r : ℤ) ∣ ((k : ℤ) * ((a1 : ℤ) - (a2 : ℤ)))) ↔
      ((r : ℤ) ∣ ((a1 : ℤ) - (a2 : ℤ))) := by
    constructor
    · intro hd
      have hci : IsCoprime (r : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
      exact hci.dvd_of_dvd_mul_left hd
    · intro hd
      exact dvd_mul_of_dvd_right hd _
  rw [hstep1, hstep2]
  constructor
  · rintro ⟨q, hq⟩
    have h1 : ((a1 : ℤ) % (r : ℤ)) = ((a2 : ℤ) % (r : ℤ)) := by
      have h2 : (a1 : ℤ) = (a2 : ℤ) + (r : ℤ) * q := by omega
      rw [h2, Int.add_mul_emod_self_left]
    have h3 : ((a1 % r : ℕ) : ℤ) = ((a2 % r : ℕ) : ℤ) := by
      rw [Int.natCast_emod, Int.natCast_emod]
      exact h1
    exact Int.ofNat.inj h3
  · intro h
    refine ⟨((a1 / r : ℕ) : ℤ) - ((a2 / r : ℕ) : ℤ), ?_⟩
    have h1 : (r : ℤ) * ((a1 / r : ℕ) : ℤ) + ((a1 % r : ℕ) : ℤ) = (a1 : ℤ) := by
      exact_mod_cast Nat.div_add_mod a1 r
    have h2 : (r : ℤ) * ((a2 / r : ℕ) : ℤ) + ((a2 % r : ℕ) : ℤ) = (a2 : ℤ) := by
      exact_mod_cast Nat.div_add_mod a2 r
    have h3 : ((a1 % r : ℕ) : ℤ) = ((a2 % r : ℕ) : ℤ) := by exact_mod_cast h
    linarith

private theorem div_gcd_pos (m c : ℕ) (hm : 1 ≤ m) : 0 < m / Nat.gcd c m := by
  have hmr : Nat.gcd c m * (m / Nat.gcd c m) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right c m)
  exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hmr; omega)

private theorem sum_chi_dot_diff {m h : ℕ} (hm : 1 ≤ m) (c : ℕ)
    (y1 y2 : Fin h → Fin m) :
    let r := m / Nat.gcd c m
    let red : (Fin h → Fin m) → (Fin h → Fin r) :=
      fun y j => ⟨(y j).val % r, Nat.mod_lt _ (div_gcd_pos m c hm)⟩
    (∑ x : Fin h → Fin m, chi m ((c : ℤ) * ((dotNat x y1 : ℤ) - (dotNat x y2 : ℤ)))) =
      if red y1 = red y2 then (m : ℂ) ^ h else 0 := by
  intro r red
  have hprod : ∀ x : Fin h → Fin m,
      chi m ((c : ℤ) * ((dotNat x y1 : ℤ) - (dotNat x y2 : ℤ))) =
      ∏ j : Fin h, chi m (((x j).val : ℤ) * ((c : ℤ) * (((y1 j).val : ℤ) - ((y2 j).val : ℤ)))) := by
    intro x
    have hsum : (c : ℤ) * ((dotNat x y1 : ℤ) - (dotNat x y2 : ℤ)) =
        ∑ j : Fin h, ((x j).val : ℤ) * ((c : ℤ) * (((y1 j).val : ℤ) - ((y2 j).val : ℤ))) := by
      simp only [dotNat, Nat.cast_sum, Nat.cast_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [hsum, chi_sum]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun j (a : Fin m) =>
    chi m ((a.val : ℤ) * ((c : ℤ) * (((y1 j).val : ℤ) - ((y2 j).val : ℤ)))))]
  have hcoord : ∀ j : Fin h,
      (∑ a : Fin m, chi m ((a.val : ℤ) * ((c : ℤ) * (((y1 j).val : ℤ) - ((y2 j).val : ℤ))))) =
      if (y1 j).val % r = (y2 j).val % r then (m : ℂ) else 0 := by
    intro j
    let e : Fin m ≃ Finset.range m :=
      { toFun := fun a => ⟨a.val, Finset.mem_range.mpr a.isLt⟩
        invFun := fun b => ⟨b.1, Finset.mem_range.mp b.2⟩
        left_inv := fun a => Fin.ext rfl
        right_inv := fun b => Subtype.ext rfl }
    have hsum_range :
        (∑ a : Fin m, chi m ((a.val : ℤ) * ((c : ℤ) * (((y1 j).val : ℤ) - ((y2 j).val : ℤ))))) =
        ∑ a ∈ Finset.range m, chi m ((a : ℤ) * ((c : ℤ) * (((y1 j).val : ℤ) - ((y2 j).val : ℤ)))) := by
      rw [← Finset.sum_coe_sort (Finset.range m)]
      exact Fintype.sum_equiv e _ _ (fun a => rfl)
    rw [hsum_range, sum_chi_range m hm]
    simp only [dvd_mul_sub_iff_mod_eq m c (y1 j).val (y2 j).val hm]
    rfl
  simp_rw [hcoord]
  by_cases hred : red y1 = red y2
  · simp only [hred, ↓reduceIte]
    have hAll : ∀ j : Fin h, (y1 j).val % r = (y2 j).val % r := by
      intro j
      exact congrArg Fin.val (congrFun hred j)
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin h)),
        (if (y1 j).val % r = (y2 j).val % r then (m : ℂ) else 0) = (m : ℂ) := by
      intro j _
      simp [hAll j]
    rw [Finset.prod_congr rfl h1]
    simp
  · simp only [hred, ↓reduceIte]
    have hex : ∃ j : Fin h, (y1 j).val % r ≠ (y2 j).val % r := by
      by_contra hno
      apply hred
      funext j
      apply Fin.ext
      by_contra hne
      exact hno ⟨j, hne⟩
    obtain ⟨j, hj⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

private theorem fiber_red_card {m h r : ℕ} (hr : 0 < r) (hrdvd : r ∣ m) (z : Fin h → Fin r) :
    ((Finset.univ : Finset (Fin h → Fin m)).filter
      (fun y => (fun j => (⟨(y j).val % r, Nat.mod_lt _ hr⟩ : Fin r)) = z)).card =
      (m / r) ^ h := by
  have hmr : m / r * r = m := Nat.div_mul_cancel hrdvd
  rw [← Fintype.card_subtype]
  let e : (Fin h → Fin (m / r)) ≃
      {y : Fin h → Fin m // (fun j => (⟨(y j).val % r, Nat.mod_lt _ hr⟩ : Fin r)) = z} :=
    { toFun := fun q =>
        ⟨fun j => ⟨(q j).val * r + (z j).val, by
          have hq := (q j).isLt
          have hz := (z j).isLt
          have hle : ((q j).val + 1) * r ≤ (m / r) * r := Nat.mul_le_mul_right r (by omega)
          nlinarith⟩,
        by
          funext j
          apply Fin.ext
          simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (z j).isLt]⟩
      invFun := fun y j => ⟨(y.1 j).val / r, by
        have hy : (y.1 j).val < r * (m / r) := by
          have h1 := (y.1 j).isLt
          linarith [hmr]
        exact Nat.div_lt_of_lt_mul hy⟩
      left_inv := fun q => by
        funext j
        apply Fin.ext
        dsimp
        rw [mul_comm, Nat.mul_add_div hr, Nat.div_eq_of_lt (z j).isLt, add_zero]
      right_inv := fun y => by
        apply Subtype.ext
        funext j
        apply Fin.ext
        have hmod : (y.1 j).val % r = (z j).val := congrArg Fin.val (congrFun y.2 j)
        have hdm := Nat.div_add_mod (y.1 j).val r
        rw [hmod] at hdm
        dsimp
        linarith }
  rw [← Fintype.card_congr e]
  simp

private theorem rect_fourier_sq_bound {m h : ℕ} (hm : 1 ≤ m) (c : ℕ)
    (Ai Bi : Finset (Fin h → Fin m)) (out : (Fin h → Fin m) → Fin m) :
    let r := m / Nat.gcd c m
    ‖∑ x ∈ Ai, ∑ y ∈ Bi, chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((out y).val : ℤ)))‖ ^ 2 ≤
      ((m : ℝ) ^ (2 * h) / (r : ℝ) ^ h) * ((Ai.card : ℝ) * (Bi.card : ℝ)) := by
  intro r
  have hg0 : 0 < Nat.gcd c m := Nat.gcd_pos_of_pos_right c (by omega)
  have hgdvd : Nat.gcd c m ∣ m := Nat.gcd_dvd_right c m
  have hmr : Nat.gcd c m * r = m := Nat.mul_div_cancel' hgdvd
  have hr : 0 < r := div_gcd_pos m c hm
  have hrdvd : r ∣ m := ⟨Nat.gcd c m, by linarith⟩
  let β : (Fin h → Fin m) → ℂ := fun y =>
    if y ∈ Bi then chi m (-((c : ℤ) * ((out y).val : ℤ))) else 0
  have hS : (∑ x ∈ Ai, ∑ y ∈ Bi, chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((out y).val : ℤ)))) =
      ∑ x ∈ Ai, ∑ y : Fin h → Fin m, β y * chi m ((c : ℤ) * (dotNat x y : ℤ)) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp only [β, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    refine Finset.sum_congr rfl ?_
    intro y _
    rw [← chi_add]
    congr 1
    ring
  rw [hS]
  have hcs1 : ‖∑ x ∈ Ai, ∑ y : Fin h → Fin m, β y * chi m ((c : ℤ) * (dotNat x y : ℤ))‖ ^ 2 ≤
      (Ai.card : ℝ) * ∑ x ∈ Ai, ‖∑ y : Fin h → Fin m, β y * chi m ((c : ℤ) * (dotNat x y : ℤ))‖ ^ 2 :=
    sq_norm_sum_le Ai _
  have hsub_sum :
      (∑ x ∈ Ai, ‖∑ y : Fin h → Fin m, β y * chi m ((c : ℤ) * (dotNat x y : ℤ))‖ ^ 2) ≤
      ∑ x : Fin h → Fin m, ‖∑ y : Fin h → Fin m, β y * chi m ((c : ℤ) * (dotNat x y : ℤ))‖ ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  let red : (Fin h → Fin m) → (Fin h → Fin r) := fun y j => ⟨(y j).val % r, Nat.mod_lt _ hr⟩
  have hexpand :
      (∑ x : Fin h → Fin m, ‖∑ y : Fin h → Fin m, β y * chi m ((c : ℤ) * (dotNat x y : ℤ))‖ ^ 2) =
      (m : ℝ) ^ h * ∑ z : Fin h → Fin r,
        ‖∑ y ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), β y‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    have hnorm_sq : ∀ w : ℂ, (‖w‖ : ℂ) ^ 2 = w * star w := by
      intro w
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    have hstar_sum : ∀ (s : Finset (Fin h → Fin m)) (f : (Fin h → Fin m) → ℂ),
        star (∑ a ∈ s, f a) = ∑ a ∈ s, star (f a) := by
      intro s f
      simp
    have hstar_mul : ∀ a b : ℂ, star (a * b) = star a * star b := by
      intro a b
      exact (star_mul a b).trans (mul_comm _ _)
    simp_rw [hnorm_sq, hstar_sum, hstar_mul, chi_neg]
    have hLHS :
        (∑ x : Fin h → Fin m,
          (∑ y1 : Fin h → Fin m, β y1 * chi m ((c : ℤ) * (dotNat x y1 : ℤ))) *
          (∑ y2 : Fin h → Fin m, star (β y2) * chi m (-((c : ℤ) * (dotNat x y2 : ℤ))))) =
        ∑ y1 : Fin h → Fin m, ∑ y2 : Fin h → Fin m,
          β y1 * star (β y2) *
          (∑ x : Fin h → Fin m, chi m ((c : ℤ) * ((dotNat x y1 : ℤ) - (dotNat x y2 : ℤ)))) := by
      have h1 : ∀ x : Fin h → Fin m,
          (∑ y1 : Fin h → Fin m, β y1 * chi m ((c : ℤ) * (dotNat x y1 : ℤ))) *
          (∑ y2 : Fin h → Fin m, star (β y2) * chi m (-((c : ℤ) * (dotNat x y2 : ℤ)))) =
          ∑ y1 : Fin h → Fin m, ∑ y2 : Fin h → Fin m,
            β y1 * star (β y2) * chi m ((c : ℤ) * ((dotNat x y1 : ℤ) - (dotNat x y2 : ℤ))) := by
        intro x
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro y1 _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro y2 _
        have hch : chi m ((c : ℤ) * (dotNat x y1 : ℤ)) *
            chi m (-((c : ℤ) * (dotNat x y2 : ℤ))) =
            chi m ((c : ℤ) * ((dotNat x y1 : ℤ) - (dotNat x y2 : ℤ))) := by
          rw [← chi_add]
          congr 1
          ring
        calc β y1 * chi m ((c : ℤ) * (dotNat x y1 : ℤ)) *
              (star (β y2) * chi m (-((c : ℤ) * (dotNat x y2 : ℤ))))
            = β y1 * star (β y2) * (chi m ((c : ℤ) * (dotNat x y1 : ℤ)) *
              chi m (-((c : ℤ) * (dotNat x y2 : ℤ)))) := by ring
          _ = β y1 * star (β y2) * chi m ((c : ℤ) * ((dotNat x y1 : ℤ) - (dotNat x y2 : ℤ))) := by
              rw [hch]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro y1 _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro y2 _
      rw [← Finset.mul_sum]
    rw [hLHS]
    have hdot := fun y1 y2 => sum_chi_dot_diff (m := m) (h := h) hm c y1 y2
    simp_rw [hdot]
    have hRHS :
        (m : ℂ) ^ h * ∑ z : Fin h → Fin r,
          (∑ y1 ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), β y1) *
          (∑ y2 ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), star (β y2)) =
        ∑ y1 : Fin h → Fin m, ∑ y2 : Fin h → Fin m,
          β y1 * star (β y2) * if red y1 = red y2 then (m : ℂ) ^ h else 0 := by
      have h1 : ∀ z : Fin h → Fin r,
          (∑ y1 ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), β y1) *
          (∑ y2 ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), star (β y2)) =
          ∑ y1 : Fin h → Fin m, ∑ y2 : Fin h → Fin m,
            if red y1 = z ∧ red y2 = z then β y1 * star (β y2) else 0 := by
        intro z
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro y1 _
        by_cases h1 : red y1 = z
        · simp [h1]
        · simp [h1]
      simp_rw [h1]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro y1 _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro y2 _
      have h2 : ∀ z : Fin h → Fin r,
          (m : ℂ) ^ h * (if red y1 = z ∧ red y2 = z then β y1 * star (β y2) else 0) =
          if red y1 = z then if red y2 = z then (m : ℂ) ^ h * (β y1 * star (β y2)) else 0 else 0 := by
        intro z
        by_cases h1' : red y1 = z <;> by_cases h2' : red y2 = z <;> simp [h1', h2']
      simp_rw [h2]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      by_cases he : red y1 = red y2
      · simp only [he, ↓reduceIte]
        ring
      · have he' : red y2 ≠ red y1 := fun h => he h.symm
        simp [he, he']
    exact hRHS.symm
  have hfib_bound :
      (∑ z : Fin h → Fin r,
        ‖∑ y ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), β y‖ ^ 2) ≤
      ((m / r : ℕ) : ℝ) ^ h * (Bi.card : ℝ) := by
    have h1 : ∀ z : Fin h → Fin r,
        ‖∑ y ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), β y‖ ^ 2 ≤
        ((m / r : ℕ) : ℝ) ^ h *
          ∑ y ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), ‖β y‖ ^ 2 := by
      intro z
      have hcs := sq_norm_sum_le
        ((Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z)) β
      rw [fiber_red_card hr hrdvd z] at hcs
      push_cast at hcs
      exact hcs
    have h2 :
        (∑ z : Fin h → Fin r,
          ‖∑ y ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), β y‖ ^ 2) ≤
        ((m / r : ℕ) : ℝ) ^ h * ∑ z : Fin h → Fin r,
          ∑ y ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), ‖β y‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun z _ => h1 z)
    have hpart_fib :
        (∑ z : Fin h → Fin r,
          ∑ y ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), ‖β y‖ ^ 2) =
        ∑ y : Fin h → Fin m, ‖β y‖ ^ 2 := by
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) (fun y => ‖β y‖ ^ 2)
    have hbeta_norm : (∑ y : Fin h → Fin m, ‖β y‖ ^ 2) = (Bi.card : ℝ) := by
      have h3 : ∀ y : Fin h → Fin m, ‖β y‖ ^ 2 = if y ∈ Bi then (1 : ℝ) else 0 := by
        intro y
        by_cases hy : y ∈ Bi
        · simp [β, hy, norm_chi]
        · simp [β, hy]
      simp_rw [h3]
      simp
    rw [hpart_fib, hbeta_norm] at h2
    exact h2
  have hmr_real : (m : ℝ) ^ h * ((m / r : ℕ) : ℝ) ^ h = (m : ℝ) ^ (2 * h) / (r : ℝ) ^ h := by
    have hrne : (r : ℝ) ≠ 0 := by positivity
    have hdiv : ((m / r : ℕ) : ℝ) = (m : ℝ) / (r : ℝ) := by
      have hnat : (m / r) * r = m := Nat.div_mul_cancel hrdvd
      have hreal : ((m / r : ℕ) : ℝ) * (r : ℝ) = (m : ℝ) := by exact_mod_cast hnat
      field_simp [hrne]
      exact hreal
    rw [hdiv, div_pow, mul_div_assoc', ← pow_add, two_mul]
  calc ‖∑ x ∈ Ai, ∑ y : Fin h → Fin m, β y * chi m ((c : ℤ) * (dotNat x y : ℤ))‖ ^ 2
      ≤ (Ai.card : ℝ) * ∑ x ∈ Ai,
          ‖∑ y : Fin h → Fin m, β y * chi m ((c : ℤ) * (dotNat x y : ℤ))‖ ^ 2 := hcs1
    _ ≤ (Ai.card : ℝ) * ∑ x : Fin h → Fin m,
          ‖∑ y : Fin h → Fin m, β y * chi m ((c : ℤ) * (dotNat x y : ℤ))‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsub_sum (Nat.cast_nonneg _)
    _ = (Ai.card : ℝ) * ((m : ℝ) ^ h * ∑ z : Fin h → Fin r,
          ‖∑ y ∈ (Finset.univ : Finset (Fin h → Fin m)).filter (fun y => red y = z), β y‖ ^ 2) := by
        rw [hexpand]
    _ ≤ (Ai.card : ℝ) * ((m : ℝ) ^ h * (((m / r : ℕ) : ℝ) ^ h * (Bi.card : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_left hfib_bound (by positivity)
    _ = ((m : ℝ) ^ h * ((m / r : ℕ) : ℝ) ^ h) * ((Ai.card : ℝ) * (Bi.card : ℝ)) := by ring
    _ = ((m : ℝ) ^ (2 * h) / (r : ℝ) ^ h) * ((Ai.card : ℝ) * (Bi.card : ℝ)) := by rw [hmr_real]

private theorem sum_range_group_divisors (m : ℕ) (hm : 1 ≤ m) (f : ℕ → ℝ) :
    (∑ c ∈ Finset.range m, f (m / Nat.gcd c m)) =
      ∑ r ∈ m.divisors, (r.totient : ℝ) * f r := by
  have hm0 : m ≠ 0 := by omega
  have hmaps : ∀ c ∈ Finset.range m, m / Nat.gcd c m ∈ m.divisors := by
    intro c _
    rw [Nat.mem_divisors]
    exact ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right c m), hm0⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hrdvd : r ∣ m := (Nat.mem_divisors.mp hr).1
  have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hrdvd (by omega)
  let g := m / r
  have hgr : g * r = m := Nat.div_mul_cancel hrdvd
  have hgpos : 0 < g := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hgr; omega)
  have hconst : (∑ c ∈ (Finset.range m).filter (fun c => m / Nat.gcd c m = r), f (m / Nat.gcd c m)) =
      (((Finset.range m).filter (fun c => m / Nat.gcd c m = r)).card : ℝ) * f r := by
    have h1 : ∀ c ∈ (Finset.range m).filter (fun c => m / Nat.gcd c m = r),
        f (m / Nat.gcd c m) = f r := by
      intro c hc
      rw [(Finset.mem_filter.mp hc).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  congr 1
  norm_cast
  have hcard : ((Finset.range m).filter (fun c => m / Nat.gcd c m = r)).card =
      ((Finset.range r).filter (fun k => Nat.Coprime r k)).card := by
    refine Finset.card_bij' (fun c _ => c / g) (fun k _ => g * k) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc ⊢
      have hgcd_eq : Nat.gcd c m = g := by
        have h1 : Nat.gcd c m * r = m := by
          rw [← hc.2]
          exact Nat.mul_div_cancel' (Nat.gcd_dvd_right c m)
        have h2 : Nat.gcd c m * r = g * r := h1.trans hgr.symm
        exact Nat.eq_of_mul_eq_mul_right hrpos h2
      have hg_dvd_c : g ∣ c := hgcd_eq ▸ Nat.gcd_dvd_left c m
      have hcg : g * (c / g) = c := Nat.mul_div_cancel' hg_dvd_c
      constructor
      · have hlt : g * (c / g) < g * r := by rw [hcg, hgr]; exact hc.1
        exact Nat.lt_of_mul_lt_mul_left hlt
      · have hcop1 : Nat.Coprime (c / g) r := by
          have h1 : g * Nat.gcd (c / g) r = g := by
            rw [← Nat.gcd_mul_left, hcg, hgr, hgcd_eq]
          have h2 : Nat.gcd (c / g) r = 1 := by
            have h3 : g * Nat.gcd (c / g) r = g * 1 := by omega
            exact Nat.eq_of_mul_eq_mul_left hgpos h3
          exact h2
        exact hcop1.symm
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      constructor
      · rw [← hgr]
        exact Nat.mul_lt_mul_of_pos_left hk.1 hgpos
      · have hgcd : Nat.gcd (g * k) m = g := by
          rw [← hgr, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hk.2.symm, mul_one]
        rw [hgcd, ← hgr, Nat.mul_div_cancel_left r hgpos]
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc
      have hgcd_eq : Nat.gcd c m = g := by
        have h1 : Nat.gcd c m * r = m := by
          rw [← hc.2]
          exact Nat.mul_div_cancel' (Nat.gcd_dvd_right c m)
        exact Nat.eq_of_mul_eq_mul_right hrpos (h1.trans hgr.symm)
      exact Nat.mul_div_cancel' (hgcd_eq ▸ Nat.gcd_dvd_left c m)
    · intro k _
      exact Nat.mul_div_cancel_left k hgpos
  rw [hcard]
  exact (Nat.totient_eq_card_coprime r).symm

theorem main_aux (m h T : ℕ) (hm : 2 ≤ m)
    (A B : Fin T → Finset (Fin h → Fin m)) (output : Fin T → (Fin h → Fin m) → Fin m)
    (hpart : ∀ x y : Fin h → Fin m, ∃! t : Fin T, x ∈ A t ∧ y ∈ B t) :
    let X := Fin h → Fin m
    let correct := ((Finset.univ : Finset (X × X)).filter (fun pair =>
      ∃ i : Fin T, pair.1 ∈ A i ∧ pair.2 ∈ B i ∧
        (output i pair.2).val =
          ((Finset.univ : Finset (Fin h)).sum (fun j => (pair.1 j).val * (pair.2 j).val)) % m)).card
    (m : ℝ) * (correct : ℝ) ≤ (m : ℝ) ^ (2 * h) *
      (m.divisors.sum (fun r => (r.totient : ℝ) *
        min 1 (Real.sqrt ((T : ℝ) / (r : ℝ) ^ h)))) := by
  intro X correct
  have hm1 : 1 ≤ m := by omega
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin T))) (fun i => A i ×ˢ B i) := by
    intro i _ j _ hij
    change Disjoint (A i ×ˢ B i) (A j ×ˢ B j)
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [Finset.mem_product] at h1 h2
    obtain ⟨t, _, ht⟩ := hpart x y
    exact hij ((ht i h1).trans (ht j h2).symm)
  have huniv_eq : (Finset.univ : Finset (Fin T)).biUnion (fun i => A i ×ˢ B i) = Finset.univ := by
    ext ⟨x, y⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_product, true_and, iff_true]
    obtain ⟨t, ht, _⟩ := hpart x y
    exact ⟨t, ht⟩
  have harea_sum : (∑ i : Fin T, ((A i).card : ℝ) * ((B i).card : ℝ)) = (m : ℝ) ^ (2 * h) := by
    have hnat : (∑ i : Fin T, (A i).card * (B i).card) = m ^ (2 * h) := by
      have h1 : (∑ i : Fin T, (A i ×ˢ B i).card) = (Finset.univ : Finset (X × X)).card := by
        rw [← Finset.card_biUnion hdisj, huniv_eq]
      simp only [Finset.card_product] at h1
      rw [h1, Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, ← pow_add, two_mul]
    exact_mod_cast hnat
  have hcorr_eq :
      (m : ℝ) * (correct : ℝ) =
      ∑ i : Fin T, ∑ x ∈ A i, ∑ y ∈ B i,
        if (output i y).val = dotNat x y % m then (m : ℝ) else 0 := by
    have hdisj_f : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin T)))
        (fun i => (A i ×ˢ B i).filter (fun p => (output i p.2).val = dotNat p.1 p.2 % m)) := by
      intro i hi j hj hij
      exact (hdisj hi hj hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcorr_biUnion :
        ((Finset.univ : Finset (X × X)).filter (fun pair =>
          ∃ i : Fin T, pair.1 ∈ A i ∧ pair.2 ∈ B i ∧
            (output i pair.2).val = dotNat pair.1 pair.2 % m)) =
        (Finset.univ : Finset (Fin T)).biUnion
          (fun i => (A i ×ˢ B i).filter (fun p => (output i p.2).val = dotNat p.1 p.2 % m)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_product]
      constructor
      · rintro ⟨i, hx, hy, heq⟩
        exact ⟨i, ⟨hx, hy⟩, heq⟩
      · rintro ⟨i, ⟨hx, hy⟩, heq⟩
        exact ⟨i, hx, hy, heq⟩
    have hcard_sum : correct =
        ∑ i : Fin T, ((A i ×ˢ B i).filter (fun p => (output i p.2).val = dotNat p.1 p.2 % m)).card := by
      change ((Finset.univ : Finset (X × X)).filter (fun pair =>
        ∃ i : Fin T, pair.1 ∈ A i ∧ pair.2 ∈ B i ∧
          (output i pair.2).val = dotNat pair.1 pair.2 % m)).card = _
      rw [hcorr_biUnion, Finset.card_biUnion hdisj_f]
    rw [hcard_sum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.card_filter]
    push_cast
    rw [Finset.mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl ?_
    intro x _
    refine Finset.sum_congr rfl ?_
    intro y _
    split_ifs <;> ring
  have hchar_expand :
      (m : ℝ) * (correct : ℝ) ≤
      ∑ c ∈ Finset.range m, ∑ i : Fin T,
        ‖∑ x ∈ A i, ∑ y ∈ B i, chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖ := by
    rw [hcorr_eq]
    have h1 :
        (∑ i : Fin T, ∑ x ∈ A i, ∑ y ∈ B i,
          if (output i y).val = dotNat x y % m then (m : ℝ) else 0) =
        ∑ c ∈ Finset.range m,
          (∑ i : Fin T, ∑ x ∈ A i, ∑ y ∈ B i,
            chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))).re := by
      have hterm : ∀ (i : Fin T) (x y : X),
          (if (output i y).val = dotNat x y % m then (m : ℝ) else 0) =
          ∑ c ∈ Finset.range m,
            (chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))).re := by
        intro i x y
        rw [indicator_mod_eq m (output i y).val (dotNat x y) hm1 (output i y).isLt,
          Complex.re_sum]
      simp_rw [hterm]
      have h2 : ∀ i : Fin T,
          (∑ x ∈ A i, ∑ y ∈ B i, ∑ c ∈ Finset.range m,
            (chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))).re) =
          ∑ c ∈ Finset.range m, ∑ x ∈ A i, ∑ y ∈ B i,
            (chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))).re := by
        intro i
        have h3 : ∀ x ∈ A i,
            (∑ y ∈ B i, ∑ c ∈ Finset.range m,
              (chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))).re) =
            ∑ c ∈ Finset.range m, ∑ y ∈ B i,
              (chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))).re :=
          fun _ _ => Finset.sum_comm
        rw [Finset.sum_congr rfl h3, Finset.sum_comm]
      simp_rw [h2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro c _
      simp only [Complex.re_sum]
    rw [h1]
    refine Finset.sum_le_sum ?_
    intro c _
    exact (Complex.re_le_norm _).trans (norm_sum_le _ _)
  have hbound_c : ∀ c ∈ Finset.range m,
      (∑ i : Fin T,
        ‖∑ x ∈ A i, ∑ y ∈ B i, chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖) ≤
      (m : ℝ) ^ (2 * h) * min 1 (Real.sqrt ((T : ℝ) / ((m / Nat.gcd c m : ℕ) : ℝ) ^ h)) := by
    intro c _
    rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
    apply le_min
    · have htriv : ∀ i : Fin T,
          ‖∑ x ∈ A i, ∑ y ∈ B i, chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖ ≤
          ((A i).card : ℝ) * ((B i).card : ℝ) := by
        intro i
        calc ‖∑ x ∈ A i, ∑ y ∈ B i,
                chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖
            ≤ ∑ x ∈ A i, ‖∑ y ∈ B i,
                chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖ := norm_sum_le _ _
          _ ≤ ∑ x ∈ A i, ∑ y ∈ B i,
                ‖chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖ :=
              Finset.sum_le_sum (fun x _ => norm_sum_le _ _)
          _ = ((A i).card : ℝ) * ((B i).card : ℝ) := by
              simp [norm_chi]
      exact (Finset.sum_le_sum (fun i _ => htriv i)).trans harea_sum.le
    · set r := m / Nat.gcd c m
      have hsq :
          (∑ i : Fin T,
            ‖∑ x ∈ A i, ∑ y ∈ B i,
              chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖) ^ 2 ≤
          ((m : ℝ) ^ (2 * h) * Real.sqrt ((T : ℝ) / (r : ℝ) ^ h)) ^ 2 := by
        have hcsT :
            (∑ i : Fin T,
              ‖∑ x ∈ A i, ∑ y ∈ B i,
                chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖) ^ 2 ≤
            (T : ℝ) * ∑ i : Fin T,
              ‖∑ x ∈ A i, ∑ y ∈ B i,
                chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖ ^ 2 := by
          have h1 := sq_sum_le_card_mul_sum_sq_aux (Finset.univ : Finset (Fin T))
            (fun i => ‖∑ x ∈ A i, ∑ y ∈ B i,
              chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖)
          simpa using h1
        have hsum_sq :
            (∑ i : Fin T,
              ‖∑ x ∈ A i, ∑ y ∈ B i,
                chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖ ^ 2) ≤
            ((m : ℝ) ^ (2 * h) / (r : ℝ) ^ h) * (m : ℝ) ^ (2 * h) := by
          calc (∑ i : Fin T,
                ‖∑ x ∈ A i, ∑ y ∈ B i,
                  chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖ ^ 2)
              ≤ ∑ i : Fin T,
                  ((m : ℝ) ^ (2 * h) / (r : ℝ) ^ h) * (((A i).card : ℝ) * ((B i).card : ℝ)) :=
                Finset.sum_le_sum (fun i _ => rect_fourier_sq_bound hm1 c (A i) (B i) (output i))
            _ = ((m : ℝ) ^ (2 * h) / (r : ℝ) ^ h) *
                  ∑ i : Fin T, ((A i).card : ℝ) * ((B i).card : ℝ) := by
                rw [← Finset.mul_sum]
            _ = ((m : ℝ) ^ (2 * h) / (r : ℝ) ^ h) * (m : ℝ) ^ (2 * h) := by rw [harea_sum]
        have hrhs :
            ((m : ℝ) ^ (2 * h) * Real.sqrt ((T : ℝ) / (r : ℝ) ^ h)) ^ 2 =
            (T : ℝ) * (((m : ℝ) ^ (2 * h) / (r : ℝ) ^ h) * (m : ℝ) ^ (2 * h)) := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          ring
        rw [hrhs]
        exact hcsT.trans (mul_le_mul_of_nonneg_left hsum_sq (Nat.cast_nonneg T))
      have hnn1 : 0 ≤ ∑ i : Fin T,
          ‖∑ x ∈ A i, ∑ y ∈ B i,
            chi m ((c : ℤ) * ((dotNat x y : ℤ) - ((output i y).val : ℤ)))‖ :=
        Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      have hnn2 : 0 ≤ (m : ℝ) ^ (2 * h) * Real.sqrt ((T : ℝ) / (r : ℝ) ^ h) := by positivity
      nlinarith
  have htot :
      (m : ℝ) * (correct : ℝ) ≤
      ∑ c ∈ Finset.range m,
        (m : ℝ) ^ (2 * h) * min 1 (Real.sqrt ((T : ℝ) / ((m / Nat.gcd c m : ℕ) : ℝ) ^ h)) :=
    hchar_expand.trans (Finset.sum_le_sum hbound_c)
  rw [← Finset.mul_sum,
    sum_range_group_divisors m hm1 (fun r => min 1 (Real.sqrt ((T : ℝ) / (r : ℝ) ^ h)))] at htot
  exact htot

end PEqualNP.Outside.L_lib_520_aux

theorem PEqualNP.Outside.L_lib_520 :
∀ (m h T : Nat), 2 ≤ m →
  let X := Fin h → Fin m
  ∀ (A B : Fin T → Finset X) (output : Fin T → X → Fin m),
    (∀ x y : X, ∃! t : Fin T, x ∈ A t ∧ y ∈ B t) →
    let correct := ((Finset.univ : Finset (X × X)).filter (fun pair =>
      ∃ i : Fin T, pair.1 ∈ A i ∧ pair.2 ∈ B i ∧
        (output i pair.2).val =
          ((Finset.univ : Finset (Fin h)).sum (fun j => (pair.1 j).val*(pair.2 j).val)) % m)).card
    (m : ℝ) * (correct : ℝ) ≤ (m : ℝ)^(2*h) *
      (m.divisors.sum (fun r => (r.totient : ℝ) *
        min 1 (Real.sqrt ((T : ℝ)/(r : ℝ)^h)))) := by
  intro m h T hm X A B output hpart correct
  exact PEqualNP.Outside.L_lib_520_aux.main_aux m h T hm A B output hpart
