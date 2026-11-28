import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_684_aux

abbrev Row (q : ℕ) := Option (Equiv.Perm (Fin q))

noncomputable def kappa (q : ℕ) : ℝ := (q : ℝ)/2 + if q % 2 = 0 then 1/2 else (q : ℝ)/(q+1)

noncomputable def mix (q : ℕ) : ℝ := if q % 2 = 0 then 1/(q : ℝ) else 1/((q : ℝ)+1)

def negSigns {q : ℕ} (a : Row q) (j : Fin q) : Bool :=
  match a with
  | none => false
  | some e => decide ((e j).val < q/2)

def sigma {q : ℕ} (a : Row q) (j : Fin q) : ℝ :=
  if negSigns a j then -1 else 1

def cap {q : ℕ} (a : Row q) : ℝ :=
  match a with
  | none => q
  | some _ => (q - q/2 : ℕ)

noncomputable def nperm (q : ℕ) : ℝ := Fintype.card (Equiv.Perm (Fin q))

noncomputable def mass {q : ℕ} (a : Row q) : ℝ :=
  match a with
  | none => mix q
  | some _ => (1-mix q)/nperm q

noncomputable def tilt {q : ℕ} (a : Row q) : ℝ := mass a * cap a / kappa q

def rowSq {q : ℕ} (a : Row q) (x : Fin q → ℝ) : ℝ := (∑ j, sigma a j * x j)^2

noncomputable def invTilt {q : ℕ} (a : Row q) : ℝ := kappa q / cap a

lemma kappa_ge {q : ℕ} (hq : 2 ≤ q) : 1 ≤ kappa q := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold kappa
  split <;> linarith [show 0 ≤ (q : ℝ)/((q : ℝ)+1) by positivity]

lemma cap_pos {q : ℕ} (hq : 2 ≤ q) (a : Row q) : 0 < cap a := by
  cases a with
  | none =>
    change (0 : ℝ) < (q : ℝ)
    exact_mod_cast (show 0 < q by omega)
  | some e =>
    change (0 : ℝ) < ((q-q/2 : ℕ) : ℝ)
    exact_mod_cast (show 0 < q-q/2 by omega)

lemma nperm_pos (q : ℕ) : 0 < nperm q := by
  unfold nperm
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin q)))

lemma mix_bounds {q : ℕ} (hq : 2 ≤ q) : 0 ≤ mix q ∧ mix q ≤ 1 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold mix
  split <;> constructor <;> first | positivity | (apply (div_le_iff₀ (by positivity)).2; linarith)

lemma tilt_nonneg {q : ℕ} (hq : 2 ≤ q) (a : Row q) : 0 ≤ tilt a := by
  have hm := mix_bounds hq
  have hn := nperm_pos q
  have hc := cap_pos hq a
  have hk := kappa_ge hq
  have hn' : 0 ≤ mass a := by
    cases a with
    | none => exact hm.1
    | some e => exact div_nonneg (sub_nonneg.mpr hm.2) hn.le
  exact div_nonneg (mul_nonneg hn' hc.le) (by linarith)

lemma mix_eqns {q : ℕ} (hq : 2 ≤ q) :
    mix q * (q : ℝ) + (1-mix q) * (q-q/2 : ℕ) = kappa q ∧
    mix q * (q : ℝ) + (1-mix q) * (q%2 : ℕ)^2 / (q : ℝ) = 1 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hN : 2*(q/2) + q%2 = q := Nat.div_add_mod q 2
  have hN' : q/2 ≤ q := by omega
  have hR : 2*((q/2 : ℕ) : ℝ) + ((q%2 : ℕ) : ℝ) = q := by exact_mod_cast hN
  rw [Nat.cast_sub hN']
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · have he : ((q/2 : ℕ) : ℝ) = (q:ℝ)/2 := by simp [h] at hR; linarith
    rw [he]
    simp only [mix, kappa, h, ite_true, Nat.cast_zero, zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero, zero_div, add_zero]
    constructor <;> (field_simp <;> ring)
  · have he : ((q/2 : ℕ) : ℝ) = ((q:ℝ)-1)/2 := by simp [h] at hR; linarith
    rw [he]
    simp only [mix, kappa, h, Nat.one_ne_zero, ite_false, Nat.cast_one, one_pow]
    have hn : (q:ℝ) ≠ 0 := by linarith
    have hn' : (q:ℝ)+1 ≠ 0 := by linarith
    constructor <;> (field_simp [hn, hn'] <;> ring)

lemma tilt_total {q : ℕ} (hq : 2 ≤ q) : ∑ a : Row q, tilt a = 1 := by
  have hn := (nperm_pos q).ne'
  have hk : kappa q ≠ 0 := by linarith [kappa_ge hq]
  simp only [tilt, Fintype.sum_option, mass, cap, Finset.sum_const, nsmul_eq_mul]
  change mix q * (q : ℝ) / kappa q + nperm q *
    (((1-mix q) / nperm q) * ((q-q/2 : ℕ) : ℝ) / kappa q) = 1
  have he := (mix_eqns hq).1
  calc
    _ = (mix q * (q : ℝ) + (1-mix q) * ((q-q/2 : ℕ) : ℝ)) / kappa q := by
      field_simp [hn, hk] <;> ring
    _ = 1 := by rw [he, div_self hk]

lemma low_count (q : ℕ) : (Finset.univ.filter fun j : Fin q => j.val < q/2).card = q/2 := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun j => if j < q/2 then (1:ℕ) else 0)]
  rw [← Finset.sum_filter]
  have h : ((Finset.range q).filter (fun j => j < q/2)) = Finset.range (q/2) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp [h]

lemma perm_count {q : ℕ} (e : Equiv.Perm (Fin q)) :
    (Finset.univ.filter fun j => (e j).val < q/2).card = q/2 := by
  rw [Finset.card_filter]
  rw [Equiv.sum_comp e (fun j => if j.val < q/2 then (1:ℕ) else 0)]
  rw [← Finset.card_filter]
  exact low_count q

lemma signed_sum {q : ℕ} (e : Equiv.Perm (Fin q)) :
    ∑ j, sigma (some e) j = ((q%2 : ℕ) : ℝ) := by
  have hN : 2*(q/2) + q%2 = q := Nat.div_add_mod q 2
  have hR : 2*((q/2 : ℕ) : ℝ) + ((q%2 : ℕ) : ℝ) = q := by exact_mod_cast hN
  have he : ∀ j : Fin q, sigma (some e) j = 1-2*(if (e j).val < q/2 then 1 else (0:ℝ)) := by
    intro j
    by_cases h : (e j).val < q/2 <;> simp [sigma, negSigns, h] <;> norm_num
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← Finset.sum_filter]
  simp [perm_count]
  linarith

lemma signed_square {q : ℕ} (a : Row q) (j : Fin q) : sigma a j ^ 2 = 1 := by
  unfold sigma
  split <;> norm_num

lemma perm_reindex {q : ℕ} (r : Equiv.Perm (Fin q)) (g : Equiv.Perm (Fin q) → ℝ) :
    ∑ e, g (r.trans e) = ∑ e, g e := by
  exact Equiv.sum_comp (Equiv.mulRight r) g

lemma sign_first {q : ℕ} (hq : 2 ≤ q) (j : Fin q) :
    ∑ e : Equiv.Perm (Fin q), sigma (some e) j = nperm q * (q%2 : ℕ) / (q : ℝ) := by
  let U : Fin q → ℝ := fun k => ∑ e : Equiv.Perm (Fin q), sigma (some e) k
  have he (k : Fin q) : U k = U j := by
    simpa [U, sigma, negSigns, Equiv.trans_apply] using
      (perm_reindex (Equiv.swap j k) (fun e => sigma (some e) j))
  have hh : ∑ k, U k = (q : ℝ) * U j := by simp [he]
  have hs : ∑ k, U k = nperm q * (q%2 : ℕ) := by
    unfold U
    rw [Finset.sum_comm]
    simp [signed_sum, nperm]
  change U j = _
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  exact (eq_div_iff hqR.ne').2 (by linarith only [hh, hs])

noncomputable def cov {q : ℕ} (j k : Fin q) : ℝ :=
  mix q + ((1-mix q)/nperm q) * ∑ e : Equiv.Perm (Fin q), sigma (some e) j * sigma (some e) k

lemma cov_eq_sum {q : ℕ} (j k : Fin q) :
    cov j k = ∑ a : Row q, mass a * (sigma a j * sigma a k) := by
  simp [cov, sigma, negSigns, Fintype.sum_option, mass, Finset.mul_sum]

lemma cov_diag {q : ℕ} (j : Fin q) : cov j j = 1 := by
  simp only [cov, ← pow_two, signed_square, Finset.sum_const, nsmul_eq_mul, mul_one]
  change mix q + (1-mix q)/nperm q * nperm q = 1
  field_simp [(nperm_pos q).ne']
  ring

lemma cov_row {q : ℕ} (hq : 2 ≤ q) (j : Fin q) : ∑ k, cov j k = 1 := by
  simp only [cov, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, signed_sum, ← Finset.sum_mul, sign_first hq j]
  have hn := (nperm_pos q).ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  calc
    _ = mix q * (q : ℝ) + (1-mix q) * (q%2 : ℕ)^2 / (q : ℝ) := by
      field_simp [hn, hqR] <;> ring
    _ = 1 := (mix_eqns hq).2

lemma cov_off {q : ℕ} (hq : 2 ≤ q) (j k : Fin q) (hjk : k ≠ j) : cov j k = 0 := by
  have he (l : Fin q) (hl : l ≠ j) : cov j l = cov j k := by
    have hj : (Equiv.swap k l) j = j := Equiv.swap_apply_of_ne_of_ne hjk.symm hl.symm
    have h := perm_reindex (Equiv.swap k l) (fun e => sigma (some e) j * sigma (some e) k)
    have hv : (∑ e : Equiv.Perm (Fin q), sigma (some e) j * sigma (some e) l) =
        ∑ e : Equiv.Perm (Fin q), sigma (some e) j * sigma (some e) k := by
      simpa [sigma, negSigns, Equiv.trans_apply, hj] using h
    simp only [cov, hv]
  have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin q)) (cov j) (Finset.mem_univ j)
  rw [cov_row hq, cov_diag] at hs
  have h0 : ∑ l ∈ (Finset.univ : Finset (Fin q)).erase j, cov j l = 0 := by linarith
  have hh : ∑ l ∈ (Finset.univ : Finset (Fin q)).erase j, cov j l =
      ((q-1 : ℕ) : ℝ) * cov j k := by
    calc
      _ = ∑ _ ∈ (Finset.univ : Finset (Fin q)).erase j, cov j k :=
        Finset.sum_congr rfl fun l hl => he l (Finset.ne_of_mem_erase hl)
      _ = _ := by simp [Finset.card_erase_of_mem (Finset.mem_univ j), nsmul_eq_mul]
  have hp : (0 : ℝ) < ((q-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < q-1 by omega)
  rcases mul_eq_zero.mp (hh ▸ h0) with h | h
  · exact (hp.ne' h).elim
  · exact h

lemma mass_mean {q : ℕ} (hq : 2 ≤ q) (x : Fin q → ℝ) :
    ∑ a : Row q, mass a * rowSq a x = ∑ j, (x j)^2 := by
  simp only [rowSq, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  calc
    (∑ k, ∑ a : Row q, mass a * (sigma a k * x k * (sigma a j * x j))) =
        ∑ k, cov j k * (x j * x k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [cov_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = x j * x j := by
      rw [← Fintype.sum_ite_eq j (fun k => x j * x k)]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases he : j = k
      · subst k
        simp [cov_diag]
      · simp [he, cov_off hq j k (fun h => he h.symm)]

lemma rowSq_nonneg {q : ℕ} (a : Row q) (x : Fin q → ℝ) : 0 ≤ rowSq a x := sq_nonneg _

lemma signed_bound {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (x : α → ℝ) (hx : ∀ j, 0 ≤ x j) (C : ℝ)
    (hp : ((Finset.univ.filter p).card : ℝ) ≤ C)
    (hn : ((Finset.univ.filter fun j => ¬ p j).card : ℝ) ≤ C) :
    (∑ j, (if p j then (-1:ℝ) else 1)*x j)^2 ≤ C * ∑ j, (x j)^2 := by
  let a := ∑ j ∈ Finset.univ.filter p, x j
  let b := ∑ j ∈ Finset.univ.filter (fun j => ¬p j), x j
  have ha : 0 ≤ a := Finset.sum_nonneg (fun j _ => hx j)
  have hb : 0 ≤ b := Finset.sum_nonneg (fun j _ => hx j)
  have hC : 0 ≤ C := (by positivity : (0:ℝ) ≤ ((Finset.univ.filter p).card : ℝ)).trans hp
  have hh (s : Finset α) (hs : (s.card : ℝ) ≤ C) :
      (∑ j ∈ s, x j)^2 ≤ C * ∑ j, (x j)^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) x
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h.trans (mul_le_mul hs (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun j _ _ => sq_nonneg _)) (Finset.sum_nonneg fun j _ => sq_nonneg _) hC)
  have he : (∑ j, (if p j then (-1:ℝ) else 1)*x j) = b-a := by
    simp only [a, b, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : p j <;> simp [h]
  rw [he]
  rcases le_total a b with h | h
  · have ht : 0 ≤ b-a := sub_nonneg.mpr h
    exact (pow_le_pow_left₀ ht (by linarith) 2).trans (hh _ hn)
  · rw [← neg_sub a b, neg_sq]
    have ht : 0 ≤ a-b := sub_nonneg.mpr h
    exact (pow_le_pow_left₀ ht (by linarith) 2).trans (hh _ hp)

lemma rowSq_le {q : ℕ} (a : Row q) (x : Fin q → ℝ) (hx : ∀ j, 0 ≤ x j) :
    rowSq a x ≤ cap a * ∑ j, (x j)^2 := by
  cases a with
  | none =>
    simpa [rowSq, sigma, negSigns, cap] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin q => (1:ℝ)) x)
  | some e =>
    have hn : (Finset.univ.filter fun j => ¬(e j).val < q/2).card = q-q/2 := by
      have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => (e j).val < q/2)
      rw [perm_count, Finset.card_univ, Fintype.card_fin] at h
      omega
    have hp : ((q/2 : ℕ) : ℝ) ≤ ((q-q/2 : ℕ) : ℝ) := by exact_mod_cast (show q/2 ≤ q-q/2 by omega)
    simpa [rowSq, sigma, negSigns, cap] using
      (signed_bound (fun j => (e j).val < q/2) x hx ((q-q/2 : ℕ) : ℝ) (by rw [perm_count]; exact hp) (by rw [hn]))

lemma tilt_cancel {q : ℕ} (hq : 2 ≤ q) (a : Row q) : tilt a * invTilt a = mass a := by
  have hK : kappa q ≠ 0 := by linarith [kappa_ge hq]
  simp only [tilt, invTilt]
  field_simp [hK, (cap_pos hq a).ne']

noncomputable def law {q b : ℕ} (a : Fin b → Row q) : ℝ := ∏ i, tilt (a i)

noncomputable def factor {q b : ℕ} (a : Fin b → Row q) : ℝ := ∏ i, invTilt (a i)

def value {q b : ℕ} (a : Fin b → Row q) (x : Fin b → Fin q → ℝ) : ℝ :=
  ∏ i, rowSq (a i) (x i)

lemma law_nonneg {q b : ℕ} (hq : 2 ≤ q) (a : Fin b → Row q) : 0 ≤ law a :=
  Finset.prod_nonneg fun i _ => tilt_nonneg hq (a i)

lemma law_total {q b : ℕ} (hq : 2 ≤ q) : ∑ a : Fin b → Row q, law a = 1 := by
  unfold law
  rw [← Fintype.prod_sum]
  simp [tilt_total hq]

lemma factor_nonneg {q b : ℕ} (hq : 2 ≤ q) (a : Fin b → Row q) : 0 ≤ factor a := by
  apply Finset.prod_nonneg
  intro i hi
  exact div_nonneg (by linarith [kappa_ge hq]) (cap_pos hq (a i)).le

lemma test_nonneg {q b : ℕ} (hq : 2 ≤ q) (a : Fin b → Row q) (x : Fin b → Fin q → ℝ) :
    0 ≤ factor a * value a x :=
  mul_nonneg (factor_nonneg hq a) (Finset.prod_nonneg fun i _ => rowSq_nonneg _ _)

lemma test_le {q b : ℕ} (hq : 2 ≤ q) (a : Fin b → Row q) (x : Fin b → Fin q → ℝ)
    (hx : ∀ i j, 0 ≤ x i j) (hu : ∀ i, ∑ j, (x i j)^2 = 1) :
    factor a * value a x ≤ kappa q ^ b := by
  unfold factor value
  rw [← Finset.prod_mul_distrib, show kappa q ^ b = ∏ _ : Fin b, kappa q by simp]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact mul_nonneg (div_nonneg (by linarith [kappa_ge hq]) (cap_pos hq (a i)).le) (rowSq_nonneg _ _)
  · intro i hi
    have h := rowSq_le (a i) (x i) (hx i)
    rw [hu, mul_one] at h
    have hc := cap_pos hq (a i)
    have hk : 0 ≤ kappa q := by linarith [kappa_ge hq]
    change kappa q / cap (a i) * rowSq (a i) (x i) ≤ kappa q
    calc
      _ ≤ kappa q / cap (a i) * cap (a i) := mul_le_mul_of_nonneg_left h (div_nonneg hk hc.le)
      _ = _ := div_mul_cancel₀ _ hc.ne'

lemma test_mean {q b : ℕ} (hq : 2 ≤ q) (x : Fin b → Fin q → ℝ)
    (hu : ∀ i, ∑ j, (x i j)^2 = 1) :
    ∑ a : Fin b → Row q, law a * (factor a * value a x) = 1 := by
  simp only [law, factor, value, ← Finset.prod_mul_distrib, ← mul_assoc, tilt_cancel hq]
  rw [← Fintype.prod_sum (fun i a => mass a * rowSq a (x i))]
  simp [mass_mean hq, hu]

private theorem sample_exp_quadratic {x : ℝ} (hx : |x| ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + (2 / 3 : ℝ) * x ^ 2 := by
  have h := (abs_le.mp (Real.exp_bound (n := 3) (show |x| ≤ 1 by linarith) (by decide))).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hc : |x| ^ 3 ≤ (1 / 2 : ℝ) * x ^ 2 := by
    calc
      |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
  nlinarith only [h, hc, sq_nonneg x]

private theorem sample_mgf {Ω : Type*} [Fintype Ω] (μ f : Ω → ℝ) {B θ : ℝ}
    (hμ : ∀ a, 0 ≤ μ a) (hμ1 : ∑ a, μ a = 1)
    (hf : ∀ a, 0 ≤ f a) (hfB : ∀ a, f a ≤ B) (hf1 : ∑ a, μ a * f a = 1)
    (hθ : |θ| * B ≤ 1 / 2) :
    ∑ a, μ a * Real.exp (θ * f a) ≤ Real.exp (θ + (2 / 3 : ℝ) * θ ^ 2 * B) := by
  calc
    ∑ a, μ a * Real.exp (θ * f a)
        ≤ ∑ a, (μ a + θ * (μ a * f a) + (2 / 3 : ℝ) * θ ^ 2 * B * (μ a * f a)) := by
      refine Finset.sum_le_sum fun a _ => ?_
      have ha : |θ * f a| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_nonneg (hf a)]
        exact (mul_le_mul_of_nonneg_left (hfB a) (abs_nonneg θ)).trans hθ
      have hs : f a ^ 2 ≤ B * f a := by
        simpa [pow_two] using mul_le_mul_of_nonneg_right (hfB a) (hf a)
      calc
        μ a * Real.exp (θ * f a) ≤ μ a * (1 + θ * f a + (2 / 3 : ℝ) * (θ * f a) ^ 2) :=
          mul_le_mul_of_nonneg_left (sample_exp_quadratic ha) (hμ a)
        _ ≤ μ a * (1 + θ * f a + (2 / 3 : ℝ) * (θ ^ 2 * (B * f a))) := by
          rw [mul_pow]
          gcongr
          exact hμ a
        _ = _ := by ring
    _ = 1 + (θ + (2 / 3 : ℝ) * θ ^ 2 * B) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hf1, mul_one]
      ring
    _ ≤ _ := by linarith [Real.add_one_le_exp (θ + (2 / 3 : ℝ) * θ ^ 2 * B)]

private theorem sample_factor {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (t : ℕ) :
    ∑ s : Fin t → Ω, ∏ i, f (s i) = (∑ a, f a) ^ t := by
  classical
  simpa using (Finset.sum_prod_piFinset (ι := Fin t) (Finset.univ : Finset Ω) (fun _ a => f a))

/-- A uniform sample simultaneously estimates every finite bounded mean-one test. -/
theorem sample {Ω G : Type*} [Fintype Ω] [Nonempty Ω] [Fintype G]
    (μ : Ω → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hμ1 : ∑ a, μ a = 1)
    (F : G → Ω → ℝ) {B P L : ℝ} (hF : ∀ g a, 0 ≤ F g a)
    (hFB : ∀ g a, F g a ≤ B) (hF1 : ∀ g, ∑ a, μ a * F g a = 1)
    (hB : 1 ≤ B) (hP : 2 ≤ P) (hL : 0 ≤ L) (hG : (Fintype.card G : ℝ) ≤ Real.exp L) :
    ∃ (t : ℕ) (_ht : 0 < t) (s : Fin t → Ω),
      (t : ℝ) ≤ 1 + 192 * P ^ 2 * B * (2 + L) ∧
      ∀ g, |(∑ h, F g (s h)) / (t : ℝ) - 1| ≤ 1 / (8 * P) := by
  classical
  let ε : ℝ := 1 / (8 * P)
  let lam : ℝ := ε / B
  let N : ℝ := 192 * P ^ 2 * B * (2 + L)
  let t : ℕ := ⌈N⌉₊
  let c : ℝ := ε ^ 2 / (3 * B)
  have hb : 0 < B := by linarith
  have hp : 0 < P := by linarith
  have he : 0 < ε := by dsimp [ε]; positivity
  have hLam : 0 < lam := div_pos he hb
  have hLamEq : lam * B = ε := div_mul_cancel₀ ε hb.ne'
  have hε : ε ≤ 1 / 2 := by
    dsimp [ε]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * P)).2 (by linarith)
  have hN : 0 < N := by dsimp [N]; positivity
  have hNt : N ≤ (t : ℝ) := Nat.le_ceil N
  have htR : (0 : ℝ) < t := hN.trans_le hNt
  have ht : 0 < t := by exact_mod_cast htR
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hNc : N * c = 2 + L := by
    dsimp [N, c, ε]
    field_simp
    <;> ring
  have htc : 2 + L ≤ (t : ℝ) * c := hNc ▸ mul_le_mul_of_nonneg_right hNt hc
  let W (s : Fin t → Ω) : ℝ := ∏ i, μ (s i)
  have hW (s : Fin t → Ω) : 0 ≤ W s := Finset.prod_nonneg fun i _ => hμ (s i)
  have hW1 : ∑ s, W s = 1 := by simp only [W, sample_factor, hμ1, one_pow]
  let D (g : G) (s : Fin t → Ω) : ℝ := (∑ i, F g (s i)) - t
  let E (g : G) (θ : ℝ) (s : Fin t → Ω) : ℝ := Real.exp (θ * D g s - (t : ℝ) * lam * ε)
  have hmoment (g : G) (θ : ℝ) (hθ : |θ| * B ≤ 1 / 2) (hθsq : θ ^ 2 = lam ^ 2) :
      ∑ s, W s * E g θ s ≤ Real.exp (-(t : ℝ) * c) := by
    calc
      ∑ s, W s * E g θ s
          = Real.exp (-(t : ℝ) * (θ + lam * ε)) * (∑ a, μ a * Real.exp (θ * F g a)) ^ t := by
        rw [← sample_factor, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        dsimp [E, D, W]
        have ha : θ * ((∑ i, F g (s i)) - (t : ℝ)) - (t : ℝ) * lam * ε =
            -(t : ℝ) * (θ + lam * ε) + ∑ i, θ * F g (s i) := by
          rw [← Finset.mul_sum]
          ring
        rw [ha, Real.exp_add, Real.exp_sum, Finset.prod_mul_distrib, mul_left_comm]
      _ ≤ Real.exp (-(t : ℝ) * (θ + lam * ε)) * (Real.exp (θ + (2 / 3 : ℝ) * θ ^ 2 * B)) ^ t := by
        gcongr
        · exact Finset.sum_nonneg fun a _ => mul_nonneg (hμ a) (Real.exp_pos _).le
        · exact sample_mgf μ (F g) hμ hμ1 (hF g) (hFB g) (hF1 g) hθ
      _ = Real.exp (-(t : ℝ) * c) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, hθsq]
        congr 1
        dsimp [c, lam]
        field_simp
        <;> ring
  let bad (g : G) (s : Fin t → Ω) : ℝ := if (t : ℝ) * ε < |D g s| then 1 else 0
  have hbad (g : G) (s : Fin t → Ω) : 0 ≤ bad g s := by
    dsimp [bad]; split <;> norm_num
  have hdom (g : G) (s : Fin t → Ω) : bad g s ≤ E g lam s + E g (-lam) s := by
    have hpos (θ : ℝ) : 0 ≤ E g θ s := (Real.exp_pos _).le
    by_cases hv : (t : ℝ) * ε < |D g s|
    · simp only [bad, ite_eq_left hv]
      rcases le_total 0 (D g s) with hd | hd
      · rw [abs_of_nonneg hd] at hv
        have hh : 0 ≤ lam * D g s - (t : ℝ) * lam * ε := by
          nlinarith [mul_nonneg hLam.le (sub_nonneg.mpr hv.le)]
        exact (Real.one_le_exp hh).trans (le_add_of_nonneg_right (hpos (-lam)))
      · rw [abs_of_nonpos hd] at hv
        have hh : 0 ≤ -lam * D g s - (t : ℝ) * lam * ε := by
          nlinarith [mul_nonneg hLam.le (sub_nonneg.mpr hv.le)]
        exact (Real.one_le_exp hh).trans (le_add_of_nonneg_left (hpos lam))
    · simp only [bad, ite_eq_right hv]
      exact add_nonneg (hpos lam) (hpos (-lam))
  have htail (g : G) : ∑ s, W s * bad g s ≤ 2 * Real.exp (-(t : ℝ) * c) := by
    have hLamB : |lam| * B ≤ 1 / 2 := by rw [abs_of_pos hLam, hLamEq]; exact hε
    calc
      ∑ s, W s * bad g s ≤ ∑ s, W s * (E g lam s + E g (-lam) s) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hdom g s) (hW s)
      _ ≤ 2 * Real.exp (-(t : ℝ) * c) := by
        simp only [mul_add, Finset.sum_add_distrib]
        linarith [hmoment g lam hLamB rfl,
          hmoment g (-lam) (by rwa [abs_neg]) (by ring)]
  have hunion : ∑ s, W s * ∑ g, bad g s < 1 := by
    calc
      ∑ s, W s * ∑ g, bad g s = ∑ g, ∑ s, W s * bad g s := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ (Fintype.card G : ℝ) * (2 * Real.exp (-(t : ℝ) * c)) := by
        simpa using Finset.sum_le_sum (s := (Finset.univ : Finset G)) (fun g _ => htail g)
      _ ≤ Real.exp L * (2 * Real.exp (-(2 + L))) := by
        have hec : -(t : ℝ) * c ≤ -(2 + L) := by linarith
        gcongr
      _ = 2 * Real.exp (-2) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ < 1 := by
        have h2 : (2 : ℝ) < Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
        calc
          2 * Real.exp (-2) < Real.exp 2 * Real.exp (-2) := mul_lt_mul_of_pos_right h2 (Real.exp_pos _)
          _ = 1 := by rw [← Real.exp_add]; norm_num
  have hex : ∃ s : Fin t → Ω, ∀ g, |D g s| ≤ (t : ℝ) * ε := by
    by_contra! hh
    have hall (s : Fin t → Ω) : 1 ≤ ∑ g, bad g s := by
      obtain ⟨g, hg⟩ := hh s
      calc
        1 = bad g s := by simp [bad, hg]
        _ ≤ ∑ k, bad k s := Finset.single_le_sum (fun k _ => hbad k s) (Finset.mem_univ g)
    have hle : 1 ≤ ∑ s, W s * ∑ g, bad g s := by
      rw [← hW1]
      exact Finset.sum_le_sum fun s _ => by simpa using mul_le_mul_of_nonneg_left (hall s) (hW s)
    exact (not_lt_of_ge hle) hunion
  obtain ⟨s, hs⟩ := hex
  refine ⟨t, ht, s, ?_, fun g => ?_⟩
  · have := (Nat.ceil_lt_add_one hN.le).le
    dsimp [t, N] at this
    linarith
  · have heq : (∑ i, F g (s i)) / (t : ℝ) - 1 = D g s / (t : ℝ) := by
      dsimp [D]
      field_simp
    rw [heq, abs_div, abs_of_pos htR]
    change |D g s| / (t : ℝ) ≤ ε
    exact (div_le_iff₀ htR).2 (by simpa only [mul_comm] using hs g)

/-- Choose one normalized representative for each occupied rounding box, giving
priority to the canonical coordinate vector in its box. -/
theorem grid (q b : ℕ) (hq : 2 ≤ q) :
    let L := (b : ℝ) * q * Real.log (2 + 72 * ((b : ℝ) + 1) * q)
    ∃ G : Finset (Fin b → Fin q → ℝ),
      (∀ x ∈ G, (∀ i j, 0 ≤ x i j) ∧ ∀ i, ∑ j, (x i j)^2 = 1) ∧
      (G.card : ℝ) ≤ Real.exp L ∧
      (∀ x : Fin b → Fin q → ℝ, (∀ i j, 0 ≤ x i j) → (∀ i, ∑ j, (x i j)^2 = 1) →
        ∃ y ∈ G, ∀ i, ∑ j, |x i j - y i j| ≤ 1 / (36 * ((b : ℝ) + 1))) ∧
      (fun _ j => if j.val = 0 then (1 : ℝ) else 0) ∈ G := by
  classical
  let m : ℕ := 72 * (b + 1) * q
  have hm : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by dsimp [m]; positivity)
  have hmval : (m : ℝ) = 72 * ((b : ℝ) + 1) * q := by simp [m]
  let s : Fin b → Fin q → ℝ := fun _ j => if j.val = 0 then 1 else 0
  let j₀ : Fin q := ⟨0, by omega⟩
  let Unit : (Fin b → Fin q → ℝ) → Prop := fun x =>
    (∀ i j, 0 ≤ x i j) ∧ ∀ i, ∑ j, (x i j)^2 = 1
  have hs : Unit s := by
    constructor
    · intro i j
      dsimp [s]
      split <;> norm_num
    · intro i
      calc
        ∑ j : Fin q, (s i j)^2 = (s i j₀)^2 := by
          apply Finset.sum_eq_single j₀
          · intro j _ hj
            have hval : j.val ≠ 0 := fun h => hj (Fin.ext h)
            simp [s, hval]
          · simp
        _ = 1 := by norm_num [s, j₀]
  let A := Fin b → Fin q → Fin (m + 1)
  let Box : A → (Fin b → Fin q → ℝ) → Prop := fun a x =>
    ∀ i j, ((a i j).val : ℝ) ≤ (m : ℝ) * x i j ∧
      (m : ℝ) * x i j ≤ ((a i j).val : ℝ) + 1
  have enc (x : Fin b → Fin q → ℝ) (hx : Unit x) : ∃ a : A, Box a x := by
    have hxle (i : Fin b) (j : Fin q) : x i j ≤ 1 := by
      have hsq : (x i j)^2 ≤ 1 := by
        rw [← hx.2 i]
        exact Finset.single_le_sum (f := fun k => (x i k)^2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      nlinarith [hx.1 i j]
    have hfloor (i : Fin b) (j : Fin q) : ⌊(m : ℝ) * x i j⌋₊ < m + 1 := by
      apply (Nat.floor_lt (mul_nonneg hm.le (hx.1 i j))).2
      push_cast
      calc
        (m : ℝ) * x i j ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left (hxle i j) hm.le
        _ < (m : ℝ) + 1 := by simp
    refine ⟨fun i j => ⟨_, hfloor i j⟩, ?_⟩
    intro i j
    exact ⟨Nat.floor_le (mul_nonneg hm.le (hx.1 i j)), (Nat.lt_floor_add_one _).le⟩
  let pick (a : A) : Fin b → Fin q → ℝ :=
    if Box a s then s else if h : ∃ x, Unit x ∧ Box a x then h.choose else s
  have pick_unit (a : A) : Unit (pick a) := by
    dsimp [pick]
    split
    · exact hs
    · split
      · rename_i h
        exact h.choose_spec.1
      · exact hs
  have pick_box (a : A) (h : ∃ x, Unit x ∧ Box a x) : Box a (pick a) := by
    by_cases h' : Box a s
    · simp [pick, h']
    · simpa [pick, h', h] using h.choose_spec.2
  let G : Finset (Fin b → Fin q → ℝ) := Finset.univ.image pick
  have iG (a : A) : pick a ∈ G := Finset.mem_image_of_mem pick (Finset.mem_univ a)
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact pick_unit a
  · have hc : G.card ≤ (m + 1)^(q * b) := by
      calc
        G.card ≤ (Finset.univ : Finset A).card := Finset.card_image_le
        _ = (m + 1)^(q * b) := by simp [A, ← pow_mul]
    have hb : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hpow : ((m : ℝ) + 2)^(q * b) =
        Real.exp ((b : ℝ) * q * Real.log (2 + 72 * ((b : ℝ) + 1) * q)) := by
      calc
        ((m : ℝ) + 2)^(q * b) = (Real.exp (Real.log ((m : ℝ) + 2)))^(q * b) := by
          rw [Real.exp_log hb]
        _ = _ := by
          rw [← Real.exp_nat_mul, hmval, add_comm (72 * ((b : ℝ) + 1) * q) 2]
          push_cast
          congr 1
          ring
    calc
      (G.card : ℝ) ≤ ((m : ℝ) + 1)^(q * b) := by exact_mod_cast hc
      _ ≤ ((m : ℝ) + 2)^(q * b) := by gcongr; linarith
      _ = _ := hpow
  · intro x hx hnorm
    obtain ⟨a, ha⟩ := enc x ⟨hx, hnorm⟩
    have hy := pick_box a ⟨x, ⟨hx, hnorm⟩, ha⟩
    refine ⟨pick a, iG a, fun i => ?_⟩
    have hdiff (j : Fin q) : |x i j - pick a i j| ≤ 1 / (m : ℝ) := by
      have hj := ha i j
      have hk := hy i j
      rw [abs_le]
      constructor
      · rw [← neg_div, div_le_iff₀ hm]
        nlinarith only [hj.1, hk.2]
      · rw [le_div_iff₀ hm]
        nlinarith only [hj.2, hk.1]
    calc
      ∑ j : Fin q, |x i j - pick a i j| ≤ ∑ _ : Fin q, 1 / (m : ℝ) :=
        Finset.sum_le_sum fun j _ => hdiff j
      _ = 1 / (72 * ((b : ℝ) + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [hmval]
        have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
        field_simp
      _ ≤ _ := by gcongr; linarith
  · obtain ⟨a, ha⟩ := enc s hs
    simpa [pick, ha] using iG a

private noncomputable def extNorm {q : ℕ} (u : Fin q → ℝ) : ℝ :=
  Real.sqrt (∑ j, (u j)^2)

private theorem extNorm_nonneg {q : ℕ} (u : Fin q → ℝ) : 0 ≤ extNorm u :=
  Real.sqrt_nonneg _

private theorem extNorm_sq {q : ℕ} (u : Fin q → ℝ) :
    (extNorm u)^2 = ∑ j, (u j)^2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (u j))

private theorem extNorm_eq_zero {q : ℕ} {u : Fin q → ℝ} (h : extNorm u = 0) : u = 0 := by
  funext j
  have hj : (u j)^2 ≤ ∑ k, (u k)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (u k)) (Finset.mem_univ j)
  rw [← extNorm_sq u, h] at hj
  change u j = 0
  nlinarith

private theorem extNorm_normalize {q : ℕ} {u : Fin q → ℝ} (hu : extNorm u ≠ 0) :
    ∑ j, (((extNorm u)⁻¹ • u) j)^2 = 1 := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, ← extNorm_sq u]
  field_simp

private def extMixed {q : ℕ} {s : Type*} [Fintype s]
    (c : s → ℝ) (L : s → (Fin q → ℝ) →ₗ[ℝ] ℝ) (u v : Fin q → ℝ) : ℝ :=
  ∑ k, c k * L k u * L k v

private theorem extMixed_sub {q : ℕ} {s : Type*} [Fintype s]
    (c : s → ℝ) (L : s → (Fin q → ℝ) →ₗ[ℝ] ℝ) (u v z : Fin q → ℝ) :
    extMixed c L (u - v) z = extMixed c L u z - extMixed c L v z := by
  simp [extMixed, mul_sub, sub_mul, Finset.sum_sub_distrib]

private theorem extMixed_smul {q : ℕ} {s : Type*} [Fintype s]
    (c : s → ℝ) (L : s → (Fin q → ℝ) →ₗ[ℝ] ℝ) (a b : ℝ) (u v : Fin q → ℝ) :
    extMixed c L (a • u) (b • v) = a * b * extMixed c L u v := by
  simp only [extMixed, map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem extMixed_bound {q : ℕ} {s : Type*} [Fintype s]
    (c : s → ℝ) (L : s → (Fin q → ℝ) →ₗ[ℝ] ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hQ : ∀ u, (∀ j, 0 ≤ u j) → (∑ j, (u j)^2) = 1 →
      |∑ k, c k * (L k u)^2| ≤ M)
    (u v : Fin q → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) :
    |extMixed c L u v| ≤ 3 * M * extNorm u * extNorm v := by
  let Q : (Fin q → ℝ) → ℝ := fun z => ∑ k, c k * (L k z)^2
  have normalize_nonneg (z : Fin q → ℝ) (hz : ∀ j, 0 ≤ z j) :
      ∀ j, 0 ≤ ((extNorm z)⁻¹ • z) j :=
    fun j => mul_nonneg (inv_nonneg.mpr (extNorm_nonneg z)) (hz j)
  have rescale (z : Fin q → ℝ) (hz : extNorm z ≠ 0) :
      extNorm z • ((extNorm z)⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
  have scaledQ (a : ℝ) (z : Fin q → ℝ) : Q (a • z) = a^2 * Q z := by
    simp only [Q, map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have generalQ (z : Fin q → ℝ) (hz : ∀ j, 0 ≤ z j) :
      |Q z| ≤ M * ∑ j, (z j)^2 := by
    by_cases hn : extNorm z = 0
    · simp [extNorm_eq_zero hn, Q]
    · calc
        |Q z| = (extNorm z)^2 * |Q ((extNorm z)⁻¹ • z)| := by
          conv_lhs => rw [← rescale z hn, scaledQ, abs_mul, abs_of_nonneg (sq_nonneg _)]
        _ ≤ (extNorm z)^2 * M := mul_le_mul_of_nonneg_left
          (hQ _ (normalize_nonneg z hz) (extNorm_normalize hn)) (sq_nonneg _)
        _ = _ := by rw [mul_comm, extNorm_sq]
  have unitMixed (a b : Fin q → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
      (ha' : ∑ j, (a j)^2 = 1) (hb' : ∑ j, (b j)^2 = 1) :
      |extMixed c L a b| ≤ 3 * M := by
    have hnorm : ∑ j, ((a + b) j)^2 ≤ 4 := calc
      _ ≤ ∑ j, (2 * (a j)^2 + 2 * (b j)^2) := by
        apply Finset.sum_le_sum
        intro j _
        change (a j + b j)^2 ≤ _
        nlinarith [sq_nonneg (a j - b j)]
      _ = 4 := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ha', hb']; norm_num
    have hpol : 2 * extMixed c L a b = Q (a + b) - Q a - Q b := by
      simp only [extMixed, Q, Finset.mul_sum, ← Finset.sum_sub_distrib, map_add]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hsum : |Q (a + b)| ≤ 4 * M := by
      calc
        _ ≤ M * ∑ j, ((a + b) j)^2 := generalQ _ (fun j => add_nonneg (ha j) (hb j))
        _ ≤ M * 4 := mul_le_mul_of_nonneg_left hnorm hM
        _ = _ := mul_comm _ _
    have htri := abs_sub (Q (a + b) - Q a) (Q b)
    have htri' := abs_sub (Q (a + b)) (Q a)
    rw [← hpol, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htri
    linarith [hQ a ha ha', hQ b hb hb']
  by_cases hnu : extNorm u = 0
  · simp [extNorm_eq_zero hnu, extMixed, extNorm]
  by_cases hnv : extNorm v = 0
  · simp [extNorm_eq_zero hnv, extMixed, extNorm]
  have hmul : 0 ≤ extNorm u * extNorm v := mul_nonneg (extNorm_nonneg u) (extNorm_nonneg v)
  calc
    |extMixed c L u v| = extNorm u * extNorm v *
        |extMixed c L ((extNorm u)⁻¹ • u) ((extNorm v)⁻¹ • v)| := by
      conv_lhs => rw [← rescale u hnu, ← rescale v hnv, extMixed_smul, abs_mul, abs_of_nonneg hmul]
    _ ≤ extNorm u * extNorm v * (3 * M) := mul_le_mul_of_nonneg_left
      (unitMixed _ _ (normalize_nonneg u hu) (normalize_nonneg v hv)
        (extNorm_normalize hnu) (extNorm_normalize hnv)) hmul
    _ = _ := by ring

private theorem extQuadratic_increment {q : ℕ} {s : Type*} [Fintype s]
    (c : s → ℝ) (L : s → (Fin q → ℝ) →ₗ[ℝ] ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hQ : ∀ u, (∀ j, 0 ≤ u j) → (∑ j, (u j)^2) = 1 →
      |∑ k, c k * (L k u)^2| ≤ M)
    (u v : Fin q → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (hu' : ∑ j, (u j)^2 = 1) (hv' : ∑ j, (v j)^2 = 1) :
    |(∑ k, c k * (L k u)^2) - (∑ k, c k * (L k v)^2)| ≤
      12 * M * extNorm (u - v) := by
  let d := u - v
  let pos : Fin q → ℝ := fun j => max (d j) 0
  let neg : Fin q → ℝ := fun j => max (-d j) 0
  have hd : d = pos - neg := by
    funext j
    change d j = max (d j) 0 - max (-d j) 0
    by_cases h : 0 ≤ d j
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
      ring
  have hpos : extNorm pos ≤ extNorm d := by
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j _
    change (max (d j) 0)^2 ≤ (d j)^2
    rcases le_total 0 (d j) with h | h
    · rw [max_eq_left h]
    · simpa [max_eq_right h] using sq_nonneg (d j)
  have hneg : extNorm neg ≤ extNorm d := by
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j _
    change (max (-d j) 0)^2 ≤ (d j)^2
    rcases le_total 0 (-d j) with h | h
    · rw [max_eq_left h]; ring_nf; rfl
    · simpa [max_eq_right h] using sq_nonneg (d j)
  have hmixed (z : Fin q → ℝ) (hz : ∀ j, 0 ≤ z j) (hz' : ∑ j, (z j)^2 = 1) :
      |extMixed c L d z| ≤ 6 * M * extNorm d := by
    have hnz : extNorm z = 1 := by simp [extNorm, hz']
    have hp := extMixed_bound c L M hM hQ pos z (fun j => le_max_right _ _) hz
    have hn := extMixed_bound c L M hM hQ neg z (fun j => le_max_right _ _) hz
    rw [hnz, mul_one] at hp hn
    have hp' := mul_le_mul_of_nonneg_left hpos (by positivity : 0 ≤ 3 * M)
    have hn' := mul_le_mul_of_nonneg_left hneg (by positivity : 0 ≤ 3 * M)
    conv_lhs => rw [hd, extMixed_sub]
    linarith [abs_sub (extMixed c L pos z) (extMixed c L neg z)]
  have hdiff : (∑ k, c k * (L k u)^2) - (∑ k, c k * (L k v)^2) =
      extMixed c L d u + extMixed c L d v := by
    simp only [d, extMixed, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, map_sub]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hdiff]
  linarith [abs_add_le (extMixed c L d u) (extMixed c L d v), hmixed u hu hu', hmixed v hv hv']

/-- A grid bounds a continuous function with a signed sum-of-squares section in each block. -/
theorem gridToUniform {q b : ℕ} {s : Type*} [Fintype s]
    (f : (Fin b → Fin q → ℝ) → ℝ) (hf : Continuous f)
    (hquadratic : ∀ z i, ∃ (c : s → ℝ) (L : s → (Fin q → ℝ) →ₗ[ℝ] ℝ),
      ∀ u, f (Function.update z i u) = ∑ k, c k * (L k u)^2)
    (G : Set (Fin b → Fin q → ℝ)) (E : ℝ)
    (hcover : ∀ x : Fin b → Fin q → ℝ, (∀ i j, 0 ≤ x i j) →
      (∀ i, ∑ j, (x i j)^2 = 1) →
      ∃ y ∈ G, (∀ i j, 0 ≤ y i j) ∧ (∀ i, ∑ j, (y i j)^2 = 1) ∧
        ∀ i, Real.sqrt (∑ j, (x i j - y i j)^2) ≤ 1 / (36 * ((b : ℝ) + 1)))
    (hbound : ∀ y ∈ G, |f y| ≤ E)
    (x : Fin b → Fin q → ℝ) (hx₀ : ∀ i j, 0 ≤ x i j)
    (hx₁ : ∀ i, ∑ j, (x i j)^2 = 1) : |f x| ≤ 2 * E := by
  classical
  let C : Set (Fin b → Fin q → ℝ) := {z | (∀ i j, 0 ≤ z i j) ∧ (∀ i, ∑ j, (z i j)^2 = 1)}
  have hcoord (i : Fin b) (j : Fin q) : Continuous fun z : Fin b → Fin q → ℝ => z i j :=
    (continuous_apply j).comp (continuous_apply i)
  have hclosed : IsClosed C := by
    have hre : C = (⋂ i : Fin b, ⋂ j : Fin q, {z | 0 ≤ z i j}) ∩
        (⋂ i : Fin b, {z | ∑ j : Fin q, (z i j)^2 = 1}) := by
      ext z
      simp [C]
    rw [hre]
    refine (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le continuous_const (hcoord i j)).inter ?_
    apply isClosed_iInter
    intro i
    exact isClosed_eq (continuous_finsetSum _ fun j _ => (hcoord i j).pow 2) continuous_const
  have hcompact : IsCompact C := by
    apply (isCompact_Icc (a := (0 : Fin b → Fin q → ℝ)) (b := 1)).of_isClosed_subset hclosed
    intro z hz
    change (∀ i j, 0 ≤ z i j) ∧ (∀ i j, z i j ≤ 1)
    refine ⟨hz.1, fun i j => ?_⟩
    have hj : (z i j)^2 ≤ ∑ k, (z i k)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (z i k)) (Finset.mem_univ j)
    rw [hz.2 i] at hj
    nlinarith [hz.1 i j]
  have hx : x ∈ C := ⟨hx₀, hx₁⟩
  obtain ⟨a, ha, hamax⟩ := hcompact.exists_isMaxOn ⟨x, hx⟩ hf.abs.continuousOn
  let M := |f a|
  have hM : 0 ≤ M := abs_nonneg _
  obtain ⟨y, hyG, hy₀, hy₁, hynear⟩ := hcover a ha.1 ha.2
  let δ : ℝ := 1 / (36 * ((b : ℝ) + 1))
  let step (S : Finset (Fin b)) (i : Fin b) := if i ∈ S then y i else a i
  have hstep (S : Finset (Fin b)) : step S ∈ C := by
    constructor
    · intro i j
      by_cases h : i ∈ S <;> simp [step, h, hy₀, ha.1]
    · intro i
      by_cases h : i ∈ S <;> simp [step, h, hy₁, ha.2]
  have hchange (S : Finset (Fin b)) (i : Fin b) (hi : i ∉ S) :
      |f (step (insert i S)) - f (step S)| ≤ 12 * M * δ := by
    have hbefore : Function.update (step S) i (a i) = step S := by
      have hsi : step S i = a i := ite_eq_right hi
      rw [← hsi, Function.update_eq_self]
    have hafter : Function.update (step S) i (y i) = step (insert i S) := by
      funext j
      by_cases h : j = i
      · subst j
        simp [step]
      · simp [step, h]
    obtain ⟨c, L, hc⟩ := hquadratic (step S) i
    have hQ (u : Fin q → ℝ) (hu : ∀ j, 0 ≤ u j) (hu' : ∑ j, (u j)^2 = 1) :
        |∑ k, c k * (L k u)^2| ≤ M := by
      rw [← hc]
      apply hamax
      constructor
      · intro i' j
        by_cases h : i' = i
        · subst i'; simpa using hu j
        · simpa [Function.update_of_ne h] using (hstep S).1 i' j
      · intro i'
        by_cases h : i' = i
        · subst i'; simpa using hu'
        · simpa [Function.update_of_ne h] using (hstep S).2 i'
    have hinc := extQuadratic_increment c L M hM hQ _ _ (ha.1 i) (hy₀ i) (ha.2 i) (hy₁ i)
    rw [← hc, ← hc, hbefore, hafter, abs_sub_comm] at hinc
    exact hinc.trans (mul_le_mul_of_nonneg_left (hynear i) (by positivity))
  have htelescope (S : Finset (Fin b)) : |f (step S) - f a| ≤ (S.card : ℝ) * (12 * M * δ) := by
    induction S using Finset.induction_on with
    | empty =>
      have h : step ∅ = a := by funext i; simp [step]
      simp [h]
    | @insert i S hi ih =>
      calc
        |f (step (insert i S)) - f a| ≤
            |f (step (insert i S)) - f (step S)| + |f (step S) - f a| := abs_sub_le _ _ _
        _ ≤ 12 * M * δ + (S.card : ℝ) * (12 * M * δ) := add_le_add (hchange S i hi) ih
        _ = _ := by rw [Finset.card_insert_of_notMem hi, Nat.cast_succ]; ring
  have hlast : step Finset.univ = y := by funext i; simp [step]
  have htel := htelescope Finset.univ
  rw [hlast, Finset.card_univ, Fintype.card_fin, abs_sub_comm] at htel
  have hbnd : (b : ℝ) * (12 * M * δ) ≤ M / 2 := by
    have hb : (0 : ℝ) ≤ b := by positivity
    have hden : 0 < 36 * ((b : ℝ) + 1) := by positivity
    calc
      _ = (12 * M * b) / (36 * ((b : ℝ) + 1)) := by unfold δ; ring
      _ ≤ _ := (div_le_iff₀ hden).2 (by nlinarith [mul_nonneg hM hb])
  have hmle : M ≤ |f a - f y| + |f y| := by
    simpa [M] using (abs_sub_le (f a) (f y) 0)
  exact (hamax hx).trans (by linarith [hbound y hyG, htel.trans hbnd])

private def extSignForm {q : ℕ} (sign : Fin q → Bool) : (Fin q → ℝ) →ₗ[ℝ] ℝ where
  toFun u := ∑ j, (if sign j then (-1 : ℝ) else 1) * u j
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The grid extension for the signed estimator minus the product of squared norms. -/
theorem gridToUniformEstSubTarget {q b t : ℕ}
    (signs : Fin t → Fin b → Fin q → Bool) (w : Fin t → ℝ)
    (G : Set (Fin b → Fin q → ℝ)) (E : ℝ)
    (hcover : ∀ x : Fin b → Fin q → ℝ, (∀ i j, 0 ≤ x i j) →
      (∀ i, ∑ j, (x i j)^2 = 1) →
      ∃ y ∈ G, (∀ i j, 0 ≤ y i j) ∧ (∀ i, ∑ j, (y i j)^2 = 1) ∧
        ∀ i, Real.sqrt (∑ j, (x i j - y i j)^2) ≤ 1 / (36 * ((b : ℝ) + 1)))
    (hbound : ∀ y ∈ G,
      |(∑ h, w h * ∏ i, (∑ j, (if signs h i j then (-1 : ℝ) else 1) * y i j)^2) -
        ∏ i, ∑ j, (y i j)^2| ≤ E)
    (x : Fin b → Fin q → ℝ) (hx₀ : ∀ i j, 0 ≤ x i j)
    (hx₁ : ∀ i, ∑ j, (x i j)^2 = 1) :
    |(∑ h, w h * ∏ i, (∑ j, (if signs h i j then (-1 : ℝ) else 1) * x i j)^2) -
      ∏ i, ∑ j, (x i j)^2| ≤ 2 * E := by
  classical
  let A (z : Fin b → Fin q → ℝ) (h : Fin t) (i : Fin b) :=
    (∑ j, (if signs h i j then (-1 : ℝ) else 1) * z i j)^2
  let D (z : Fin b → Fin q → ℝ) (i : Fin b) := ∑ j, (z i j)^2
  let f (z : Fin b → Fin q → ℝ) := (∑ h, w h * ∏ i, A z h i) - ∏ i, D z i
  have hcoord (i : Fin b) (j : Fin q) : Continuous fun z : Fin b → Fin q → ℝ => z i j :=
    (continuous_apply j).comp (continuous_apply i)
  have hf : Continuous f := by
    have hAcont (h : Fin t) (i : Fin b) : Continuous (fun z => A z h i) := by
      exact (continuous_finsetSum
        (f := fun j (z : Fin b → Fin q → ℝ) => (if signs h i j then (-1 : ℝ) else 1) * z i j)
        Finset.univ (fun j _ => (hcoord i j).const_mul _)).pow 2
    have hDcont (i : Fin b) : Continuous (fun z => D z i) :=
      continuous_finsetSum (f := fun j (z : Fin b → Fin q → ℝ) => (z i j)^2)
        Finset.univ (fun j _ => (hcoord i j).pow 2)
    exact (continuous_finsetSum (f := fun h z => w h * ∏ i, A z h i) Finset.univ
      (fun h _ => (continuous_finsetProd (f := fun i z => A z h i) Finset.univ
        (fun i _ => hAcont h i)).const_mul _)).sub
      (continuous_finsetProd (f := fun i z => D z i) Finset.univ (fun i _ => hDcont i))
  refine gridToUniform (s := Fin t ⊕ Fin q) f hf ?_ G E hcover hbound x hx₀ hx₁
  intro z i
  let ca (h : Fin t) := ∏ k ∈ Finset.univ.erase i, A z h k
  let cd := ∏ k ∈ Finset.univ.erase i, D z k
  refine ⟨Sum.elim (fun h => w h * ca h) (fun _ => -cd),
    Sum.elim (fun h => extSignForm (signs h i)) (fun j => LinearMap.proj j), ?_⟩
  intro u
  have eraseProd (P : (Fin q → ℝ) → ℝ) :
      (∏ k, P (Function.update z i u k)) = (∏ k ∈ Finset.univ.erase i, P (z k)) * P u := by
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have hA (h : Fin t) : (∏ k, A (Function.update z i u) h k) =
      ca h * (extSignForm (signs h i) u)^2 := by
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
    have hprod : (∏ k ∈ Finset.univ.erase i, A (Function.update z i u) h k) = ca h := by
      apply Finset.prod_congr rfl
      intro k hk
      unfold A
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    rw [hprod]
    simp [A, extSignForm]
  have hD : (∏ k, D (Function.update z i u) k) = cd * ∑ j, (u j)^2 :=
    eraseProd (fun v => ∑ j, (v j)^2)
  change (∑ h, w h * ∏ k, A (Function.update z i u) h k) -
      (∏ k, D (Function.update z i u) k) = _
  simp only [hA, hD, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, LinearMap.proj_apply]
  rw [← Finset.mul_sum, neg_mul, ← sub_eq_add_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  ring

def basisVec {q : ℕ} (j : Fin q) : ℝ := if j.val = 0 then 1 else 0

lemma basisVec_nonneg {q : ℕ} (j : Fin q) : 0 ≤ basisVec j := by
  unfold basisVec
  split <;> norm_num

lemma basisVec_sign_sq {q : ℕ} (hq : 0 < q) (z : Fin q → Bool) :
    (∑ j, (if z j then (-1:ℝ) else 1)*basisVec j)^2 = 1 := by
  let j₀ : Fin q := ⟨0,hq⟩
  rw [show (∑ j : Fin q, (if z j then (-1:ℝ) else 1)*basisVec j) =
      (if z j₀ then (-1:ℝ) else 1)*basisVec j₀ by
    apply Finset.sum_eq_single j₀
    · intro j _ hj
      have hn : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
      simp [basisVec, hn]
    · simp]
  simp only [basisVec, j₀, ite_true, mul_one]
  split <;> norm_num

lemma basisVec_unit {q : ℕ} (hq : 0 < q) : ∑ j : Fin q, basisVec j ^ 2 = 1 := by
  let j₀ : Fin q := ⟨0,hq⟩
  rw [Finset.sum_eq_single j₀]
  · norm_num [basisVec, j₀]
  · intro j _ hj
    have hn : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
    simp [basisVec, hn]
  · simp

lemma root_sum_le_sum_abs {q : ℕ} (z : Fin q → ℝ) :
    Real.sqrt (∑ j, (z j)^2) ≤ ∑ j, |z j| := by
  have hs : 0 ≤ ∑ j, |z j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  apply (Real.sqrt_le_left hs).2
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  rw [← sq_abs, pow_two]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun k _ => abs_nonneg (z k)) hj)
    (abs_nonneg _)

lemma ratio_bound {A S P : ℝ} (hP : 2 ≤ P)
    (hA : |A-1| ≤ 1/(8*P)) (hS : |S-1| ≤ 1/(8*P)) :
    0 < S ∧ |A/S-1| ≤ 1/(2*P) := by
  have hP₀ : 0 < P := by linarith
  have hsmall : 1 / (8*P) ≤ 1/2 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hhalf : 1/2 ≤ S := by linarith [(abs_le.mp hS).1]
  have hs₀ : 0 < S := by linarith
  constructor
  · exact hs₀
  · have he : A/S-1 = (A-S)/S := by
      rw [sub_div, div_self hs₀.ne']
    rw [he, abs_div, abs_of_pos hs₀]
    apply (div_le_iff₀ hs₀).2
    have hd : |A-S| ≤ 1/(8*P) + 1/(8*P) := by
      have ht := abs_sub_le A 1 S
      rw [abs_sub_comm (1:ℝ) S] at ht
      linarith
    have hp' : 0 ≤ 1/(2*P) := by positivity
    calc
      |A-S| ≤ 1/(8*P) + 1/(8*P) := hd
      _ = 1/(2*P)*(1/2) := by ring
      _ ≤ 1/(2*P)*S := mul_le_mul_of_nonneg_left hhalf hp'
lemma rescale {q b t : ℕ} (hq : 0 < q) (z : Fin t → Fin b → Fin q → Bool)
    (w : Fin t → ℝ) (P : ℝ) (hP : 0 < P)
    (hunit : ∀ x : Fin b → Fin q → ℝ, (∀ i j, 0 ≤ x i j) → (∀ i, ∑ j, (x i j)^2 = 1) →
      |(∑ h, w h * ∏ i, (∑ j, (if z h i j then (-1:ℝ) else 1)*x i j)^2)-1| ≤ 1/P)
    (x : Fin b → Fin q → ℝ) (hx : ∀ i j, 0 ≤ x i j) :
    let target := ∏ i, ∑ j, (x i j)^2
    let est := ∑ h, w h * ∏ i, (∑ j, (if z h i j then (-1:ℝ) else 1)*x i j)^2
    (P-1)*target ≤ P*est ∧ P*est ≤ (P+1)*target := by
  let r (i : Fin b) := Real.sqrt (∑ j, (x i j)^2)
  have hr (i : Fin b) : 0 ≤ r i := Real.sqrt_nonneg _
  have hr₂ (i : Fin b) : r i ^ 2 = ∑ j, (x i j)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  let u (i : Fin b) (j : Fin q) := if r i = 0 then basisVec j else x i j / r i
  have hu (i : Fin b) (j : Fin q) : 0 ≤ u i j := by
    unfold u
    split
    · exact basisVec_nonneg _
    · exact div_nonneg (hx i j) (hr i)
  have hscale (i : Fin b) (j : Fin q) : x i j = r i * u i j := by
    unfold u
    split
    · rename_i h
      have hsq : (x i j)^2 ≤ r i ^ 2 := by
        rw [hr₂]
        exact Finset.single_le_sum (fun k _ => sq_nonneg (x i k)) (Finset.mem_univ j)
      simp only [h, zero_pow (by decide : (2:ℕ) ≠ 0), zero_mul] at *
      nlinarith [sq_nonneg (x i j)]
    · rename_i h
      field_simp
  have hu₂ (i : Fin b) : ∑ j, (u i j)^2 = 1 := by
    unfold u
    by_cases h : r i = 0
    · simpa [h] using basisVec_unit hq
    · simp only [h, ite_false, div_pow, ← Finset.sum_div, ← hr₂]
      exact div_self (pow_ne_zero 2 h)
  let T := ∏ i, r i ^ 2
  let U := ∑ h, w h * ∏ i, (∑ j, (if z h i j then (-1:ℝ) else 1)*u i j)^2
  have ht : 0 ≤ T := Finset.prod_nonneg (fun i _ => sq_nonneg _)
  have hT : (∏ i, ∑ j, (x i j)^2) = T := by simp only [T, hr₂]
  have hrow (h : Fin t) (i : Fin b) :
      (∑ j, (if z h i j then (-1:ℝ) else 1)*x i j)^2 =
        r i ^ 2 * (∑ j, (if z h i j then (-1:ℝ) else 1)*u i j)^2 := by
    rw [← mul_pow, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [hscale i j]; ring)
  have hW : (∑ h, w h * ∏ i, (∑ j, (if z h i j then (-1:ℝ) else 1)*x i j)^2) = T*U := by
    simp only [hrow, Finset.prod_mul_distrib, T, U, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun h _ => by ring)
  have he : |U-1| ≤ 1/P := hunit u hu hu₂
  obtain ⟨hl, hh⟩ := abs_le.mp he
  have hl' : P-1 ≤ P*U := by
    have h := (le_div_iff₀ hP).1 (show (1-U) ≤ 1/P by linarith)
    linarith
  have hh' : P*U ≤ P+1 := by
    have h := (le_div_iff₀ hP).1 hh
    linarith
  dsimp only
  rw [hT, hW]
  constructor
  · simpa [mul_left_comm P T U, mul_comm T (P*U)] using mul_le_mul_of_nonneg_right hl' ht
  · simpa [mul_left_comm P T U, mul_comm T (P*U)] using mul_le_mul_of_nonneg_right hh' ht

end PEqualNP.Outside.L_lib_684_aux

open PEqualNP.Outside.L_lib_684_aux

theorem PEqualNP.Outside.L_lib_684 :
    ∀ (q b p : ℕ), 2 ≤ q → 2 ≤ p →
      let K := (q : ℝ)/2 + if q % 2 = 0 then 1/2 else (q : ℝ)/(q+1)
      ∃ (t : ℕ) (signs : Fin t → Fin b → Fin q → Bool) (w : Fin t → ℝ),
        (∀ h, 0 ≤ w h) ∧ (∑ h : Fin t, w h) = 1 ∧
        (t : ℝ) ≤ 1 + 192*(p : ℝ)^2*K^b * (2+(b : ℝ)*q*Real.log (2+72*((b : ℝ)+1)*q)) ∧
        ∀ x : Fin b → Fin q → ℝ, (∀ i j, 0 ≤ x i j) →
          let target := ∏ i : Fin b, ∑ j : Fin q, (x i j)^2
          let est := ∑ h : Fin t, w h * ∏ i : Fin b,
            (∑ j : Fin q, (if signs h i j then (-1 : ℝ) else 1) * x i j)^2
          ((p : ℝ)-1)*target ≤ (p : ℝ)*est ∧ (p : ℝ)*est ≤ ((p : ℝ)+1)*target := by
  classical
  intro q b p hq hp
  let L := (b : ℝ)*q*Real.log (2+72*((b : ℝ)+1)*q)
  let P := (p : ℝ)
  have hpR : 2 ≤ P := by
    change (2 : ℝ) ≤ (p : ℝ)
    exact_mod_cast hp
  have hp₀ : 0 < P := by linarith
  have hq₀ : 0 < q := by omega
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith [show 0 ≤ 72*((b : ℝ)+1)*q by positivity]))
  have hk : 1 ≤ kappa q ^ b := one_le_pow₀ (kappa_ge hq)
  obtain ⟨G, hGu, hGc, hGnet, hGb⟩ := grid q b hq
  let F (x : ↥G) (a : Fin b → Row q) := factor a * value a x.val
  have hf₀ (x : ↥G) (a : Fin b → Row q) : 0 ≤ F x a := test_nonneg hq a x.val
  have hfB (x : ↥G) (a : Fin b → Row q) : F x a ≤ kappa q ^ b :=
    test_le hq a x.val (hGu x.val x.property).1 (hGu x.val x.property).2
  have hf₁ (x : ↥G) : ∑ a : Fin b → Row q, law a * F x a = 1 :=
    test_mean hq x.val (hGu x.val x.property).2
  have hcard : (Fintype.card ↥G : ℝ) ≤ Real.exp L := by simpa [L] using hGc
  obtain ⟨t, ht, s, hbound, hs⟩ := sample law (law_nonneg hq) (law_total hq) F hf₀ hfB hf₁ hk hpR hL hcard
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  let z (h : Fin t) (i : Fin b) (j : Fin q) := negSigns (s h i) j
  let T := ∑ h : Fin t, factor (s h)
  let S := T/(t:ℝ)
  let v : Fin b → Fin q → ℝ := fun _ j => basisVec j
  have hv : v ∈ G := hGb
  have hvtest (a : Fin b → Row q) : value a v = 1 := by
    unfold value
    apply Finset.prod_eq_one
    intro i hi
    exact basisVec_sign_sq hq₀ (negSigns (a i))
  have hS : |S-1| ≤ 1/(8*P) := by
    simpa [F, hvtest, S, T] using hs ⟨v, hv⟩
  have hS₀ : 0 < S := (ratio_bound hpR hS hS).1
  have hT : 0 < T := (div_pos_iff_of_pos_right htR).1 hS₀
  let w (h : Fin t) := factor (s h)/T
  refine ⟨t, z, w, (fun h => div_nonneg (factor_nonneg hq _) hT.le), ?_, hbound, ?_⟩
  · simp only [w, ← Finset.sum_div]
    exact div_self hT.ne'
  intro x hx
  apply rescale hq₀ z w P hp₀ _ x hx
  intro u hu hu₁
  have hnet : ∀ u : Fin b → Fin q → ℝ, (∀ i j, 0 ≤ u i j) →
      (∀ i, ∑ j, (u i j)^2 = 1) → ∃ y ∈ (↑G : Set (Fin b → Fin q → ℝ)),
        (∀ i j, 0 ≤ y i j) ∧ (∀ i, ∑ j, (y i j)^2 = 1) ∧
        ∀ i, Real.sqrt (∑ j, (u i j-y i j)^2) ≤ 1/(36*((b : ℝ)+1)) := by
    intro u hu hu₁
    obtain ⟨y, hy, hyd⟩ := hGnet u hu hu₁
    exact ⟨y, hy, (hGu y hy).1, (hGu y hy).2,
      fun i => (root_sum_le_sum_abs fun j => u i j-y i j).trans (hyd i)⟩
  have hclose (y : Fin b → Fin q → ℝ) (hy : y ∈ (↑G : Set (Fin b → Fin q → ℝ))) :
      |(∑ h, w h * ∏ i, (∑ j, (if z h i j then (-1:ℝ) else 1)*y i j)^2) -
        (∏ i, ∑ j, (y i j)^2)| ≤ 1/(2*P) := by
    have hy₁ : (∏ i, ∑ j, (y i j)^2) = 1 := by simp [(hGu y hy).2]
    rw [hy₁]
    let A := (∑ h, F ⟨y,hy⟩ (s h))/(t:ℝ)
    have hA : |A-1| ≤ 1/(8*P) := hs ⟨y,hy⟩
    have he : (∑ h, w h * ∏ i, (∑ j, (if z h i j then (-1:ℝ) else 1)*y i j)^2) = A/S := by
      change (∑ h, (factor (s h)/T) * value (s h) y) = A/S
      calc
        _ = (∑ h, F ⟨y,hy⟩ (s h))/T := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun h _ => by simp only [F, ← mul_div_right_comm]
        _ = _ := by dsimp [A,S]; field_simp
    rw [he]
    exact (ratio_bound hpR hA hS).2
  have h := gridToUniformEstSubTarget z w (↑G) (1/(2*P)) hnet hclose u hu hu₁
  have huu : (∏ i, ∑ j, (u i j)^2) = 1 := by simp [hu₁]
  rw [huu] at h
  convert h using 1 <;> ring
