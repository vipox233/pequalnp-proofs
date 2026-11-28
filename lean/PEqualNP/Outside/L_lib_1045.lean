import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1045_aux

open scoped BigOperators

def wt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∏ j : Fin n, M (π j) j

def edgeMu {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  ∑ π : Equiv.Perm (Fin n), if π j = i then wt M π else 0

def sgnMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (s : (Fin n × Fin n) → Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if s (i, j) then -M i j else M i j

def chi (b : Bool) : ℝ :=
  if b then -1 else 1

lemma wt_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (π : Equiv.Perm (Fin n)) : 0 ≤ wt M π :=
  Finset.prod_nonneg (fun j _ => hM (π j) j)

lemma wt_pos_iff {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (π : Equiv.Perm (Fin n)) : 0 < wt M π ↔ ∀ j : Fin n, 0 < M (π j) j := by
  constructor
  · intro hpos j
    by_contra hle
    have h0 : M (π j) j = 0 := le_antisymm (not_lt.mp hle) (hM (π j) j)
    have hw0 : wt M π = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h0
    linarith
  · intro hpos
    exact Finset.prod_pos (fun j _ => hpos j)

lemma entry_pos_of_edgeMu_pos {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {i j : Fin n} (hpos : 0 < edgeMu M i j) : 0 < M i j := by
  by_contra hle
  have h0 : M i j = 0 := le_antisymm (not_lt.mp hle) (hM i j)
  have hmu0 : edgeMu M i j = 0 := by
    apply Finset.sum_eq_zero
    intro π _
    split_ifs with hπ
    · exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hπ, h0])
    · rfl
  linarith

lemma edgeMu_pos_of_wt_pos {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {π : Equiv.Perm (Fin n)} (hpos : 0 < wt M π) (j : Fin n) : 0 < edgeMu M (π j) j := by
  have hle : (if π j = π j then wt M π else 0) ≤ edgeMu M (π j) j := by
    apply Finset.single_le_sum (f := fun σ : Equiv.Perm (Fin n) => if σ j = π j then wt M σ else 0)
    · intro σ _
      split_ifs
      · exact wt_nonneg hM σ
      · exact le_rfl
    · exact Finset.mem_univ π
  simp only [↓reduceIte] at hle
  linarith

lemma wt_pos_iff_of_edgeMu_eq {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hmu : ∀ i j, edgeMu A i j = edgeMu B i j) (π : Equiv.Perm (Fin n)) :
    0 < wt A π ↔ 0 < wt B π := by
  constructor
  · intro hpos
    rw [wt_pos_iff hB]
    intro j
    have h1 : 0 < edgeMu A (π j) j := edgeMu_pos_of_wt_pos hA hpos j
    rw [hmu] at h1
    exact entry_pos_of_edgeMu_pos hB h1
  · intro hpos
    rw [wt_pos_iff hA]
    intro j
    have h1 : 0 < edgeMu B (π j) j := edgeMu_pos_of_wt_pos hB hpos j
    rw [← hmu] at h1
    exact entry_pos_of_edgeMu_pos hA h1

lemma nat_le_two_pow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    push_cast
    rw [pow_succ]
    linarith

lemma exists_zpow_two_le_lt {x : ℝ} (hx : 0 < x) :
    ∃ a : ℤ, (2 : ℝ) ^ a ≤ x ∧ x < (2 : ℝ) ^ (a + 1) := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have hup : x < (2 : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast]
    exact lt_of_lt_of_le hn (nat_le_two_pow n)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / x)
  have hlo : (2 : ℝ) ^ (-(m : ℤ)) ≤ x := by
    have hm2 : 1 / x < (2 : ℝ) ^ m := lt_of_lt_of_le hm (nat_le_two_pow m)
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    rw [zpow_neg, zpow_natCast]
    have hmul : 1 < (2 : ℝ) ^ m * x := by
      have := (div_lt_iff₀ hx).mp hm2
      linarith
    rw [inv_eq_one_div, div_le_iff₀ h2pos]
    linarith
  have hex : ∃ k : ℕ, x < (2 : ℝ) ^ (-(m : ℤ) + (k : ℤ)) := by
    refine ⟨m + n, ?_⟩
    have hEq : -(m : ℤ) + ((m + n : ℕ) : ℤ) = (n : ℤ) := by push_cast; ring
    rw [hEq]
    exact hup
  let k := Nat.find hex
  have hk : x < (2 : ℝ) ^ (-(m : ℤ) + (k : ℤ)) := Nat.find_spec hex
  have hk_ne : k ≠ 0 := by
    intro h0
    have hk0 : x < (2 : ℝ) ^ (-(m : ℤ)) := by simpa [k, h0] using hk
    linarith
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne
  have hprev : ¬ (x < (2 : ℝ) ^ (-(m : ℤ) + (k' : ℤ))) :=
    Nat.find_min hex (by omega)
  refine ⟨-(m : ℤ) + (k' : ℤ), le_of_not_gt hprev, ?_⟩
  have hEq : -(m : ℤ) + (k : ℤ) = -(m : ℤ) + (k' : ℤ) + 1 := by
    rw [hk']
    push_cast
    ring
  rwa [← hEq]

noncomputable def logSet (x : ℝ) : Set ℝ :=
  { q : ℝ | ∃ (a : ℤ) (b : ℕ), 0 < b ∧ q = (a : ℝ) / (b : ℝ) ∧ (2 : ℝ) ^ a ≤ x ^ b }

noncomputable def myLog (x : ℝ) : ℝ :=
  sSup (logSet x)

lemma logSet_nonempty {x : ℝ} (hx : 0 < x) : (logSet x).Nonempty := by
  obtain ⟨a, hlo, _⟩ := exists_zpow_two_le_lt hx
  refine ⟨(a : ℝ) / (1 : ℕ), a, 1, Nat.one_pos, rfl, ?_⟩
  simpa using hlo

lemma logSet_le_of_lt_zpow {x : ℝ} (hx : 0 < x) {A : ℤ} {b : ℕ} (hb : 0 < b)
    (hhi : x ^ b < (2 : ℝ) ^ A) : ∀ q ∈ logSet x, q ≤ (A : ℝ) / (b : ℝ) := by
  intro q hq
  rcases hq with ⟨c, d, hd, rfl, hcd⟩
  have hbpos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have h1 : (2 : ℝ) ^ (c * (b : ℤ)) ≤ (x ^ d) ^ b := by
    rw [zpow_mul, zpow_natCast]
    exact pow_le_pow_left₀ (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) c) hcd b
  have h2 : (x ^ d) ^ b < (2 : ℝ) ^ (A * (d : ℤ)) := by
    rw [← pow_mul, mul_comm d b, pow_mul, zpow_mul, zpow_natCast]
    exact pow_lt_pow_left₀ hhi (by positivity) (Nat.pos_iff_ne_zero.mp hd)
  have h3 : (2 : ℝ) ^ (c * (b : ℤ)) < (2 : ℝ) ^ (A * (d : ℤ)) := lt_of_le_of_lt h1 h2
  have h4 : c * (b : ℤ) < A * (d : ℤ) :=
    (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h3
  have h5 : (c : ℝ) * (b : ℝ) ≤ (A : ℝ) * (d : ℝ) := by
    exact_mod_cast le_of_lt h4
  exact (div_le_div_iff₀ hdpos hbpos).mpr h5

lemma logSet_bddAbove {x : ℝ} (hx : 0 < x) : BddAbove (logSet x) := by
  obtain ⟨a, _, hhi⟩ := exists_zpow_two_le_lt hx
  refine ⟨((a + 1 : ℤ) : ℝ) / (1 : ℕ), ?_⟩
  intro q hq
  exact logSet_le_of_lt_zpow hx Nat.one_pos (by simpa using hhi) q hq

lemma myLog_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    myLog (x * y) = myLog x + myLog y := by
  by_contra hne
  have hpos : 0 < |myLog (x * y) - (myLog x + myLog y)| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨b, hb⟩ := exists_nat_gt (2 / |myLog (x * y) - (myLog x + myLog y)|)
  have hb_pos : 0 < b := by
    by_contra h0
    have hb0 : b = 0 := Nat.eq_zero_of_not_pos h0
    have hdiv : 0 < 2 / |myLog (x * y) - (myLog x + myLog y)| := by positivity
    rw [hb0, Nat.cast_zero] at hb
    linarith
  have hbr : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb_pos
  obtain ⟨ax, hax_lo, hax_hi⟩ := exists_zpow_two_le_lt (pow_pos hx b)
  obtain ⟨ay, hay_lo, hay_hi⟩ := exists_zpow_two_le_lt (pow_pos hy b)
  have hx_lo : (ax : ℝ) / (b : ℝ) ≤ myLog x :=
    le_csSup (logSet_bddAbove hx) ⟨ax, b, hb_pos, rfl, hax_lo⟩
  have hx_hi : myLog x ≤ ((ax + 1 : ℤ) : ℝ) / (b : ℝ) :=
    csSup_le (logSet_nonempty hx) (logSet_le_of_lt_zpow hx hb_pos hax_hi)
  have hy_lo : (ay : ℝ) / (b : ℝ) ≤ myLog y :=
    le_csSup (logSet_bddAbove hy) ⟨ay, b, hb_pos, rfl, hay_lo⟩
  have hy_hi : myLog y ≤ ((ay + 1 : ℤ) : ℝ) / (b : ℝ) :=
    csSup_le (logSet_nonempty hy) (logSet_le_of_lt_zpow hy hb_pos hay_hi)
  have hxy_lo_pow : (2 : ℝ) ^ (ax + ay) ≤ (x * y) ^ b := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_pow]
    exact mul_le_mul hax_lo hay_lo (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ay) (pow_nonneg hx.le b)
  have hxy_hi_pow : (x * y) ^ b < (2 : ℝ) ^ (ax + ay + 2) := by
    have hEq : ax + ay + 2 = (ax + 1) + (ay + 1) := by ring
    rw [hEq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_pow]
    exact mul_lt_mul hax_hi (le_of_lt hay_hi) (pow_pos hy b) (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (ax + 1))
  have hxy_lo : ((ax + ay : ℤ) : ℝ) / (b : ℝ) ≤ myLog (x * y) :=
    le_csSup (logSet_bddAbove (mul_pos hx hy)) ⟨ax + ay, b, hb_pos, rfl, hxy_lo_pow⟩
  have hxy_hi : myLog (x * y) ≤ ((ax + ay + 2 : ℤ) : ℝ) / (b : ℝ) :=
    csSup_le (logSet_nonempty (mul_pos hx hy))
      (logSet_le_of_lt_zpow (mul_pos hx hy) hb_pos hxy_hi_pow)
  have habs : |myLog (x * y) - (myLog x + myLog y)| ≤ 2 / (b : ℝ) := by
    rw [abs_le]
    push_cast at hx_hi hy_hi hxy_lo hxy_hi
    constructor
    · have : (ax : ℝ) / (b : ℝ) + (ay : ℝ) / (b : ℝ) = ((ax : ℝ) + (ay : ℝ)) / (b : ℝ) := by ring
      have : ((ax : ℝ) + 1) / (b : ℝ) + ((ay : ℝ) + 1) / (b : ℝ) =
          ((ax : ℝ) + (ay : ℝ)) / (b : ℝ) + 2 / (b : ℝ) := by ring
      linarith
    · have : ((ax : ℝ) + (ay : ℝ) + 2) / (b : ℝ) =
          (ax : ℝ) / (b : ℝ) + (ay : ℝ) / (b : ℝ) + 2 / (b : ℝ) := by ring
      linarith
  have hlt : 2 / (b : ℝ) < |myLog (x * y) - (myLog x + myLog y)| := by
    rw [div_lt_iff₀ hbr]
    have := (div_lt_iff₀ hpos).mp hb
    linarith
  linarith

lemma myLog_one : myLog 1 = 0 := by
  have h := myLog_mul (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  rw [mul_one] at h
  linarith

lemma myLog_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    myLog (x / y) = myLog x - myLog y := by
  have h := myLog_mul (div_pos hx hy) hy
  rw [div_mul_cancel₀ x hy.ne'] at h
  linarith

lemma myLog_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    myLog (∏ i ∈ s, f i) = ∑ i ∈ s, myLog (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [myLog_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have ha_pos : 0 < f a := hf a (Finset.mem_insert_self a s)
    have hs_pos : 0 < ∏ i ∈ s, f i :=
      Finset.prod_pos (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [myLog_mul ha_pos hs_pos, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma bernoulli_ineq (δ : ℝ) (hδ : 0 ≤ δ) (b : ℕ) :
    1 + (b : ℝ) * δ ≤ (1 + δ) ^ b := by
  induction b with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [pow_succ]
    have h1 : (1 + (k : ℝ) * δ) * (1 + δ) ≤ (1 + δ) ^ k * (1 + δ) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : 0 ≤ (k : ℝ) * δ * δ := by positivity
    linarith

lemma myLog_pos_of_one_lt {r : ℝ} (hr : 1 < r) : 0 < myLog r := by
  have hδ : 0 < r - 1 := sub_pos.mpr hr
  obtain ⟨b, hb⟩ := exists_nat_gt (1 / (r - 1))
  have hb_pos : 0 < b := by
    by_contra h0
    have hb0 : b = 0 := Nat.eq_zero_of_not_pos h0
    have hdiv : 0 < 1 / (r - 1) := by positivity
    rw [hb0, Nat.cast_zero] at hb
    linarith
  have hmul : 1 < (b : ℝ) * (r - 1) := by
    have := (div_lt_iff₀ hδ).mp hb
    linarith
  have hpow : (2 : ℝ) ^ (1 : ℤ) ≤ r ^ b := by
    have hbern := bernoulli_ineq (r - 1) hδ.le b
    have hr' : 1 + (r - 1) = r := by ring
    rw [hr'] at hbern
    rw [zpow_one]
    linarith
  have hmem : ((1 : ℤ) : ℝ) / (b : ℝ) ∈ logSet r := ⟨1, b, hb_pos, rfl, hpow⟩
  have hle : ((1 : ℤ) : ℝ) / (b : ℝ) ≤ myLog r :=
    le_csSup (logSet_bddAbove (by linarith)) hmem
  have hpos : (0 : ℝ) < ((1 : ℤ) : ℝ) / (b : ℝ) := by
    have : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb_pos
    positivity
  linarith

lemma sub_mul_myLog_div_nonneg {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 ≤ (u - v) * myLog (u / v) := by
  rcases lt_trichotomy u v with hlt | heq | hgt
  · have h1 : 1 < v / u := (one_lt_div hu).mpr hlt
    have hpos : 0 < myLog (v / u) := myLog_pos_of_one_lt h1
    have hneg : myLog (u / v) < 0 := by
      rw [myLog_div hu hv]
      rw [myLog_div hv hu] at hpos
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hneg.le
  · subst heq
    simp
  · have h1 : 1 < u / v := (one_lt_div hv).mpr hgt
    have hpos : 0 < myLog (u / v) := myLog_pos_of_one_lt h1
    exact mul_nonneg (by linarith) hpos.le

lemma eq_of_sub_mul_myLog_div_eq_zero {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : (u - v) * myLog (u / v) = 0) : u = v := by
  rcases mul_eq_zero.mp h with hsub | hlog
  · linarith
  · rcases lt_trichotomy u v with hlt | heq | hgt
    · have hpos : 0 < myLog (v / u) := myLog_pos_of_one_lt ((one_lt_div hu).mpr hlt)
      rw [myLog_div hu hv] at hlog
      rw [myLog_div hv hu] at hpos
      linarith
    · exact heq
    · have hpos : 0 < myLog (u / v) := myLog_pos_of_one_lt ((one_lt_div hv).mpr hgt)
      linarith

lemma myLog_wt_div {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    {π : Equiv.Perm (Fin n)} (hpA : 0 < wt A π) (hpB : 0 < wt B π) :
    myLog (wt A π / wt B π) = ∑ j : Fin n, myLog (A (π j) j / B (π j) j) := by
  have hA' := (wt_pos_iff hA π).mp hpA
  have hB' := (wt_pos_iff hB π).mp hpB
  have hdiv : wt A π / wt B π = ∏ j : Fin n, (A (π j) j / B (π j) j) := by
    simp only [wt, Finset.prod_div_distrib]
  rw [hdiv]
  exact myLog_prod Finset.univ (fun j => A (π j) j / B (π j) j)
    (fun j _ => div_pos (hA' j) (hB' j))

lemma wt_eq_of_edgeMu_eq {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hmu : ∀ i j, edgeMu A i j = edgeMu B i j) :
    ∀ π : Equiv.Perm (Fin n), wt A π = wt B π := by
  classical
  let S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter (fun π => 0 < wt A π)
  have hzero_out : ∀ π : Equiv.Perm (Fin n), π ∉ S → wt A π = 0 ∧ wt B π = 0 := by
    intro π hπ
    have hnotA : ¬ (0 < wt A π) := by
      simpa [S] using hπ
    have hnotB : ¬ (0 < wt B π) := by
      rwa [← wt_pos_iff_of_edgeMu_eq hA hB hmu π]
    exact ⟨le_antisymm (not_lt.mp hnotA) (wt_nonneg hA π),
      le_antisymm (not_lt.mp hnotB) (wt_nonneg hB π)⟩
  have hsum0 : ∑ π ∈ S, (wt A π - wt B π) * myLog (wt A π / wt B π) = 0 := by
    have h1 : ∑ π ∈ S, (wt A π - wt B π) * myLog (wt A π / wt B π) =
        ∑ π ∈ S, ∑ j : Fin n, (wt A π - wt B π) * myLog (A (π j) j / B (π j) j) := by
      apply Finset.sum_congr rfl
      intro π hπ
      have hpA : 0 < wt A π := (Finset.mem_filter.mp hπ).2
      have hpB : 0 < wt B π := (wt_pos_iff_of_edgeMu_eq hA hB hmu π).mp hpA
      rw [myLog_wt_div hA hB hpA hpB, Finset.mul_sum]
    rw [h1, Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    have h2 : ∑ π ∈ S, (wt A π - wt B π) * myLog (A (π j) j / B (π j) j) =
        ∑ π : Equiv.Perm (Fin n), (wt A π - wt B π) * myLog (A (π j) j / B (π j) j) := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro π _ hπ
      rcases hzero_out π hπ with ⟨h0A, h0B⟩
      simp [h0A, h0B]
    rw [h2]
    have h3 : ∑ π : Equiv.Perm (Fin n), (wt A π - wt B π) * myLog (A (π j) j / B (π j) j) =
        ∑ π : Equiv.Perm (Fin n), ∑ i : Fin n,
          if π j = i then (wt A π - wt B π) * myLog (A i j / B i j) else 0 := by
      apply Finset.sum_congr rfl
      intro π _
      simp
    rw [h3, Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    have h4 : (∑ π : Equiv.Perm (Fin n),
        if π j = i then (wt A π - wt B π) * myLog (A i j / B i j) else 0) =
        (edgeMu A i j - edgeMu B i j) * myLog (A i j / B i j) := by
      have hsub : edgeMu A i j - edgeMu B i j =
          ∑ π : Equiv.Perm (Fin n), if π j = i then (wt A π - wt B π) else 0 := by
        simp only [edgeMu, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro π _
        split_ifs <;> ring
      rw [hsub, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro π _
      split_ifs <;> ring
    rw [h4, hmu i j, sub_self, zero_mul]
  have hnonneg : ∀ π ∈ S, 0 ≤ (wt A π - wt B π) * myLog (wt A π / wt B π) := by
    intro π hπ
    have hpA : 0 < wt A π := (Finset.mem_filter.mp hπ).2
    have hpB : 0 < wt B π := (wt_pos_iff_of_edgeMu_eq hA hB hmu π).mp hpA
    exact sub_mul_myLog_div_nonneg hpA hpB
  have heach := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0
  intro π
  by_cases hπ : π ∈ S
  · have hpA : 0 < wt A π := (Finset.mem_filter.mp hπ).2
    have hpB : 0 < wt B π := (wt_pos_iff_of_edgeMu_eq hA hB hmu π).mp hpA
    exact eq_of_sub_mul_myLog_div_eq_zero hpA hpB (heach π hπ)
  · rcases hzero_out π hπ with ⟨h0A, h0B⟩
    rw [h0A, h0B]

lemma chi_mul_self (b : Bool) : chi b * chi b = 1 := by
  cases b <;> simp [chi]

lemma chi_not (b : Bool) : chi (!b) = -chi b := by
  cases b <;> simp [chi]

lemma det_sgnMat_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (s : (Fin n × Fin n) → Bool) :
    Matrix.det (sgnMat M s) =
      ∑ π : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℝ) * wt M π * (∏ j : Fin n, chi (s (π j, j))) := by
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro π _
  have hprod : (∏ j : Fin n, sgnMat M s (π j) j) =
      wt M π * (∏ j : Fin n, chi (s (π j, j))) := by
    rw [wt, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    simp only [sgnMat, chi]
    cases s (π j, j) <;> simp
  rw [hprod]
  ring

def flipEquiv {n : ℕ} (e₀ : Fin n × Fin n) :
    ((Fin n × Fin n) → Bool) ≃ ((Fin n × Fin n) → Bool) where
  toFun s := Function.update s e₀ (!s e₀)
  invFun s := Function.update s e₀ (!s e₀)
  left_inv s := by
    funext e
    by_cases h : e = e₀
    · subst h
      simp [Function.update]
    · simp [Function.update, h]
  right_inv s := by
    funext e
    by_cases h : e = e₀
    · subst h
      simp [Function.update]
    · simp [Function.update, h]

lemma sum_chi_prod_ne {n : ℕ} {π σ : Equiv.Perm (Fin n)} (hne : π ≠ σ) :
    ∑ s : (Fin n × Fin n) → Bool,
      (∏ j : Fin n, chi (s (π j, j))) * (∏ j : Fin n, chi (s (σ j, j))) = 0 := by
  have hex : ∃ j₀ : Fin n, π j₀ ≠ σ j₀ := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  rcases hex with ⟨j₀, hj₀⟩
  let e₀ : Fin n × Fin n := (π j₀, j₀)
  let g : ((Fin n × Fin n) → Bool) → ℝ :=
    fun s => (∏ j : Fin n, chi (s (π j, j))) * (∏ j : Fin n, chi (s (σ j, j)))
  have hneg : ∀ s, g (flipEquiv e₀ s) = -g s := by
    intro s
    have h1 : (∏ j : Fin n, chi (flipEquiv e₀ s (π j, j))) =
        -(∏ j : Fin n, chi (s (π j, j))) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀),
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
      have hat : chi (flipEquiv e₀ s (π j₀, j₀)) = -chi (s (π j₀, j₀)) := by
        simp [flipEquiv, e₀, chi_not]
      have hrest : (∏ j ∈ Finset.univ.erase j₀, chi (flipEquiv e₀ s (π j, j))) =
          ∏ j ∈ Finset.univ.erase j₀, chi (s (π j, j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hne_j : j ≠ j₀ := (Finset.mem_erase.mp hj).1
        have hne_e : (π j, j) ≠ e₀ := by
          intro heq
          exact hne_j (congrArg Prod.snd heq)
        simp [flipEquiv, Function.update, hne_e]
      rw [hat, hrest]
      ring
    have h2 : (∏ j : Fin n, chi (flipEquiv e₀ s (σ j, j))) =
        ∏ j : Fin n, chi (s (σ j, j)) := by
      apply Finset.prod_congr rfl
      intro j _
      have hne_e : (σ j, j) ≠ e₀ := by
        intro heq
        have hj : j = j₀ := congrArg Prod.snd heq
        have h1' : σ j = π j₀ := congrArg Prod.fst heq
        rw [hj] at h1'
        exact hj₀ h1'.symm
      simp [flipEquiv, Function.update, hne_e]
    dsimp only [g]
    rw [h1, h2]
    ring
  have hcomp : ∑ s : (Fin n × Fin n) → Bool, g (flipEquiv e₀ s) =
      ∑ s : (Fin n × Fin n) → Bool, g s :=
    Equiv.sum_comp (flipEquiv e₀) g
  have hsum_neg : ∑ s : (Fin n × Fin n) → Bool, g (flipEquiv e₀ s) =
      -(∑ s : (Fin n × Fin n) → Bool, g s) := by
    simp only [hneg, Finset.sum_neg_distrib]
  linarith

lemma sum_chi_prod_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∑ s : (Fin n × Fin n) → Bool,
      (∏ j : Fin n, chi (s (σ j, j))) * (∏ j : Fin n, chi (s (σ j, j))) =
      (Fintype.card ((Fin n × Fin n) → Bool) : ℝ) := by
  have h1 : ∀ s : (Fin n × Fin n) → Bool,
      (∏ j : Fin n, chi (s (σ j, j))) * (∏ j : Fin n, chi (s (σ j, j))) = 1 := by
    intro s
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j _
    exact chi_mul_self (s (σ j, j))
  simp [h1]

lemma wt_eq_of_det_eq {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hdet : ∀ s : (Fin n × Fin n) → Bool, Matrix.det (sgnMat A s) = Matrix.det (sgnMat B s)) :
    ∀ σ : Equiv.Perm (Fin n), wt A σ = wt B σ := by
  intro σ
  let c : Equiv.Perm (Fin n) → ℝ :=
    fun π => ((Equiv.Perm.sign π : ℤ) : ℝ) * (wt A π - wt B π)
  have hdiff : ∀ s : (Fin n × Fin n) → Bool,
      Matrix.det (sgnMat A s) - Matrix.det (sgnMat B s) =
        ∑ π : Equiv.Perm (Fin n), c π * (∏ j : Fin n, chi (s (π j, j))) := by
    intro s
    rw [det_sgnMat_eq A s, det_sgnMat_eq B s, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro π _
    dsimp only [c]
    ring
  have h0 : ∑ s : (Fin n × Fin n) → Bool,
      (Matrix.det (sgnMat A s) - Matrix.det (sgnMat B s)) *
        (∏ j : Fin n, chi (s (σ j, j))) = 0 := by
    simp [hdet]
  have h1 : ∑ s : (Fin n × Fin n) → Bool,
      (Matrix.det (sgnMat A s) - Matrix.det (sgnMat B s)) *
        (∏ j : Fin n, chi (s (σ j, j))) =
      c σ * (Fintype.card ((Fin n × Fin n) → Bool) : ℝ) := by
    calc
      ∑ s : (Fin n × Fin n) → Bool,
          (Matrix.det (sgnMat A s) - Matrix.det (sgnMat B s)) *
            (∏ j : Fin n, chi (s (σ j, j)))
        = ∑ s : (Fin n × Fin n) → Bool,
            ∑ π : Equiv.Perm (Fin n),
              c π * ((∏ j : Fin n, chi (s (π j, j))) * (∏ j : Fin n, chi (s (σ j, j)))) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [hdiff s, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro π _
          ring
      _ = ∑ π : Equiv.Perm (Fin n),
            c π * ∑ s : (Fin n × Fin n) → Bool,
              (∏ j : Fin n, chi (s (π j, j))) * (∏ j : Fin n, chi (s (σ j, j))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro π _
          rw [Finset.mul_sum]
      _ = c σ * (Fintype.card ((Fin n × Fin n) → Bool) : ℝ) := by
          rw [Finset.sum_eq_single σ]
          · rw [sum_chi_prod_eq σ]
          · intro π _ hne
            rw [sum_chi_prod_ne hne, mul_zero]
          · intro hmem
            exact absurd (Finset.mem_univ σ) hmem
  have hc0 : c σ * (Fintype.card ((Fin n × Fin n) → Bool) : ℝ) = 0 := by
    linarith
  have hcard_pos : (0 : ℝ) < (Fintype.card ((Fin n × Fin n) → Bool) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ((Fin n × Fin n) → Bool))
  have hc : c σ = 0 := (mul_eq_zero.mp hc0).resolve_right hcard_pos.ne'
  have hsgn : ((Equiv.Perm.sign σ : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hsub : wt A σ - wt B σ = 0 := (mul_eq_zero.mp hc).resolve_left hsgn
  linarith

end PEqualNP.Outside.L_lib_1045_aux

theorem PEqualNP.Outside.L_lib_1045 :
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
  (∀ i j, 0 ≤ A i j) → (∀ i j, 0 ≤ B i j) →
  let I := Fin n
  let w := fun (M : Matrix I I ℝ) (π : Equiv.Perm I) => ∏ j : I, M (π j) j
  let mu := fun (M : Matrix I I ℝ) (i j : I) =>
    ∑ π : Equiv.Perm I, if π j = i then w M π else 0
  let det := fun (M : Matrix I I ℝ) (s : I × I → Bool) =>
    Matrix.det (fun i j => if s (i,j) then -M i j else M i j : Matrix I I ℝ)
  ((∀ i j : I, mu A i j = mu B i j) ↔ (∀ π : Equiv.Perm I, w A π = w B π)) ∧
  ((∀ s : I × I → Bool, det A s = det B s) ↔ (∀ π : Equiv.Perm I, w A π = w B π)) := by
  intro n A B hA hB
  dsimp only
  constructor
  · constructor
    · intro hmu
      exact PEqualNP.Outside.L_lib_1045_aux.wt_eq_of_edgeMu_eq hA hB hmu
    · intro hw i j
      simp only [hw]
  · constructor
    · intro hdet
      exact PEqualNP.Outside.L_lib_1045_aux.wt_eq_of_det_eq hdet
    · intro hw s
      change Matrix.det (PEqualNP.Outside.L_lib_1045_aux.sgnMat A s) =
        Matrix.det (PEqualNP.Outside.L_lib_1045_aux.sgnMat B s)
      rw [PEqualNP.Outside.L_lib_1045_aux.det_sgnMat_eq A s,
          PEqualNP.Outside.L_lib_1045_aux.det_sgnMat_eq B s]
      apply Finset.sum_congr rfl
      intro π _
      change ((Equiv.Perm.sign π : ℤ) : ℝ) * (∏ j : Fin n, A (π j) j) *
          (∏ j : Fin n, PEqualNP.Outside.L_lib_1045_aux.chi (s (π j, j))) =
        ((Equiv.Perm.sign π : ℤ) : ℝ) * (∏ j : Fin n, B (π j) j) *
          (∏ j : Fin n, PEqualNP.Outside.L_lib_1045_aux.chi (s (π j, j)))
      rw [hw π]
