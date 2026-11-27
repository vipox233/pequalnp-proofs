import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_847_aux

private lemma extract_prime_pow {p : ℕ} (hp : Nat.Prime p) :
    ∀ j : ℕ, 0 < j → ∃ m r : ℕ, 0 < r ∧ ¬ p ∣ r ∧ j = p ^ m * r := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hd : p ∣ j
    · rcases hd with ⟨j', rfl⟩
      have hj'pos : 0 < j' := by
        rcases Nat.eq_zero_or_pos j' with rfl | hpos
        · simp at hj
        · exact hpos
      have hlt : j' < p * j' := by
        have hp2 := hp.two_le
        nlinarith
      obtain ⟨m, r, hrpos, hrnd, heq⟩ := ih j' hlt hj'pos
      refine ⟨m + 1, r, hrpos, hrnd, ?_⟩
      rw [heq, pow_succ']
      ring
    · exact ⟨0, j, hj, hd, by simp⟩

private lemma prime_pow_dvd_choose_prime_pow {p : ℕ} (hp : Nat.Prime p)
    (k b j : ℕ) (hj0 : 0 < j) (hkb : k ≤ b) (hjlt : j < p ^ (b - k + 1)) :
    p ^ k ∣ Nat.choose (p ^ b) j := by
  obtain ⟨m, r, hrpos, hrnd, hj_eq⟩ := extract_prime_pow hp j hj0
  have hm_lt : m < b - k + 1 := by
    by_contra hge
    push Not at hge
    have h1 : p ^ (b - k + 1) ≤ p ^ m := Nat.pow_le_pow_right hp.pos hge
    have h2 : p ^ m ≤ p ^ m * r := Nat.le_mul_of_pos_right _ hrpos
    omega
  have hmk : m + k ≤ b := by omega
  have hqpos : 0 < p ^ b := pow_pos hp.pos b
  have hmul : j * Nat.choose (p ^ b) j = p ^ b * Nat.choose (p ^ b - 1) (j - 1) := by
    have h := Nat.add_one_mul_choose_eq (p ^ b - 1) (j - 1)
    have h1 : p ^ b - 1 + 1 = p ^ b := by omega
    have h2 : j - 1 + 1 = j := by omega
    rw [h1, h2] at h
    linarith
  have hsplit : p ^ b = p ^ m * p ^ (b - m) := by
    rw [← pow_add, show m + (b - m) = b by omega]
  have hmul' : p ^ m * (r * Nat.choose (p ^ b) j) =
      p ^ m * (p ^ (b - m) * Nat.choose (p ^ b - 1) (j - 1)) := by
    calc p ^ m * (r * Nat.choose (p ^ b) j) = (p ^ m * r) * Nat.choose (p ^ b) j := by ring
      _ = j * Nat.choose (p ^ b) j := by rw [← hj_eq]
      _ = p ^ b * Nat.choose (p ^ b - 1) (j - 1) := hmul
      _ = (p ^ m * p ^ (b - m)) * Nat.choose (p ^ b - 1) (j - 1) := by rw [hsplit]
      _ = p ^ m * (p ^ (b - m) * Nat.choose (p ^ b - 1) (j - 1)) := by ring
  have hpm_pos : 0 < p ^ m := pow_pos hp.pos m
  have hcancel : r * Nat.choose (p ^ b) j = p ^ (b - m) * Nat.choose (p ^ b - 1) (j - 1) :=
    Nat.eq_of_mul_eq_mul_left hpm_pos hmul'
  have hpk_dvd_bm : p ^ k ∣ p ^ (b - m) := Nat.pow_dvd_pow p (by omega)
  have hpk_dvd_prod : p ^ k ∣ r * Nat.choose (p ^ b) j := by
    rw [hcancel]
    exact dvd_mul_of_dvd_left hpk_dvd_bm _
  have hcop : Nat.Coprime (p ^ k) r := (hp.coprime_iff_not_dvd.mpr hrnd).pow_left k
  exact hcop.dvd_of_dvd_mul_left hpk_dvd_prod

private lemma choose_pred_mod_prime {p b : ℕ} (hp : Nat.Prime p) (hb : 0 < b) :
    ∀ r < p ^ b, ((Nat.choose (p ^ b - 1) r : ℤ) - (-1 : ℤ) ^ r) % (p : ℤ) = 0 := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro hr
    have hr0 : r < p ^ b := by omega
    have hih := ih hr0
    have hpas : Nat.choose (p ^ b - 1) r + Nat.choose (p ^ b - 1) (r + 1) = Nat.choose (p ^ b) (r + 1) := by
      have h1 : p ^ b = (p ^ b - 1) + 1 := by
        have : 0 < p ^ b := pow_pos hp.pos b
        omega
      conv_rhs => rw [h1]
      exact (Nat.choose_succ_succ (p ^ b - 1) r).symm
    have hdvd : p ∣ Nat.choose (p ^ b) (r + 1) := by
      have h := prime_pow_dvd_choose_prime_pow hp 1 b (r + 1) (Nat.succ_pos r) hb
        (by simpa [show b - 1 + 1 = b by omega] using hr)
      simpa using h
    rcases hdvd with ⟨t, ht⟩
    have hdvd_ih : (p : ℤ) ∣ ((Nat.choose (p ^ b - 1) r : ℤ) - (-1 : ℤ) ^ r) :=
      Int.dvd_of_emod_eq_zero hih
    rcases hdvd_ih with ⟨c, hc⟩
    have hpasZ : (Nat.choose (p ^ b - 1) r : ℤ) + (Nat.choose (p ^ b - 1) (r + 1) : ℤ) = (p : ℤ) * (t : ℤ) := by
      exact_mod_cast (hpas.trans ht)
    have hdiff : (Nat.choose (p ^ b - 1) (r + 1) : ℤ) - (-1 : ℤ) ^ (r + 1) = (p : ℤ) * ((t : ℤ) - c) := by
      rw [pow_succ]
      linarith
    rw [hdiff, Int.mul_emod_right]

private lemma neg_one_pow_prime_pow_pred_mod {p b : ℕ} (hp : Nat.Prime p) (_hb : 0 < b) :
    (((-1 : ℤ) ^ (p ^ b - 1) - 1) % (p : ℤ)) = 0 := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · have h : ((-1 : ℤ) ^ (2 ^ b - 1) - 1) = if Even (2 ^ b - 1) then 0 else -2 := by
      rcases Nat.even_or_odd (2 ^ b - 1) with hev | hod
      · simp [hev, Even.neg_one_pow hev]
      · simp [Nat.not_even_iff_odd.mpr hod, Odd.neg_one_pow hod]
    rw [h]
    split_ifs <;> norm_num
  · have hqodd : Odd (p ^ b) := Odd.pow (Nat.odd_iff.mpr hodd)
    have hev : Even (p ^ b - 1) := by
      rcases hqodd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    rw [Even.neg_one_pow hev]
    simp

private lemma choose_q_qprime_cong {p b : ℕ} (hp : Nat.Prime p) (hb : 0 < b) :
    let q := p ^ b
    let q' := q / p
    ((p : ℤ) ^ 2) ∣ ((Nat.choose q q' : ℤ) - (p : ℤ)) := by
  dsimp only
  let q := p ^ b
  let q' := q / p
  have hq'_eq : q' = p ^ (b - 1) := by
    dsimp only [q', q]
    have hsplit : p ^ b = p ^ (b - 1) * p := by
      rw [← pow_succ, show b - 1 + 1 = b by omega]
    rw [hsplit, Nat.mul_div_cancel _ hp.pos]
  have hq'_pos : 0 < q' := by rw [hq'_eq]; exact pow_pos hp.pos (b - 1)
  have hq_eq : q = p * q' := by
    rw [hq'_eq]
    dsimp only [q]
    rw [← pow_succ', show b - 1 + 1 = b by omega]
  have hmul : q' * Nat.choose q q' = q * Nat.choose (q - 1) (q' - 1) := by
    have h := Nat.add_one_mul_choose_eq (q - 1) (q' - 1)
    have h1 : q - 1 + 1 = q := by have := pow_pos hp.pos b; omega
    have h2 : q' - 1 + 1 = q' := by omega
    rw [h1, h2] at h
    linarith
  have hch_eq : Nat.choose q q' = p * Nat.choose (q - 1) (q' - 1) := by
    have hmul' : q' * Nat.choose q q' = q' * (p * Nat.choose (q - 1) (q' - 1)) := by
      calc q' * Nat.choose q q' = q * Nat.choose (q - 1) (q' - 1) := hmul
        _ = (p * q') * Nat.choose (q - 1) (q' - 1) := by rw [hq_eq]
        _ = q' * (p * Nat.choose (q - 1) (q' - 1)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hq'_pos hmul'
  have hq'_lt : q' - 1 < p ^ b := by
    have h1 : q' ≤ q := by rw [hq_eq]; exact Nat.le_mul_of_pos_left _ hp.pos
    change q' - 1 < q
    omega
  have hmod1 := choose_pred_mod_prime hp hb (q' - 1) hq'_lt
  have hmod2 : (((-1 : ℤ) ^ (q' - 1) - 1) % (p : ℤ)) = 0 := by
    rw [hq'_eq]
    rcases Nat.eq_zero_or_pos (b - 1) with hb0 | hbpos
    · rw [hb0]; simp
    · exact neg_one_pow_prime_pow_pred_mod hp hbpos
  have hdvd1 : (p : ℤ) ∣ ((Nat.choose (q - 1) (q' - 1) : ℤ) - (-1 : ℤ) ^ (q' - 1)) :=
    Int.dvd_of_emod_eq_zero hmod1
  have hdvd2 : (p : ℤ) ∣ ((-1 : ℤ) ^ (q' - 1) - 1) :=
    Int.dvd_of_emod_eq_zero hmod2
  have hdvd : (p : ℤ) ∣ ((Nat.choose (q - 1) (q' - 1) : ℤ) - 1) := by
    have hadd := dvd_add hdvd1 hdvd2
    have hrew : ((Nat.choose (q - 1) (q' - 1) : ℤ) - (-1 : ℤ) ^ (q' - 1)) + ((-1 : ℤ) ^ (q' - 1) - 1) =
        (Nat.choose (q - 1) (q' - 1) : ℤ) - 1 := by ring
    rwa [hrew] at hadd
  rcases hdvd with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hchZ : (Nat.choose q q' : ℤ) = (p : ℤ) * (Nat.choose (q - 1) (q' - 1) : ℤ) := by
    exact_mod_cast hch_eq
  calc (Nat.choose q q' : ℤ) - (p : ℤ)
      = (p : ℤ) * ((Nat.choose (q - 1) (q' - 1) : ℤ) - 1) := by rw [hchZ]; ring
    _ = (p : ℤ) * ((p : ℤ) * t) := by rw [ht]
    _ = (p : ℤ) ^ 2 * t := by ring

private def KZ (q n u : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1),
    if j % q = u then (-1 : ℤ) ^ (n - j) * (Nat.choose n j : ℤ) else 0

private lemma mod_add_one_iff {q : ℕ} (hq : 0 < q) (j u : ℕ) (hu : u < q) :
    (j + 1) % q = u ↔ j % q = (u + q - 1) % q := by
  constructor
  · intro h
    have h1 : (j + 1 + (q - 1)) % q = (u + (q - 1)) % q := by
      rw [Nat.add_mod, h, Nat.mod_eq_of_lt (by omega : q - 1 < q)]
    have h2 : j + 1 + (q - 1) = j + q := by omega
    have h3 : u + (q - 1) = u + q - 1 := by omega
    rw [h2, Nat.add_mod_right, h3] at h1
    exact h1
  · intro h
    have h1 : (j + 1) % q = (u + q - 1 + 1) % q := by
      rw [Nat.add_mod, h, ← Nat.add_mod]
    have h2 : u + q - 1 + 1 = u + q := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hu] at h1
    exact h1

private lemma KZ_succ {q : ℕ} (hq : 0 < q) (n u : ℕ) (hu : u < q) :
    KZ q (n + 1) u = KZ q n ((u + q - 1) % q) - KZ q n u := by
  dsimp only [KZ]
  let prev := (u + q - 1) % q
  have hprev_iff : ∀ j : ℕ, (j + 1) % q = u ↔ j % q = prev :=
    fun j => mod_add_one_iff hq j u hu
  rw [Finset.sum_range_succ']
  have hsum_split : ∑ j ∈ Finset.range (n + 1),
      (if (j + 1) % q = u then (-1 : ℤ) ^ (n + 1 - (j + 1)) * (Nat.choose (n + 1) (j + 1) : ℤ) else 0) =
      (∑ j ∈ Finset.range (n + 1),
        if j % q = prev then (-1 : ℤ) ^ (n - j) * (Nat.choose n j : ℤ) else 0) +
      (∑ j ∈ Finset.range (n + 1),
        if (j + 1) % q = u then (-1 : ℤ) ^ (n - j) * (Nat.choose n (j + 1) : ℤ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hsub : n + 1 - (j + 1) = n - j := by omega
    rw [hsub, Nat.choose_succ_succ, Nat.cast_add, mul_add]
    by_cases hju : (j + 1) % q = u
    · have hjp : j % q = prev := (hprev_iff j).mp hju
      simp [hju, hjp]
    · have hjp : j % q ≠ prev := fun h => hju ((hprev_iff j).mpr h)
      simp [hju, hjp]
  rw [hsum_split]
  have hshift : (∑ j ∈ Finset.range (n + 1),
      if (j + 1) % q = u then (-1 : ℤ) ^ (n - j) * (Nat.choose n (j + 1) : ℤ) else 0) +
      (if 0 % q = u then (-1 : ℤ) ^ (n + 1 - 0) * (Nat.choose (n + 1) 0 : ℤ) else 0) =
      - ∑ j ∈ Finset.range (n + 1),
        if j % q = u then (-1 : ℤ) ^ (n - j) * (Nat.choose n j : ℤ) else 0 := by
    have hrhs : ∑ j ∈ Finset.range (n + 1),
        (if j % q = u then (-1 : ℤ) ^ (n - j) * (Nat.choose n j : ℤ) else 0) =
        (∑ j ∈ Finset.range n,
          if (j + 1) % q = u then (-1 : ℤ) ^ (n - (j + 1)) * (Nat.choose n (j + 1) : ℤ) else 0) +
        (if 0 % q = u then (-1 : ℤ) ^ (n - 0) * (Nat.choose n 0 : ℤ) else 0) := by
      rw [Finset.sum_range_succ']
    rw [hrhs, Finset.sum_range_succ]
    have hlast : Nat.choose n (n + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
    simp only [hlast, Nat.cast_zero, mul_zero, ite_self, add_zero]
    rw [neg_add, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjlt : j < n := Finset.mem_range.mp hj
      have hexp : n - j = (n - (j + 1)) + 1 := by omega
      split_ifs
      · rw [hexp, pow_succ]; ring
      · simp
    · split_ifs
      · simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_succ]
        ring
      · simp
  linarith

private lemma sum_choose_KZ {q : ℕ} (hq : 0 < q) :
    ∀ (v u : ℕ), u < q →
      (∑ n ∈ Finset.range (v + 1), (Nat.choose v n : ℤ) * KZ q n u) =
        if v % q = u then 1 else 0 := by
  intro v
  induction v with
  | zero =>
    intro u _
    simp only [KZ, Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_self,
      Nat.cast_one, one_mul, Nat.zero_mod, Nat.sub_self, pow_zero]
    rfl
  | succ v ih =>
    intro u hu
    let prev := (u + q - 1) % q
    have hprev_lt : prev < q := Nat.mod_lt _ hq
    have hprev_iff : (v + 1) % q = u ↔ v % q = prev := mod_add_one_iff hq v u hu
    rw [Finset.sum_range_succ']
    have hsplit : ∑ n ∈ Finset.range (v + 1), (Nat.choose (v + 1) (n + 1) : ℤ) * KZ q (n + 1) u =
        (∑ n ∈ Finset.range (v + 1), (Nat.choose v n : ℤ) * KZ q (n + 1) u) +
        (∑ n ∈ Finset.range (v + 1), (Nat.choose v (n + 1) : ℤ) * KZ q (n + 1) u) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]
    rw [hsplit]
    have hsecond : (∑ n ∈ Finset.range (v + 1), (Nat.choose v (n + 1) : ℤ) * KZ q (n + 1) u) +
        (Nat.choose (v + 1) 0 : ℤ) * KZ q 0 u =
        ∑ n ∈ Finset.range (v + 1), (Nat.choose v n : ℤ) * KZ q n u := by
      rw [Finset.sum_range_succ]
      have hlast : Nat.choose v (v + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self v)
      simp only [hlast, Nat.cast_zero, zero_mul, add_zero]
      conv_rhs => rw [Finset.sum_range_succ']
      simp
    have hcombine : (∑ n ∈ Finset.range (v + 1), (Nat.choose v n : ℤ) * KZ q (n + 1) u) +
        (∑ n ∈ Finset.range (v + 1), (Nat.choose v n : ℤ) * KZ q n u) =
        ∑ n ∈ Finset.range (v + 1), (Nat.choose v n : ℤ) * KZ q n prev := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [KZ_succ hq n u hu]
      ring
    have hgoal : (∑ n ∈ Finset.range (v + 1), (Nat.choose v n : ℤ) * KZ q (n + 1) u) +
        (∑ n ∈ Finset.range (v + 1), (Nat.choose v (n + 1) : ℤ) * KZ q (n + 1) u) +
        (Nat.choose (v + 1) 0 : ℤ) * KZ q 0 u =
        ∑ n ∈ Finset.range (v + 1), (Nat.choose v n : ℤ) * KZ q n prev := by
      linarith
    rw [hgoal, ih prev hprev_lt]
    by_cases h : (v + 1) % q = u
    · simp [h, hprev_iff.mp h]
    · have h' : v % q ≠ prev := fun hp => h (hprev_iff.mpr hp)
      simp [h, h']

private lemma KZ_q_eq {q : ℕ} (hq : 0 < q) (u : ℕ) (hu : u < q) :
    KZ q q u = - ∑ j ∈ Finset.range (q - 1), (Nat.choose q (j + 1) : ℤ) * KZ q (j + 1) u := by
  have h := sum_choose_KZ hq q u hu
  have hr : Finset.range q = Finset.range ((q - 1) + 1) := by congr 1; omega
  rw [Finset.sum_range_succ, hr, Finset.sum_range_succ'] at h
  have hq0 : q % q = 0 := Nat.mod_self q
  have hK0 : KZ q 0 u = if 0 = u then 1 else 0 := by simp [KZ]
  rw [hq0, Nat.choose_self, Nat.choose_zero_right] at h
  simp only [Nat.cast_one, one_mul] at h
  rw [hK0] at h
  linarith

private def yStep (q : ℕ) (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => c i - (Nat.choose q (i + 1) : ℤ) * c (q - 1)

private def yVec (q : ℕ) : ℕ → ℕ → ℤ
  | 0 => fun i => if i = 0 then 1 else 0
  | n + 1 => yStep q (yVec q n)

private lemma KZ_eq_yVec {q : ℕ} (hq : 0 < q) (n u : ℕ) (hu : u < q) :
    KZ q n u = ∑ i ∈ Finset.range q, yVec q n i * KZ q i u := by
  induction n generalizing u with
  | zero =>
    rw [Finset.sum_eq_single 0]
    · simp [yVec]
    · intro i _ hi0; simp [yVec, hi0]
    · intro h0; exact absurd (Finset.mem_range.mpr hq) h0
  | succ n ih =>
    rw [KZ_succ hq n u hu, ih ((u + q - 1) % q) (Nat.mod_lt _ hq), ih u hu, ← Finset.sum_sub_distrib]
    have hlin : ∑ i ∈ Finset.range q, (yVec q n i * KZ q i ((u + q - 1) % q) - yVec q n i * KZ q i u) =
        ∑ i ∈ Finset.range q, yVec q n i * KZ q (i + 1) u := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [KZ_succ hq i u hu]
      ring
    rw [hlin]
    have hr : Finset.range q = Finset.range ((q - 1) + 1) := by congr 1; omega
    conv_lhs => rw [hr, Finset.sum_range_succ]
    have hq_pred : q - 1 + 1 = q := by omega
    rw [hq_pred, KZ_q_eq hq u hu]
    conv_rhs => rw [hr, Finset.sum_range_succ']
    simp only [yVec, yStep, zero_mul, add_zero]
    rw [mul_neg, ← sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

private lemma yVec_dvd_inv {p b : ℕ} (hp : Nat.Prime p) (hb : 0 < b) :
    let q := p ^ b
    let q' := q / p
    let s := q - q'
    ∀ n : ℕ,
      (∀ i < q, ∀ d : ℕ, i + d * s < n → (p : ℤ) ^ (d + 1) ∣ yVec q n i) ∧
      (∀ i < q', ∀ d : ℕ, i + (d + 1) * s ≤ n → (p : ℤ) ^ (d + 2) ∣ yVec q n i) := by
  dsimp only
  let q := p ^ b
  let q' := q / p
  let s := q - q'
  have hq'_eq : q' = p ^ (b - 1) := by
    dsimp only [q', q]
    have hsplit : p ^ b = p ^ (b - 1) * p := by
      rw [← pow_succ, show b - 1 + 1 = b by omega]
    rw [hsplit, Nat.mul_div_cancel _ hp.pos]
  have hq_eq : q = p * q' := by
    rw [hq'_eq]
    dsimp only [q]
    rw [← pow_succ', show b - 1 + 1 = b by omega]
  have h2q'_le : 2 * q' ≤ q := by
    have hp2 := hp.two_le
    rw [hq_eq]
    exact Nat.mul_le_mul_right q' hp2
  have hq'_pos : 0 < q' := by rw [hq'_eq]; exact pow_pos hp.pos (b - 1)
  have hdvd1 : ∀ j : ℕ, 0 < j → j < q → (p : ℤ) ∣ (Nat.choose q j : ℤ) := by
    intro j hj0 hjlt
    have h := prime_pow_dvd_choose_prime_pow hp 1 b j hj0 hb
      (by simpa [show b - 1 + 1 = b by omega] using hjlt)
    exact_mod_cast (by simpa using h : p ∣ Nat.choose q j)
  have hdvd2 : ∀ j : ℕ, 0 < j → j < q' → (p : ℤ) ^ 2 ∣ (Nat.choose q j : ℤ) := by
    intro j hj0 hjlt
    have hb2 : 2 ≤ b := by
      by_contra hlt
      have hb1 : b = 1 := by omega
      rw [hb1] at hq'_eq
      simp at hq'_eq
      omega
    have h := prime_pow_dvd_choose_prime_pow hp 2 b j hj0 hb2
      (by
        have heq : b - 2 + 1 = b - 1 := by omega
        rw [heq, ← hq'_eq]
        exact hjlt)
    exact_mod_cast h
  intro n
  change (∀ i < q, ∀ d : ℕ, i + d * s < n → (p : ℤ) ^ (d + 1) ∣ yVec q n i) ∧
    (∀ i < q', ∀ d : ℕ, i + (d + 1) * s ≤ n → (p : ℤ) ^ (d + 2) ∣ yVec q n i)
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro i _ d hlt; omega
    · intro i _ d hle
      have hs_pos : 0 < s := by dsimp only [s]; omega
      have h1 : 0 < (d + 1) * s := Nat.mul_pos (Nat.succ_pos d) hs_pos
      omega
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    refine ⟨?_, ?_⟩
    · intro i hi d hlt
      cases i with
      | zero => simp [yVec, yStep]
      | succ i' =>
        simp only [yVec, yStep]
        have hterm1 : (p : ℤ) ^ (d + 1) ∣ yVec q n i' := ih1 i' (by omega) d (by omega)
        have hterm2 : (p : ℤ) ^ (d + 1) ∣ (Nat.choose q (i' + 1) : ℤ) * yVec q n (q - 1) := by
          by_cases hi'q' : i' + 1 < q'
          · have hch2 := hdvd2 (i' + 1) (Nat.succ_pos i') hi'q'
            cases d with
            | zero =>
              have hp12 : (p : ℤ) ^ 1 ∣ (p : ℤ) ^ 2 := by
                rw [pow_one, pow_two]; exact dvd_mul_right _ _
              exact dvd_mul_of_dvd_left (dvd_trans hp12 hch2) _
            | succ d' =>
              cases d' with
              | zero => exact dvd_mul_of_dvd_left hch2 _
              | succ d'' =>
                have htail : (p : ℤ) ^ (d'' + 1) ∣ yVec q n (q - 1) :=
                  ih1 (q - 1) (by omega) d'' (by
                    have : (d'' + 1 + 1) * s = d'' * s + 2 * s := by ring
                    dsimp only [s] at this hlt ⊢
                    omega)
                have hmul := mul_dvd_mul hch2 htail
                have hexp : (p : ℤ) ^ 2 * (p : ℤ) ^ (d'' + 1) = (p : ℤ) ^ (d'' + 1 + 1 + 1) := by
                  rw [← pow_add]; congr 1; omega
                rwa [hexp] at hmul
          · have hch1 := hdvd1 (i' + 1) (Nat.succ_pos i') hi
            cases d with
            | zero =>
              simpa using dvd_mul_of_dvd_left hch1 (yVec q n (q - 1))
            | succ d' =>
              have htail : (p : ℤ) ^ (d' + 1) ∣ yVec q n (q - 1) :=
                ih1 (q - 1) (by omega) d' (by
                  have : (d' + 1) * s = d' * s + s := by ring
                  dsimp only [s] at this hlt ⊢
                  omega)
              have hmul := mul_dvd_mul hch1 htail
              have hexp : (p : ℤ) * (p : ℤ) ^ (d' + 1) = (p : ℤ) ^ (d' + 1 + 1) := by
                rw [← pow_succ']
              rwa [hexp] at hmul
        exact dvd_sub hterm1 hterm2
    · intro i hi d hle
      cases i with
      | zero => simp [yVec, yStep]
      | succ i' =>
        simp only [yVec, yStep]
        have hterm1 : (p : ℤ) ^ (d + 2) ∣ yVec q n i' := ih2 i' (by omega) d (by omega)
        have hch2 := hdvd2 (i' + 1) (Nat.succ_pos i') hi
        have hterm2 : (p : ℤ) ^ (d + 2) ∣ (Nat.choose q (i' + 1) : ℤ) * yVec q n (q - 1) := by
          cases d with
          | zero => exact dvd_mul_of_dvd_left hch2 _
          | succ d' =>
            have htail : (p : ℤ) ^ (d' + 1) ∣ yVec q n (q - 1) :=
              ih1 (q - 1) (by omega) d' (by
                have : (d' + 1 + 1) * s = d' * s + 2 * s := by ring
                dsimp only [s] at this hle ⊢
                omega)
            have hmul := mul_dvd_mul hch2 htail
            have hexp : (p : ℤ) ^ 2 * (p : ℤ) ^ (d' + 1) = (p : ℤ) ^ (d' + 1 + 2) := by
              rw [← pow_add]; congr 1; omega
            rwa [hexp] at hmul
        exact dvd_sub hterm1 hterm2

private lemma yVec_diag_zero {q : ℕ} (hq : 0 < q) :
    ∀ n < q, yVec q n n = 1 ∧ ∀ j, n < j → j < q → yVec q n j = 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨by simp [yVec], ?_⟩
    intro j hj _
    simp [yVec, Nat.ne_of_gt hj]
  | succ n ih =>
    intro hn
    have ⟨hd, hz⟩ := ih (by omega)
    have hq1 : yVec q n (q - 1) = 0 := hz (q - 1) (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · simp [yVec, yStep, hd, hq1]
    · intro j hj hjq
      cases j with
      | zero => omega
      | succ j' =>
        simp [yVec, yStep, hz j' (by omega) (by omega), hq1]

private lemma yVec_lead_cong {p b : ℕ} (hp : Nat.Prime p) (hb : 0 < b) :
    let q := p ^ b
    let q' := q / p
    let s := q - q'
    ∀ d : ℕ, ((p : ℤ) ^ (d + 1)) ∣ (yVec q (q - 1 + d * s) (q - 1) - (-(p : ℤ)) ^ d) := by
  dsimp only
  let q := p ^ b
  let q' := q / p
  let s := q - q'
  have hq'_eq : q' = p ^ (b - 1) := by
    dsimp only [q', q]
    have hsplit : p ^ b = p ^ (b - 1) * p := by
      rw [← pow_succ, show b - 1 + 1 = b by omega]
    rw [hsplit, Nat.mul_div_cancel _ hp.pos]
  have hq_eq : q = p * q' := by
    rw [hq'_eq]
    dsimp only [q]
    rw [← pow_succ', show b - 1 + 1 = b by omega]
  have hq'_pos : 0 < q' := by rw [hq'_eq]; exact pow_pos hp.pos (b - 1)
  have hq_pos : 0 < q := pow_pos hp.pos b
  have hq'_lt_q : q' < q := by
    have hp2 := hp.two_le
    rw [hq_eq]
    nlinarith
  have hdvd1 : ∀ j : ℕ, 0 < j → j < q → (p : ℤ) ∣ (Nat.choose q j : ℤ) := by
    intro j hj0 hjlt
    have h := prime_pow_dvd_choose_prime_pow hp 1 b j hj0 hb
      (by simpa [show b - 1 + 1 = b by omega] using hjlt)
    exact_mod_cast (by simpa using h : p ∣ Nat.choose q j)
  intro d
  change ((p : ℤ) ^ (d + 1)) ∣ (yVec q (q - 1 + d * s) (q - 1) - (-(p : ℤ)) ^ d)
  induction d with
  | zero =>
    have hdiag := (yVec_diag_zero hq_pos (q - 1) (by omega)).1
    simp [hdiag]
  | succ d ih =>
    have hstep_i : ∀ i : ℕ, q' ≤ i → i < q →
        ((p : ℤ) ^ (d + 2)) ∣ (yVec q (i + (d + 1) * s) i - (-(p : ℤ)) ^ (d + 1)) := by
      intro i hiq' hiq
      obtain ⟨r, rfl⟩ : ∃ r, i = q' + r := ⟨i - q', by omega⟩
      induction r with
      | zero =>
        have hq'add : q' + 0 + (d + 1) * s = (q - 1 + d * s) + 1 := by
          have : (d + 1) * s = d * s + s := by ring
          dsimp only [s] at this ⊢
          omega
        have hq'succ : q' + 0 = (q' - 1) + 1 := by omega
        rw [hq'add, hq'succ]
        simp only [yVec, yStep]
        have h1 : (p : ℤ) ^ (d + 2) ∣ yVec q (q - 1 + d * s) (q' - 1) := by
          have hinv := (yVec_dvd_inv hp hb (q - 1 + d * s)).2 (q' - 1) (by change q' - 1 < q'; omega) d
          apply hinv
          change q' - 1 + (d + 1) * s ≤ q - 1 + d * s
          have : (d + 1) * s = d * s + s := by ring
          dsimp only [s] at this ⊢
          omega
        have hch : (p : ℤ) ^ 2 ∣ ((Nat.choose q (q' - 1 + 1) : ℤ) - (p : ℤ)) := by
          rw [show q' - 1 + 1 = q' by omega]
          exact choose_q_qprime_cong hp hb
        rcases hch with ⟨t1, ht1⟩
        rcases ih with ⟨t2, ht2⟩
        have hprod : (p : ℤ) ^ (d + 2) ∣
            (-(Nat.choose q (q' - 1 + 1) : ℤ) * yVec q (q - 1 + d * s) (q - 1) - (-(p : ℤ)) ^ (d + 1)) := by
          refine ⟨-(t1 * (-(p : ℤ)) ^ d / (p : ℤ) ^ d + (p : ℤ) * t1 * t2 + t2), ?_⟩
          have hch_eq : (Nat.choose q (q' - 1 + 1) : ℤ) = (p : ℤ) + (p : ℤ) ^ 2 * t1 := by linarith
          have hy_eq : yVec q (q - 1 + d * s) (q - 1) = (-(p : ℤ)) ^ d + (p : ℤ) ^ (d + 1) * t2 := by linarith
          have hneg : (-(p : ℤ)) ^ d = (-1 : ℤ) ^ d * (p : ℤ) ^ d := by rw [← mul_pow]; simp
          have hneg1 : (-(p : ℤ)) ^ (d + 1) = (-(p : ℤ)) * (-(p : ℤ)) ^ d := by rw [pow_succ']
          have hdiv_exact : t1 * (-(p : ℤ)) ^ d / (p : ℤ) ^ d = t1 * (-1 : ℤ) ^ d := by
            rw [hneg, show t1 * ((-1 : ℤ) ^ d * (p : ℤ) ^ d) = (t1 * (-1 : ℤ) ^ d) * (p : ℤ) ^ d by ring]
            exact Int.mul_ediv_cancel _ (pow_ne_zero d (by exact_mod_cast hp.ne_zero))
          rw [hdiv_exact, hch_eq, hy_eq, hneg1, hneg]
          have hpow1 : (p : ℤ) ^ (d + 2) = (p : ℤ) ^ 2 * (p : ℤ) ^ d := by rw [← pow_add]; congr 1; omega
          have hpow2 : (p : ℤ) ^ (d + 1) = (p : ℤ) * (p : ℤ) ^ d := by rw [pow_succ']
          rw [hpow1, hpow2]
          ring
        have hrew : yVec q (q - 1 + d * s) (q' - 1) -
            (Nat.choose q (q' - 1 + 1) : ℤ) * yVec q (q - 1 + d * s) (q - 1) - (-(p : ℤ)) ^ (d + 1) =
            yVec q (q - 1 + d * s) (q' - 1) +
            (-(Nat.choose q (q' - 1 + 1) : ℤ) * yVec q (q - 1 + d * s) (q - 1) - (-(p : ℤ)) ^ (d + 1)) := by ring
        rw [hrew]
        exact dvd_add h1 hprod
      | succ r ihr =>
        have hprev := ihr (by omega) (by omega)
        have hadd1 : q' + (r + 1) + (d + 1) * s = (q' + r + (d + 1) * s) + 1 := by omega
        have hadd2 : q' + (r + 1) = (q' + r) + 1 := by omega
        rw [hadd1, hadd2]
        simp only [yVec, yStep]
        have hch1 := hdvd1 (q' + r + 1) (Nat.succ_pos _) (by omega)
        have htail : (p : ℤ) ^ (d + 1) ∣ yVec q (q' + r + (d + 1) * s) (q - 1) := by
          apply (yVec_dvd_inv hp hb (q' + r + (d + 1) * s)).1 (q - 1) (by change q - 1 < q; omega) d
          change q - 1 + d * s < q' + r + (d + 1) * s
          have : (d + 1) * s = d * s + s := by ring
          dsimp only [s] at this ⊢
          omega
        have hprod : (p : ℤ) ^ (d + 2) ∣
            (Nat.choose q (q' + r + 1) : ℤ) * yVec q (q' + r + (d + 1) * s) (q - 1) := by
          have hmul := mul_dvd_mul hch1 htail
          have hexp : (p : ℤ) * (p : ℤ) ^ (d + 1) = (p : ℤ) ^ (d + 2) := by rw [← pow_succ']
          rwa [hexp] at hmul
        have hrew : yVec q (q' + r + (d + 1) * s) (q' + r) -
            (Nat.choose q (q' + r + 1) : ℤ) * yVec q (q' + r + (d + 1) * s) (q - 1) - (-(p : ℤ)) ^ (d + 1) =
            (yVec q (q' + r + (d + 1) * s) (q' + r) - (-(p : ℤ)) ^ (d + 1)) -
            (Nat.choose q (q' + r + 1) : ℤ) * yVec q (q' + r + (d + 1) * s) (q - 1) := by ring
        rw [hrew]
        exact dvd_sub hprev hprod
    exact hstep_i (q - 1) (by omega) (by omega)

end PEqualNP.Outside.L_lib_847_aux

open PEqualNP.Outside.L_lib_847_aux

theorem PEqualNP.Outside.L_lib_847 :
    (∀ (p b a : ℕ), Nat.Prime p → 0 < b → 0 < a →
  let q := p^b
  let L := q-1+(a-1)*(q-q/p)
  let R := ZMod (p^a)
  let K := fun (n u : ℕ) =>
    ∑ j ∈ Finset.range (n+1),
      if j % q = u then (-1 : R)^(n-j) * (Nat.choose n j : R) else 0
  (∀ u < q, K L u = (-(p : R))^(a-1) ∧ K L u ≠ 0) ∧
  (∀ n > L, ∀ u < q, K n u = 0) ∧
  ∀ v : ℕ, ∀ u < q,
    (∑ n ∈ Finset.range (L+1), (Nat.choose v n : R) * K n u) =
      (if v % q = u then 1 else 0)) := by
  intro p b a hp hb ha
  dsimp only
  let q := p ^ b
  let s := q - q / p
  let L := q - 1 + (a - 1) * s
  let R := ZMod (p ^ a)
  let K : ℕ → ℕ → R := fun n u =>
    ∑ j ∈ Finset.range (n + 1),
      if j % q = u then (-1 : R) ^ (n - j) * (Nat.choose n j : R) else 0
  have hq_pos : 0 < q := pow_pos hp.pos b
  have hK_cast : ∀ n u : ℕ, K n u = (KZ q n u : R) := by
    intro n u
    dsimp only [K, KZ]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> simp
  have hpart2 : ∀ n > L, ∀ u < q, K n u = 0 := by
    intro n hn u hu
    rw [hK_cast, KZ_eq_yVec hq_pos n u hu]
    push_cast
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hiq : i < q := Finset.mem_range.mp hi
    have hdvd : (p : ℤ) ^ a ∣ yVec q n i := by
      have h := (yVec_dvd_inv hp hb n).1 i hiq (a - 1) (by
        change i + (a - 1) * s < n
        dsimp only [L] at hn
        omega)
      rwa [show a - 1 + 1 = a by omega] at h
    rcases hdvd with ⟨t, ht⟩
    have hzero : (yVec q n i : R) = 0 := by
      rw [ht]
      push_cast
      have hpa : ((p : R) ^ a) = 0 := by
        rw [← Nat.cast_pow]
        exact ZMod.natCast_self (p ^ a)
      rw [hpa, zero_mul]
    rw [hzero, zero_mul]
  have hpart1 : ∀ u < q, K L u = (-(p : R)) ^ (a - 1) ∧ K L u ≠ 0 := by
    intro u hu
    have hEq : K L u = (-(p : R)) ^ (a - 1) := by
      rw [hK_cast, KZ_eq_yVec hq_pos L u hu]
      have hr : Finset.range q = Finset.range ((q - 1) + 1) := by congr 1; omega
      rw [hr, Finset.sum_range_succ]
      push_cast
      have hrest : ∑ i ∈ Finset.range (q - 1), (yVec q L i : R) * (KZ q i u : R) = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        have hiq : i < q - 1 := Finset.mem_range.mp hi
        have hdvd : (p : ℤ) ^ a ∣ yVec q L i := by
          have h := (yVec_dvd_inv hp hb L).1 i (by change i < q; omega) (a - 1) (by
            change i + (a - 1) * s < L
            dsimp only [L]; omega)
          rwa [show a - 1 + 1 = a by omega] at h
        rcases hdvd with ⟨t, ht⟩
        have hzero : (yVec q L i : R) = 0 := by
          rw [ht]; push_cast
          have hpa : ((p : R) ^ a) = 0 := by
            rw [← Nat.cast_pow]
            exact ZMod.natCast_self (p ^ a)
          rw [hpa, zero_mul]
        rw [hzero, zero_mul]
      rw [hrest, zero_add]
      have hlead : (p : ℤ) ^ a ∣ (yVec q L (q - 1) - (-(p : ℤ)) ^ (a - 1)) := by
        have h := yVec_lead_cong hp hb (a - 1)
        rwa [show a - 1 + 1 = a by omega] at h
      have hKu : KZ q (q - 1) u = (-1 : ℤ) ^ (q - 1 - u) * (Nat.choose (q - 1) u : ℤ) := by
        dsimp only [KZ]
        rw [show q - 1 + 1 = q by omega, Finset.sum_eq_single u]
        · simp [Nat.mod_eq_of_lt hu]
        · intro j hj hne
          have hjlt : j < q := Finset.mem_range.mp hj
          simp [Nat.mod_eq_of_lt hjlt, hne]
        · intro hnu; exact absurd (Finset.mem_range.mpr hu) hnu
      have hKu_mod : (p : ℤ) ∣ (KZ q (q - 1) u - 1) := by
        rw [hKu]
        have h1 : (p : ℤ) ∣ ((Nat.choose (q - 1) u : ℤ) - (-1 : ℤ) ^ u) :=
          Int.dvd_of_emod_eq_zero (choose_pred_mod_prime hp hb u hu)
        have h2 : (p : ℤ) ∣ ((-1 : ℤ) ^ (q - 1) - 1) :=
          Int.dvd_of_emod_eq_zero (neg_one_pow_prime_pow_pred_mod hp hb)
        have hmul := dvd_mul_of_dvd_right h1 ((-1 : ℤ) ^ (q - 1 - u))
        have hadd := dvd_add hmul h2
        have hpow : (-1 : ℤ) ^ (q - 1 - u) * (-1 : ℤ) ^ u = (-1 : ℤ) ^ (q - 1) := by
          rw [← pow_add, show q - 1 - u + u = q - 1 by omega]
        have hrew : (-1 : ℤ) ^ (q - 1 - u) * ((Nat.choose (q - 1) u : ℤ) - (-1 : ℤ) ^ u) +
            ((-1 : ℤ) ^ (q - 1) - 1) =
            (-1 : ℤ) ^ (q - 1 - u) * (Nat.choose (q - 1) u : ℤ) - 1 := by
          rw [mul_sub, hpow]; ring
        rwa [hrew] at hadd
      have hprod_dvd : (p : ℤ) ^ a ∣ (yVec q L (q - 1) * KZ q (q - 1) u - (-(p : ℤ)) ^ (a - 1)) := by
        have h1 := dvd_mul_of_dvd_left hlead (KZ q (q - 1) u)
        have h2 : (p : ℤ) ^ a ∣ (-(p : ℤ)) ^ (a - 1) * (KZ q (q - 1) u - 1) := by
          have hpa1 : (p : ℤ) ^ (a - 1) ∣ (-(p : ℤ)) ^ (a - 1) := by
            rw [show (-(p : ℤ)) ^ (a - 1) = (-1 : ℤ) ^ (a - 1) * (p : ℤ) ^ (a - 1) by rw [← mul_pow]; simp]
            exact dvd_mul_left _ _
          have hmul := mul_dvd_mul hpa1 hKu_mod
          have hexp : (p : ℤ) ^ (a - 1) * (p : ℤ) = (p : ℤ) ^ a := by
            rw [← pow_succ, show a - 1 + 1 = a by omega]
          rwa [hexp] at hmul
        have hadd := dvd_add h1 h2
        have hrew : (yVec q L (q - 1) - (-(p : ℤ)) ^ (a - 1)) * KZ q (q - 1) u +
            (-(p : ℤ)) ^ (a - 1) * (KZ q (q - 1) u - 1) =
            yVec q L (q - 1) * KZ q (q - 1) u - (-(p : ℤ)) ^ (a - 1) := by ring
        rwa [hrew] at hadd
      rcases hprod_dvd with ⟨t, ht⟩
      have hZ : yVec q L (q - 1) * KZ q (q - 1) u = (-(p : ℤ)) ^ (a - 1) + (p : ℤ) ^ a * t := by linarith
      have hcast := congrArg (fun x : ℤ => (x : R)) hZ
      push_cast at hcast
      have hpa : ((p : R) ^ a) = 0 := by
        rw [← Nat.cast_pow]
        exact ZMod.natCast_self (p ^ a)
      rw [hpa, zero_mul, add_zero] at hcast
      exact hcast
    refine ⟨hEq, ?_⟩
    rw [hEq]
    intro h0
    have hmul0 : ((-1 : R) ^ (a - 1)) * ((-(p : R)) ^ (a - 1)) = 0 := by rw [h0, mul_zero]
    have hpa1 : ((p ^ (a - 1) : ℕ) : ZMod (p ^ a)) = 0 := by
      have hrew : ((-1 : R) ^ (a - 1)) * ((-(p : R)) ^ (a - 1)) = ((p ^ (a - 1) : ℕ) : R) := by
        rw [← mul_pow]; simp
      rw [← hrew]
      exact hmul0
    have hdvd : p ^ a ∣ p ^ (a - 1) := (ZMod.natCast_eq_zero_iff (p ^ (a - 1)) (p ^ a)).mp hpa1
    have hle : p ^ a ≤ p ^ (a - 1) := Nat.le_of_dvd (pow_pos hp.pos (a - 1)) hdvd
    have hlt : p ^ (a - 1) < p ^ a := by
      have hsplit : p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, show a - 1 + 1 = a by omega]
      have hp2 := hp.two_le
      have hpos := pow_pos hp.pos (a - 1)
      rw [hsplit]
      nlinarith
    omega
  refine ⟨hpart1, hpart2, ?_⟩
  intro v u hu
  have hfull : (∑ n ∈ Finset.range (v + 1), (Nat.choose v n : R) * K n u) =
      if v % q = u then 1 else 0 := by
    have hZ := sum_choose_KZ hq_pos v u hu
    have hcast := congrArg (fun x : ℤ => (x : R)) hZ
    push_cast at hcast
    have hlhs : (∑ n ∈ Finset.range (v + 1), (Nat.choose v n : R) * K n u) =
        ∑ n ∈ Finset.range (v + 1), (Nat.choose v n : R) * (KZ q n u : R) :=
      Finset.sum_congr rfl (fun n _ => by rw [hK_cast])
    rw [hlhs, hcast]
  change (∑ n ∈ Finset.range (L + 1), (Nat.choose v n : R) * K n u) = if v % q = u then 1 else 0
  rw [← hfull]
  by_cases hLv : L ≤ v
  · have hsub : Finset.range (L + 1) ⊆ Finset.range (v + 1) :=
      Finset.range_mono (by omega)
    refine Finset.sum_subset hsub (fun n _ hnL => ?_)
    have hn_gt : L < n := by
      rw [Finset.mem_range] at hnL
      omega
    rw [hpart2 n hn_gt u hu, mul_zero]
  · have hsub : Finset.range (v + 1) ⊆ Finset.range (L + 1) :=
      Finset.range_mono (by omega)
    symm
    refine Finset.sum_subset hsub (fun n _ hnv => ?_)
    have hnv_gt : v < n := by
      rw [Finset.mem_range] at hnv
      omega
    rw [Nat.choose_eq_zero_of_lt hnv_gt, Nat.cast_zero, zero_mul]
