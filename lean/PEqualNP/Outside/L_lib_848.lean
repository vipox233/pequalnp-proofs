import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_848_aux

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

private lemma residue_indicator_mod {p b a : ℕ} (hp : Nat.Prime p) (hb : 0 < b) (ha : 0 < a)
    (v u : ℕ) (hu : u < p ^ b) :
    let q := p ^ b
    let L := q - 1 + (a - 1) * (q - q / p)
    let R := ZMod (p ^ a)
    let K := fun n : ℕ =>
      ∑ l ∈ Finset.range (n + 1),
        if l % q = u then (-1 : R) ^ (n - l) * (Nat.choose n l : R) else 0
    (∑ n ∈ Finset.range (L + 1), (Nat.choose v n : R) * K n) =
      if v % q = u then 1 else 0 := by
  dsimp only
  let q := p ^ b
  let s := q - q / p
  let L := q - 1 + (a - 1) * s
  let R := ZMod (p ^ a)
  let K : ℕ → R := fun n =>
    ∑ l ∈ Finset.range (n + 1),
      if l % q = u then (-1 : R) ^ (n - l) * (Nat.choose n l : R) else 0
  have hq_pos : 0 < q := pow_pos hp.pos b
  have hK_cast : ∀ n : ℕ, K n = (KZ q n u : R) := by
    intro n
    dsimp only [K, KZ]
    push_cast
    refine Finset.sum_congr rfl (fun l _ => ?_)
    split_ifs <;> simp
  have hvanish : ∀ n > L, K n = 0 := by
    intro n hn
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
      rw [ht]; push_cast
      have hpa : ((p : R) ^ a) = 0 := by
        rw [← Nat.cast_pow]
        exact ZMod.natCast_self (p ^ a)
      rw [hpa, zero_mul]
    rw [hzero, zero_mul]
  have hfull : (∑ n ∈ Finset.range (v + 1), (Nat.choose v n : R) * K n) =
      if v % q = u then 1 else 0 := by
    have hZ := sum_choose_KZ hq_pos v u hu
    have hcast := congrArg (fun x : ℤ => (x : R)) hZ
    push_cast at hcast
    have hlhs : (∑ n ∈ Finset.range (v + 1), (Nat.choose v n : R) * K n) =
        ∑ n ∈ Finset.range (v + 1), (Nat.choose v n : R) * (KZ q n u : R) :=
      Finset.sum_congr rfl (fun n _ => by rw [hK_cast])
    rw [hlhs, hcast]
  change (∑ n ∈ Finset.range (L + 1), (Nat.choose v n : R) * K n) = if v % q = u then 1 else 0
  rw [← hfull]
  by_cases hLv : L ≤ v
  · have hsub : Finset.range (L + 1) ⊆ Finset.range (v + 1) := Finset.range_mono (by omega)
    refine Finset.sum_subset hsub (fun n _ hnL => ?_)
    have hn_gt : L < n := by rw [Finset.mem_range] at hnL; omega
    rw [hvanish n hn_gt, mul_zero]
  · have hsub : Finset.range (v + 1) ⊆ Finset.range (L + 1) := Finset.range_mono (by omega)
    symm
    refine Finset.sum_subset hsub (fun n _ hnv => ?_)
    have hnv_gt : v < n := by rw [Finset.mem_range] at hnv; omega
    rw [Nat.choose_eq_zero_of_lt hnv_gt, Nat.cast_zero, zero_mul]

private lemma choose_mul_choose_eq (i j n : ℕ) :
    Nat.choose (j + n) j * Nat.choose i (j + n) = Nat.choose i j * Nat.choose (i - j) n := by
  rw [Nat.mul_comm, Nat.choose_mul (Nat.le_add_right j n), show j + n - j = n by omega]

private lemma coeff_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Polynomial ℚ) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

private noncomputable def fallPoly (n : ℕ) : Polynomial ℚ :=
  ∏ k ∈ Finset.range n, (Polynomial.X - Polynomial.C (k : ℚ))

private lemma fallPoly_eval (n i : ℕ) :
    (fallPoly n).eval (i : ℚ) = (n.factorial : ℚ) * (Nat.choose i n : ℚ) := by
  have hdesc : (fallPoly n).eval (i : ℚ) = (Nat.descFactorial i n : ℚ) := by
    induction n with
    | zero => simp [fallPoly]
    | succ n ih =>
      dsimp only [fallPoly] at ih ⊢
      rw [Finset.prod_range_succ, Polynomial.eval_mul, ih, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, Nat.descFactorial_succ]
      by_cases hni : n ≤ i
      · rw [Nat.cast_mul, Nat.cast_sub hni]; ring
      · have h0 : Nat.descFactorial i n = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        have h1 : i - n = 0 := by omega
        rw [h0, h1]; simp
  rw [hdesc]
  have h := Nat.descFactorial_eq_factorial_mul_choose i n
  exact_mod_cast h

private lemma fallPoly_natDegree_le (n : ℕ) : (fallPoly n).natDegree ≤ n := by
  induction n with
  | zero => simp [fallPoly]
  | succ n ih =>
    dsimp only [fallPoly] at ih ⊢
    rw [Finset.prod_range_succ]
    have hdeg1 : (Polynomial.X - Polynomial.C (n : ℚ)).natDegree ≤ 1 := by
      rw [Polynomial.natDegree_X_sub_C]
    exact le_trans (Polynomial.natDegree_mul_le) (by omega)

private lemma iter_deriv_X_pow (i j : ℕ) :
    (Polynomial.derivative^[j] (Polynomial.X ^ i : Polynomial ℚ)) =
      Polynomial.C (Nat.descFactorial i j : ℚ) * Polynomial.X ^ (i - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
    rw [Nat.descFactorial_succ, Nat.cast_mul, ← mul_assoc, Polynomial.C_mul]
    by_cases hji : j ≤ i
    · have hsub : i - (j + 1) = i - j - 1 := by omega
      rw [hsub]
      simp only [Polynomial.C_eq_natCast]
      ring
    · have h0 : Nat.descFactorial i j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      have h1 : i - j = 0 := by omega
      rw [h0, h1]
      simp

private lemma iter_deriv_linear (j : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℚ) (f : ι → Polynomial ℚ) :
    Polynomial.derivative^[j] (∑ i ∈ s, Polynomial.C (c i) * f i) =
      ∑ i ∈ s, Polynomial.C (c i) * Polynomial.derivative^[j] (f i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.derivative_C_mul, Function.iterate_succ_apply']

private lemma X_pow_sub_one_dvd_of_residue_sum_zero {q : ℕ} (hq : 0 < q) (P : Polynomial ℚ)
    (hres : ∀ u < q, (∑ k ∈ Finset.range (P.natDegree + 1), if k % q = u then P.coeff k else 0) = 0) :
    (Polynomial.X ^ q - 1 : Polynomial ℚ) ∣ P := by
  have hterm : ∀ k : ℕ, (Polynomial.X ^ q - 1 : Polynomial ℚ) ∣
      (Polynomial.X ^ k - Polynomial.X ^ (k % q)) := by
    intro k
    have hk : k = k % q + q * (k / q) := (Nat.mod_add_div k q).symm
    have hpow : (Polynomial.X ^ k - Polynomial.X ^ (k % q) : Polynomial ℚ) =
        Polynomial.X ^ (k % q) * ((Polynomial.X ^ q) ^ (k / q) - 1) := by
      have h1 : (Polynomial.X : Polynomial ℚ) ^ k = Polynomial.X ^ (k % q) * (Polynomial.X ^ q) ^ (k / q) := by
        conv_lhs => rw [hk]
        rw [pow_add, pow_mul]
      rw [h1]
      ring
    rw [hpow]
    exact dvd_mul_of_dvd_right (sub_one_dvd_pow_sub_one (Polynomial.X ^ q : Polynomial ℚ) (k / q)) _
  have hP_eq : P = ∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff k) * Polynomial.X ^ k :=
    Polynomial.as_sum_range_C_mul_X_pow P
  have hrem_zero : ∑ k ∈ Finset.range (P.natDegree + 1),
      Polynomial.C (P.coeff k) * Polynomial.X ^ (k % q) = 0 := by
    have hmaps : ∀ k ∈ Finset.range (P.natDegree + 1), k % q ∈ Finset.range q :=
      fun k _ => Finset.mem_range.mpr (Nat.mod_lt k hq)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_eq_zero (fun u hu => ?_)
    have huq : u < q := Finset.mem_range.mp hu
    have hfac : ∑ k ∈ (Finset.range (P.natDegree + 1)).filter (fun k => k % q = u),
        Polynomial.C (P.coeff k) * Polynomial.X ^ (k % q) =
        Polynomial.C (∑ k ∈ Finset.range (P.natDegree + 1), if k % q = u then P.coeff k else 0) *
          Polynomial.X ^ u := by
      rw [← Finset.sum_filter, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [(Finset.mem_filter.mp hk).2]
    rw [hfac, hres u huq, map_zero, zero_mul]
  have hdiff : P = ∑ k ∈ Finset.range (P.natDegree + 1),
      Polynomial.C (P.coeff k) * (Polynomial.X ^ k - Polynomial.X ^ (k % q)) := by
    calc P = P - 0 := (sub_zero P).symm
      _ = (∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff k) * Polynomial.X ^ k) -
          (∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff k) * Polynomial.X ^ (k % q)) := by
            rw [← hP_eq, hrem_zero]
      _ = ∑ k ∈ Finset.range (P.natDegree + 1),
            Polynomial.C (P.coeff k) * (Polynomial.X ^ k - Polynomial.X ^ (k % q)) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [hdiff]
  exact Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_right (hterm k) _)

private noncomputable def phiPoly (q : ℕ) : Polynomial ℚ :=
  ∑ r ∈ Finset.range q, Polynomial.X ^ r

private lemma X_sub_one_mul_phiPoly (q : ℕ) :
    (Polynomial.X - 1 : Polynomial ℚ) * phiPoly q = Polynomial.X ^ q - 1 := by
  dsimp only [phiPoly]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    rw [pow_succ]
    ring

private lemma phiPoly_monic {q : ℕ} (hq : 0 < q) : (phiPoly q).Monic := by
  have hprod : ((Polynomial.X - 1 : Polynomial ℚ) * phiPoly q).Monic := by
    rw [X_sub_one_mul_phiPoly]
    have hC1 : (1 : Polynomial ℚ) = Polynomial.C 1 := (map_one Polynomial.C).symm
    rw [hC1]
    exact Polynomial.monic_X_pow_sub_C (1 : ℚ) (Nat.ne_of_gt hq)
  have hX1 : (Polynomial.X - 1 : Polynomial ℚ).Monic := by
    rw [← map_one Polynomial.C]
    exact Polynomial.monic_X_sub_C (1 : ℚ)
  exact Polynomial.Monic.of_mul_monic_left hX1 hprod

private lemma phiPoly_natDegree {q : ℕ} (hq : 0 < q) : (phiPoly q).natDegree = q - 1 := by
  have hprod := X_sub_one_mul_phiPoly q
  have hC1 : (1 : Polynomial ℚ) = Polynomial.C 1 := (map_one Polynomial.C).symm
  have hX1 : (Polynomial.X - 1 : Polynomial ℚ).Monic := by
    rw [hC1]; exact Polynomial.monic_X_sub_C (1 : ℚ)
  have hphi := phiPoly_monic hq
  have hdeg := Polynomial.Monic.natDegree_mul hX1 hphi
  rw [hprod, hC1, Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_X_sub_C] at hdeg
  omega

private lemma isCoprime_phiPoly_deriv {q : ℕ} (hq : 0 < q) :
    IsCoprime (phiPoly q) (Polynomial.derivative (phiPoly q)) := by
  have h1 := congrArg Polynomial.derivative (X_sub_one_mul_phiPoly q)
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_one, Polynomial.derivative_X_pow, sub_zero, one_mul] at h1
  have hmul : Polynomial.X * phiPoly q + Polynomial.X * ((Polynomial.X - 1) * Polynomial.derivative (phiPoly q)) =
      Polynomial.C (q : ℚ) * Polynomial.X ^ q := by
    calc Polynomial.X * phiPoly q + Polynomial.X * ((Polynomial.X - 1) * Polynomial.derivative (phiPoly q))
        = Polynomial.X * (phiPoly q + (Polynomial.X - 1) * Polynomial.derivative (phiPoly q)) := by ring
      _ = Polynomial.X * (Polynomial.C (q : ℚ) * Polynomial.X ^ (q - 1)) := by
            rw [h1]
      _ = Polynomial.C (q : ℚ) * (Polynomial.X * Polynomial.X ^ (q - 1)) := by ring
      _ = Polynomial.C (q : ℚ) * Polynomial.X ^ q := by
            rw [← pow_succ', show q - 1 + 1 = q by omega]
  have hXq : Polynomial.X ^ q = (Polynomial.X - 1) * phiPoly q + 1 := by
    have := X_sub_one_mul_phiPoly q
    linear_combination -this
  rw [hXq] at hmul
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  refine ⟨Polynomial.C ((q : ℚ)⁻¹) * (Polynomial.X - Polynomial.C (q : ℚ) * (Polynomial.X - 1)),
    Polynomial.C ((q : ℚ)⁻¹) * (Polynomial.X * (Polynomial.X - 1)), ?_⟩
  have hcomb : (Polynomial.X - Polynomial.C (q : ℚ) * (Polynomial.X - 1)) * phiPoly q +
      (Polynomial.X * (Polynomial.X - 1)) * Polynomial.derivative (phiPoly q) = Polynomial.C (q : ℚ) := by
    linear_combination hmul
  calc Polynomial.C ((q : ℚ)⁻¹) * (Polynomial.X - Polynomial.C (q : ℚ) * (Polynomial.X - 1)) * phiPoly q +
        Polynomial.C ((q : ℚ)⁻¹) * (Polynomial.X * (Polynomial.X - 1)) * Polynomial.derivative (phiPoly q)
      = Polynomial.C ((q : ℚ)⁻¹) * ((Polynomial.X - Polynomial.C (q : ℚ) * (Polynomial.X - 1)) * phiPoly q +
          (Polynomial.X * (Polynomial.X - 1)) * Polynomial.derivative (phiPoly q)) := by ring
    _ = Polynomial.C ((q : ℚ)⁻¹) * Polynomial.C (q : ℚ) := by rw [hcomb]
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hq0, map_one]

private lemma isCoprime_X_sub_one_phiPoly {q : ℕ} (hq : 0 < q) :
    IsCoprime (Polynomial.X - 1 : Polynomial ℚ) (phiPoly q) := by
  have hrem : ∀ n : ℕ, phiPoly n - Polynomial.C (n : ℚ) =
      (Polynomial.X - 1 : Polynomial ℚ) * (∑ r ∈ Finset.range n, phiPoly r) := by
    intro n
    induction n with
    | zero => simp [phiPoly]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ← ih, X_sub_one_mul_phiPoly]
      dsimp only [phiPoly]
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, map_add, map_one]
      ring
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  refine ⟨-Polynomial.C ((q : ℚ)⁻¹) * (∑ r ∈ Finset.range q, phiPoly r), Polynomial.C ((q : ℚ)⁻¹), ?_⟩
  calc -Polynomial.C ((q : ℚ)⁻¹) * (∑ r ∈ Finset.range q, phiPoly r) * (Polynomial.X - 1) +
        Polynomial.C ((q : ℚ)⁻¹) * phiPoly q
      = Polynomial.C ((q : ℚ)⁻¹) * (phiPoly q - (Polynomial.X - 1) * (∑ r ∈ Finset.range q, phiPoly r)) := by ring
    _ = Polynomial.C ((q : ℚ)⁻¹) * Polynomial.C (q : ℚ) := by
          congr 1; linear_combination hrem q
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hq0, map_one]

private lemma isCoprime_phiPoly_X {q : ℕ} (hq : 0 < q) :
    IsCoprime (phiPoly q) (Polynomial.X : Polynomial ℚ) := by
  have hsplit : phiPoly q = 1 + Polynomial.X * (∑ r ∈ Finset.range (q - 1), Polynomial.X ^ r) := by
    dsimp only [phiPoly]
    conv_lhs => rw [show q = (q - 1) + 1 by omega, Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', ← Finset.mul_sum]
    ring
  refine ⟨1, -(∑ r ∈ Finset.range (q - 1), Polynomial.X ^ r), ?_⟩
  rw [hsplit]
  ring

private lemma isCoprime_phiPoly_of_coprime {q1 q2 : ℕ} (hq1 : 1 < q1) (hq2 : 1 < q2)
    (hcop : Nat.Coprime q1 q2) :
    IsCoprime (phiPoly q1) (phiPoly q2) := by
  have : NeZero q2 := ⟨by omega⟩
  have : Fact (1 < q2) := ⟨hq2⟩
  let uUnit : (ZMod q2)ˣ := (ZMod.unitOfCoprime q1 hcop)⁻¹
  let u : ℕ := (uUnit : ZMod q2).val
  have hu_mod : (u * q1) % q2 = 1 := by
    have hZ : ((u * q1 : ℕ) : ZMod q2) = 1 := by
      push_cast
      have hcast : (u : ZMod q2) = (uUnit : ZMod q2) := ZMod.natCast_zmod_val _
      rw [hcast]
      have hmul : uUnit * ZMod.unitOfCoprime q1 hcop = 1 := inv_mul_cancel _
      have := congrArg (fun x : (ZMod q2)ˣ => (x : ZMod q2)) hmul
      simpa using this
    have hval := congrArg ZMod.val hZ
    rw [ZMod.val_natCast, ZMod.val_one] at hval
    exact hval
  let v : ℕ := (u * q1) / q2
  have huv : u * q1 = v * q2 + 1 := by
    have h := Nat.div_add_mod (u * q1) q2
    rw [hu_mod] at h
    dsimp only [v]
    linarith
  have hdvd1 : (Polynomial.X ^ q1 - 1 : Polynomial ℚ) ∣ (Polynomial.X ^ (u * q1) - 1) := by
    rw [Nat.mul_comm, pow_mul]
    exact sub_one_dvd_pow_sub_one (Polynomial.X ^ q1 : Polynomial ℚ) u
  have hdvd2 : (Polynomial.X ^ q2 - 1 : Polynomial ℚ) ∣ (Polynomial.X ^ (v * q2) - 1) := by
    rw [Nat.mul_comm, pow_mul]
    exact sub_one_dvd_pow_sub_one (Polynomial.X ^ q2 : Polynomial ℚ) v
  rcases hdvd1 with ⟨A1, hA1⟩
  rcases hdvd2 with ⟨A2, hA2⟩
  have hdiff : (Polynomial.X - 1 : Polynomial ℚ) * (phiPoly q1 * A1 - phiPoly q2 * A2) =
      (Polynomial.X - 1) * Polynomial.X ^ (v * q2) := by
    calc (Polynomial.X - 1 : Polynomial ℚ) * (phiPoly q1 * A1 - phiPoly q2 * A2)
        = ((Polynomial.X - 1) * phiPoly q1) * A1 - ((Polynomial.X - 1) * phiPoly q2) * A2 := by ring
      _ = (Polynomial.X ^ q1 - 1) * A1 - (Polynomial.X ^ q2 - 1) * A2 := by
            rw [X_sub_one_mul_phiPoly, X_sub_one_mul_phiPoly]
      _ = (Polynomial.X ^ (u * q1) - 1) - (Polynomial.X ^ (v * q2) - 1) := by rw [← hA1, ← hA2]
      _ = Polynomial.X ^ (v * q2 + 1) - Polynomial.X ^ (v * q2) := by rw [huv]; ring
      _ = (Polynomial.X - 1) * Polynomial.X ^ (v * q2) := by rw [pow_succ]; ring
  have hX1_ne : (Polynomial.X - 1 : Polynomial ℚ) ≠ 0 := (Polynomial.monic_X_sub_C (1 : ℚ)).ne_zero
  have hbez1 : phiPoly q1 * A1 - phiPoly q2 * A2 = Polynomial.X ^ (v * q2) :=
    mul_left_cancel₀ hX1_ne hdiff
  have hcopX : IsCoprime (phiPoly q1) (Polynomial.X ^ (v * q2) : Polynomial ℚ) :=
    (isCoprime_phiPoly_X (by omega)).pow_right
  rcases hcopX with ⟨c1, c2, hc⟩
  refine ⟨c1 + c2 * A1, -c2 * A2, ?_⟩
  calc (c1 + c2 * A1) * phiPoly q1 + (-c2 * A2) * phiPoly q2
      = c1 * phiPoly q1 + c2 * (phiPoly q1 * A1 - phiPoly q2 * A2) := by ring
    _ = c1 * phiPoly q1 + c2 * Polynomial.X ^ (v * q2) := by rw [hbez1]
    _ = 1 := hc

private lemma pow_dvd_of_iter_deriv_dvd {Φ : Polynomial ℚ} (hcop : IsCoprime Φ (Polynomial.derivative Φ))
    (hΦ0 : Φ ≠ 0) :
    ∀ (m : ℕ) (P : Polynomial ℚ), (∀ j < m, Φ ∣ Polynomial.derivative^[j] P) → Φ ^ m ∣ P := by
  intro m
  induction m with
  | zero => intro P _; simp
  | succ m ih =>
    intro P hP
    cases m with
    | zero => simpa using hP 0 (Nat.zero_lt_one)
    | succ m' =>
      have hPm : Φ ^ (m' + 1) ∣ P := ih P (fun j hj => hP j (by omega))
      have hPd : Φ ^ (m' + 1) ∣ Polynomial.derivative P :=
        ih (Polynomial.derivative P) (fun j hj => by
          rw [← Function.iterate_succ_apply Polynomial.derivative j P]
          exact hP (j + 1) (by omega))
      rcases hPm with ⟨S, hS⟩
      have hderiv_eq : Polynomial.derivative P =
          Polynomial.C ((m' + 1 : ℕ) : ℚ) * Φ ^ m' * Polynomial.derivative Φ * S +
            Φ ^ (m' + 1) * Polynomial.derivative S := by
        rw [hS, Polynomial.derivative_mul, Polynomial.derivative_pow]
        simp only [Polynomial.C_eq_natCast, Nat.add_sub_cancel]
      have hdvd_term : Φ ^ (m' + 1) ∣
          Polynomial.C ((m' + 1 : ℕ) : ℚ) * Φ ^ m' * Polynomial.derivative Φ * S := by
        have h1 : Φ ^ (m' + 1) ∣ Φ ^ (m' + 1) * Polynomial.derivative S := dvd_mul_right _ _
        have hsub := dvd_sub hPd h1
        have hrew : Polynomial.derivative P - Φ ^ (m' + 1) * Polynomial.derivative S =
            Polynomial.C ((m' + 1 : ℕ) : ℚ) * Φ ^ m' * Polynomial.derivative Φ * S := by
          rw [hderiv_eq]; ring
        rwa [hrew] at hsub
      rcases hdvd_term with ⟨T, hT⟩
      have hmul_eq : Φ ^ m' * (Φ * T) =
          Φ ^ m' * (Polynomial.C ((m' + 1 : ℕ) : ℚ) * (Polynomial.derivative Φ * S)) := by
        calc Φ ^ m' * (Φ * T) = Φ ^ (m' + 1) * T := by rw [pow_succ]; ring
          _ = Polynomial.C ((m' + 1 : ℕ) : ℚ) * Φ ^ m' * Polynomial.derivative Φ * S := hT.symm
          _ = Φ ^ m' * (Polynomial.C ((m' + 1 : ℕ) : ℚ) * (Polynomial.derivative Φ * S)) := by ring
      have hcancel := mul_left_cancel₀ (pow_ne_zero m' hΦ0) hmul_eq
      have hscalar_ne : ((m' + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m')
      have hdvd_dS : Φ ∣ Polynomial.derivative Φ * S := by
        refine ⟨Polynomial.C (((m' + 1 : ℕ) : ℚ)⁻¹) * T, ?_⟩
        calc Polynomial.derivative Φ * S
            = Polynomial.C (((m' + 1 : ℕ) : ℚ)⁻¹) *
                (Polynomial.C ((m' + 1 : ℕ) : ℚ) * (Polynomial.derivative Φ * S)) := by
                rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hscalar_ne, map_one, one_mul]
          _ = Polynomial.C (((m' + 1 : ℕ) : ℚ)⁻¹) * (Φ * T) := by rw [← hcancel]
          _ = Φ * (Polynomial.C (((m' + 1 : ℕ) : ℚ)⁻¹) * T) := by ring
      have hdvd_S : Φ ∣ S := hcop.dvd_of_dvd_mul_left hdvd_dS
      rcases hdvd_S with ⟨U, rfl⟩
      refine ⟨U, ?_⟩
      rw [hS, pow_succ]
      ring

end PEqualNP.Outside.L_lib_848_aux

open PEqualNP.Outside.L_lib_848_aux

theorem PEqualNP.Outside.L_lib_848 :
    (∀ (D P d : ℕ) (primes : Finset ℕ) (b depth : ℕ → ℕ) (prec : ℕ → ℕ → ℕ),
  let q := fun p => p^(b p)
  let cut := fun (p j : ℕ) => q p-1+(prec p j-1)*(q p-q p/p)
  (∀ p ∈ primes, Nat.Prime p ∧ 0 < b p) →
  (∀ p ∈ primes, ∀ j < depth p,
    0 < prec p j ∧ P * Nat.choose D j < p^(prec p j) ∧ j+cut p j ≤ d) →
  D < d+1 + ∑ p ∈ primes, depth p * (q p-1) →
  let bin := fun (f : Fin (D+1) → ℕ) (n : ℕ) =>
    ∑ i, f i * Nat.choose i.val n
  let powMom := fun (f : Fin (D+1) → ℕ) (n : ℕ) =>
    ∑ i, f i * i.val^n
  (∀ (f : Fin (D+1) → ℕ), (∑ i, f i) ≤ P →
    ∀ p ∈ primes, ∀ j < depth p, ∀ u < q p,
      let R := ZMod (p^(prec p j))
      let K := fun (n : ℕ) =>
        ∑ l ∈ Finset.range (n+1),
          if l % q p = u then (-1 : R)^(n-l)*(Nat.choose n l : R) else 0
      (∑ i : Fin (D+1), if (i.val-j) % q p = u then f i * Nat.choose i.val j else 0) =
        (∑ n ∈ Finset.range (cut p j+1),
          K n * (Nat.choose (j+n) j : R) * (bin f (j+n) : R)).val) ∧
  ∀ (f g : Fin (D+1) → ℕ), (∑ i, f i) ≤ P → (∑ i, g i) ≤ P →
    (∀ n ≤ d, powMom f n = powMom g n) → f = g) := by
  intro D P d primes b depth prec
  dsimp only
  intro hpr hdepth hD
  let q : ℕ → ℕ := fun p => p ^ (b p)
  let cut : ℕ → ℕ → ℕ := fun p j => q p - 1 + (prec p j - 1) * (q p - q p / p)
  let bin : (Fin (D + 1) → ℕ) → ℕ → ℕ := fun f n => ∑ i : Fin (D + 1), f i * Nat.choose i.val n
  let powMom : (Fin (D + 1) → ℕ) → ℕ → ℕ := fun f n => ∑ i : Fin (D + 1), f i * i.val ^ n
  have hpart1 : ∀ (f : Fin (D + 1) → ℕ), (∑ i, f i) ≤ P →
      ∀ p ∈ primes, ∀ j < depth p, ∀ u < q p,
        let R := ZMod (p ^ (prec p j))
        let K := fun n : ℕ =>
          ∑ l ∈ Finset.range (n + 1),
            if l % q p = u then (-1 : R) ^ (n - l) * (Nat.choose n l : R) else 0
        (∑ i : Fin (D + 1), if (i.val - j) % q p = u then f i * Nat.choose i.val j else 0) =
          (∑ n ∈ Finset.range (cut p j + 1),
            K n * (Nat.choose (j + n) j : R) * (bin f (j + n) : R)).val := by
    intro f hfP p hp j hj u hu
    dsimp only
    rcases hpr p hp with ⟨hp_prime, hbp⟩
    rcases hdepth p hp j hj with ⟨hprec, hbound, _⟩
    let R := ZMod (p ^ (prec p j))
    let K : ℕ → R := fun n =>
      ∑ l ∈ Finset.range (n + 1),
        if l % q p = u then (-1 : R) ^ (n - l) * (Nat.choose n l : R) else 0
    let S : ℕ := ∑ i : Fin (D + 1), if (i.val - j) % q p = u then f i * Nat.choose i.val j else 0
    have hS_lt : S < p ^ (prec p j) := by
      have h1 : S ≤ ∑ i : Fin (D + 1), f i * Nat.choose D j := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hiD : i.val ≤ D := Nat.lt_succ_iff.mp i.isLt
        have hch : Nat.choose i.val j ≤ Nat.choose D j := Nat.choose_le_choose j hiD
        split_ifs
        · exact Nat.mul_le_mul_left (f i) hch
        · exact Nat.zero_le _
      have h2 : (∑ i : Fin (D + 1), f i * Nat.choose D j) ≤ P * Nat.choose D j := by
        rw [← Finset.sum_mul]
        exact Nat.mul_le_mul_right _ hfP
      omega
    have hmod_eq : (S : R) = ∑ n ∈ Finset.range (cut p j + 1),
        K n * (Nat.choose (j + n) j : R) * (bin f (j + n) : R) := by
      have hrhs : (∑ n ∈ Finset.range (cut p j + 1),
          K n * (Nat.choose (j + n) j : R) * (bin f (j + n) : R)) =
          ∑ i : Fin (D + 1), (f i : R) * (Nat.choose i.val j : R) *
            (∑ n ∈ Finset.range (cut p j + 1), (Nat.choose (i.val - j) n : R) * K n) := by
        calc ∑ n ∈ Finset.range (cut p j + 1), K n * (Nat.choose (j + n) j : R) * (bin f (j + n) : R)
            = ∑ n ∈ Finset.range (cut p j + 1), ∑ i : Fin (D + 1),
                K n * (Nat.choose (j + n) j : R) * ((f i : R) * (Nat.choose i.val (j + n) : R)) := by
                  refine Finset.sum_congr rfl (fun n _ => ?_)
                  dsimp only [bin]
                  push_cast
                  rw [Finset.mul_sum]
          _ = ∑ i : Fin (D + 1), ∑ n ∈ Finset.range (cut p j + 1),
                K n * (Nat.choose (j + n) j : R) * ((f i : R) * (Nat.choose i.val (j + n) : R)) :=
                  Finset.sum_comm
          _ = ∑ i : Fin (D + 1), (f i : R) * (Nat.choose i.val j : R) *
                (∑ n ∈ Finset.range (cut p j + 1), (Nat.choose (i.val - j) n : R) * K n) := by
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun n _ => ?_)
                  have hch := choose_mul_choose_eq i.val j n
                  have hchR : (Nat.choose (j + n) j : R) * (Nat.choose i.val (j + n) : R) =
                      (Nat.choose i.val j : R) * (Nat.choose (i.val - j) n : R) := by
                    simpa only [Nat.cast_mul] using congrArg (fun x : ℕ => (x : R)) hch
                  calc K n * (Nat.choose (j + n) j : R) * ((f i : R) * (Nat.choose i.val (j + n) : R))
                      = (f i : R) * ((Nat.choose (j + n) j : R) * (Nat.choose i.val (j + n) : R)) * K n := by ring
                    _ = (f i : R) * ((Nat.choose i.val j : R) * (Nat.choose (i.val - j) n : R)) * K n := by rw [hchR]
                    _ = (f i : R) * (Nat.choose i.val j : R) * ((Nat.choose (i.val - j) n : R) * K n) := by ring
      rw [hrhs]
      dsimp only [S]
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hind := residue_indicator_mod hp_prime hbp hprec (i.val - j) u hu
      change (∑ n ∈ Finset.range (cut p j + 1), (Nat.choose (i.val - j) n : R) * K n) =
        if (i.val - j) % q p = u then 1 else 0 at hind
      rw [hind]
      split_ifs <;> simp
    rw [← hmod_eq]
    exact (ZMod.val_natCast_of_lt hS_lt).symm
  refine ⟨hpart1, ?_⟩
  intro f g hfP hgP hpow
  have hbin_eq : ∀ n ≤ d, bin f n = bin g n := by
    intro n hn
    have heval_eq : (∑ i : Fin (D + 1), ((f i : ℚ) - (g i : ℚ)) * (fallPoly n).eval (i.val : ℚ)) = 0 := by
      have hdeg := fallPoly_natDegree_le n
      have hexp : ∀ i : Fin (D + 1), (fallPoly n).eval (i.val : ℚ) =
          ∑ k ∈ Finset.range (n + 1), (fallPoly n).coeff k * (i.val : ℚ) ^ k := by
        intro i
        rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
      calc ∑ i : Fin (D + 1), ((f i : ℚ) - (g i : ℚ)) * (fallPoly n).eval (i.val : ℚ)
          = ∑ i : Fin (D + 1), ∑ k ∈ Finset.range (n + 1),
              ((f i : ℚ) - (g i : ℚ)) * ((fallPoly n).coeff k * (i.val : ℚ) ^ k) := by
                refine Finset.sum_congr rfl (fun i _ => by rw [hexp i, Finset.mul_sum])
        _ = ∑ k ∈ Finset.range (n + 1), (fallPoly n).coeff k *
              (∑ i : Fin (D + 1), ((f i : ℚ) - (g i : ℚ)) * (i.val : ℚ) ^ k) := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl (fun k _ => ?_)
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun i _ => by ring)
        _ = 0 := by
                refine Finset.sum_eq_zero (fun k hk => ?_)
                have hkd : k ≤ d := by
                  have := Finset.mem_range.mp hk
                  omega
                have hpm := hpow k hkd
                have hpmQ : (∑ i : Fin (D + 1), (f i : ℚ) * (i.val : ℚ) ^ k) =
                    ∑ i : Fin (D + 1), (g i : ℚ) * (i.val : ℚ) ^ k := by
                  exact_mod_cast hpm
                have hzero : (∑ i : Fin (D + 1), ((f i : ℚ) - (g i : ℚ)) * (i.val : ℚ) ^ k) = 0 := by
                  have hsub : (∑ i : Fin (D + 1), ((f i : ℚ) - (g i : ℚ)) * (i.val : ℚ) ^ k) =
                      (∑ i : Fin (D + 1), (f i : ℚ) * (i.val : ℚ) ^ k) -
                      (∑ i : Fin (D + 1), (g i : ℚ) * (i.val : ℚ) ^ k) := by
                    rw [← Finset.sum_sub_distrib]
                    refine Finset.sum_congr rfl (fun i _ => by ring)
                  rw [hsub, hpmQ, sub_self]
                rw [hzero, mul_zero]
    have hfac : (n.factorial : ℚ) * ((bin f n : ℚ) - (bin g n : ℚ)) = 0 := by
      have heq : (n.factorial : ℚ) * ((bin f n : ℚ) - (bin g n : ℚ)) =
          ∑ i : Fin (D + 1), ((f i : ℚ) - (g i : ℚ)) * (fallPoly n).eval (i.val : ℚ) := by
        dsimp only [bin]
        push_cast
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [fallPoly_eval n i.val]
        ring
      rw [heq, heval_eq]
    have hfn0 : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hdiff0 : (bin f n : ℚ) - (bin g n : ℚ) = 0 := (mul_eq_zero.mp hfac).resolve_left hfn0
    have hQ : (bin f n : ℚ) = (bin g n : ℚ) := sub_eq_zero.mp hdiff0
    exact_mod_cast hQ
  let H : Polynomial ℚ := ∑ i : Fin (D + 1), Polynomial.C ((f i : ℚ) - (g i : ℚ)) * Polynomial.X ^ i.val
  have hH_coeff : ∀ k : ℕ, H.coeff k = if hk : k < D + 1 then (f ⟨k, hk⟩ : ℚ) - (g ⟨k, hk⟩ : ℚ) else 0 := by
    intro k
    dsimp only [H]
    rw [coeff_finset_sum]
    split_ifs with hk
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
      · intro i _ hne
        have hval_ne : i.val ≠ k := fun h => hne (Fin.ext h)
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        simp [Ne.symm hval_ne]
      · intro hnu; exact absurd (Finset.mem_univ _) hnu
    · refine Finset.sum_eq_zero (fun i _ => ?_)
      have hval_ne : k ≠ i.val := fun h => hk (h ▸ i.isLt)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [hval_ne]
  have hH_deg : H.natDegree ≤ D := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => ?_)
    rw [hH_coeff k]
    simp [show ¬ k < D + 1 by omega]
  have hdvd_A : (Polynomial.X - 1 : Polynomial ℚ) ^ (d + 1) ∣ H := by
    have hcomp_coeff : ∀ n ≤ d, (H.comp (Polynomial.X + 1)).coeff n = 0 := by
      intro n hn
      dsimp only [H]
      rw [Polynomial.sum_comp, coeff_finset_sum]
      have hsum : (∑ i : Fin (D + 1),
          ((Polynomial.C ((f i : ℚ) - (g i : ℚ)) * Polynomial.X ^ i.val).comp (Polynomial.X + 1)).coeff n) =
          (bin f n : ℚ) - (bin g n : ℚ) := by
        dsimp only [bin]
        push_cast
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
          Polynomial.coeff_C_mul]
        have hpow_coeff : ((Polynomial.X + 1 : Polynomial ℚ) ^ i.val).coeff n = (Nat.choose i.val n : ℚ) := by
          rw [add_pow, coeff_finset_sum]
          by_cases hni : n ≤ i.val
          · rw [Finset.sum_eq_single n]
            · simp [Polynomial.coeff_X_pow]
            · intro k _ hne
              simp [Polynomial.coeff_X_pow, Ne.symm hne]
            · intro hn_mem; exact absurd (Finset.mem_range.mpr (by omega)) hn_mem
          · rw [Nat.choose_eq_zero_of_lt (by omega : i.val < n), Nat.cast_zero]
            refine Finset.sum_eq_zero (fun k hk => ?_)
            have hkn : k ≠ n := by have := Finset.mem_range.mp hk; omega
            simp [Polynomial.coeff_X_pow, Ne.symm hkn]
        rw [hpow_coeff]
        ring
      rw [hsum, hbin_eq n hn, sub_self]
    have hX_dvd : (Polynomial.X : Polynomial ℚ) ^ (d + 1) ∣ H.comp (Polynomial.X + 1) := by
      rw [Polynomial.X_pow_dvd_iff]
      intro n hn
      exact hcomp_coeff n (by omega)
    rcases hX_dvd with ⟨U, hU⟩
    refine ⟨U.comp (Polynomial.X - 1), ?_⟩
    have hcomp := congrArg (fun p : Polynomial ℚ => p.comp (Polynomial.X - 1)) hU
    rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp] at hcomp
    have hcancel : (Polynomial.X + 1 : Polynomial ℚ).comp (Polynomial.X - 1) = Polynomial.X := by
      simp [Polynomial.add_comp]
    rw [hcancel, Polynomial.comp_X] at hcomp
    exact hcomp
  have hdvd_B : ∀ p ∈ primes, (phiPoly (q p)) ^ (depth p) ∣ H := by
    intro p hp
    rcases hpr p hp with ⟨hp_prime, hbp⟩
    have hq_pos : 0 < q p := pow_pos hp_prime.pos (b p)
    have hcop := isCoprime_phiPoly_deriv hq_pos
    have hne0 : phiPoly (q p) ≠ 0 := (phiPoly_monic hq_pos).ne_zero
    apply pow_dvd_of_iter_deriv_dvd hcop hne0 (depth p) H
    intro j hj
    rcases hdepth p hp j hj with ⟨hprec, hbound, hcut_le⟩
    have hres_eq : ∀ u < q p,
        (∑ i : Fin (D + 1), if (i.val - j) % q p = u then f i * Nat.choose i.val j else 0) =
        (∑ i : Fin (D + 1), if (i.val - j) % q p = u then g i * Nat.choose i.val j else 0) := by
      intro u hu
      rw [hpart1 f hfP p hp j hj u hu, hpart1 g hgP p hp j hj u hu]
      congr 1
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hn_le : j + n ≤ d := by
        have := Finset.mem_range.mp hn
        dsimp only [cut, q] at this
        omega
      rw [hbin_eq (j + n) hn_le]
    have hderiv_eq : Polynomial.derivative^[j] H =
        ∑ i : Fin (D + 1), Polynomial.C (((f i : ℚ) - (g i : ℚ)) * (Nat.descFactorial i.val j : ℚ)) *
          Polynomial.X ^ (i.val - j) := by
      dsimp only [H]
      rw [iter_deriv_linear]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [iter_deriv_X_pow, ← mul_assoc, ← map_mul]
    have hXq_dvd : (Polynomial.X ^ (q p) - 1 : Polynomial ℚ) ∣ Polynomial.derivative^[j] H := by
      apply X_pow_sub_one_dvd_of_residue_sum_zero hq_pos (Polynomial.derivative^[j] H)
      intro u hu
      have hdeg_le : (Polynomial.derivative^[j] H).natDegree ≤ D := by
        refine le_trans ?_ hH_deg
        have hiter : ∀ (t : ℕ) (Q : Polynomial ℚ), (Polynomial.derivative^[t] Q).natDegree ≤ Q.natDegree := by
          intro t
          induction t with
          | zero => intro Q; simp
          | succ t iht =>
            intro Q
            rw [Function.iterate_succ_apply']
            exact le_trans (Polynomial.natDegree_derivative_le _) (le_trans (Nat.sub_le _ _) (iht Q))
        exact hiter j H
      have hcoeff_zero : ∀ k > (Polynomial.derivative^[j] H).natDegree,
          (Polynomial.derivative^[j] H).coeff k = 0 :=
        fun k hk => Polynomial.coeff_eq_zero_of_natDegree_lt hk
      have hpad : (∑ k ∈ Finset.range ((Polynomial.derivative^[j] H).natDegree + 1),
          if k % q p = u then (Polynomial.derivative^[j] H).coeff k else 0) =
          ∑ k ∈ Finset.range (D + 1),
            if k % q p = u then (Polynomial.derivative^[j] H).coeff k else 0 := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) (fun k _ hkn => ?_)
        have hkgt : (Polynomial.derivative^[j] H).natDegree < k := by
          rw [Finset.mem_range] at hkn; omega
        rw [hcoeff_zero k hkgt, ite_self]
      rw [hpad]
      have hswap : (∑ k ∈ Finset.range (D + 1),
          if k % q p = u then (Polynomial.derivative^[j] H).coeff k else 0) =
          ∑ i : Fin (D + 1),
            if (i.val - j) % q p = u then ((f i : ℚ) - (g i : ℚ)) * (Nat.descFactorial i.val j : ℚ) else 0 := by
        have hcoeff_sum : ∀ k : ℕ, (Polynomial.derivative^[j] H).coeff k =
            ∑ i : Fin (D + 1), if k = i.val - j then
              ((f i : ℚ) - (g i : ℚ)) * (Nat.descFactorial i.val j : ℚ) else 0 := by
          intro k
          rw [hderiv_eq, coeff_finset_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
          split_ifs <;> simp
        calc (∑ k ∈ Finset.range (D + 1), if k % q p = u then (Polynomial.derivative^[j] H).coeff k else 0)
            = ∑ k ∈ Finset.range (D + 1), ∑ i : Fin (D + 1),
                if k % q p = u ∧ k = i.val - j then
                  ((f i : ℚ) - (g i : ℚ)) * (Nat.descFactorial i.val j : ℚ) else 0 := by
                  refine Finset.sum_congr rfl (fun k _ => ?_)
                  rw [hcoeff_sum k]
                  split_ifs with hku
                  · refine Finset.sum_congr rfl (fun i _ => by simp [hku])
                  · symm; refine Finset.sum_eq_zero (fun i _ => by simp [hku])
          _ = ∑ i : Fin (D + 1), ∑ k ∈ Finset.range (D + 1),
                if k % q p = u ∧ k = i.val - j then
                  ((f i : ℚ) - (g i : ℚ)) * (Nat.descFactorial i.val j : ℚ) else 0 := Finset.sum_comm
          _ = ∑ i : Fin (D + 1),
                if (i.val - j) % q p = u then ((f i : ℚ) - (g i : ℚ)) * (Nat.descFactorial i.val j : ℚ) else 0 := by
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  have hmem : i.val - j ∈ Finset.range (D + 1) :=
                    Finset.mem_range.mpr (by have := i.isLt; omega)
                  rw [Finset.sum_eq_single (i.val - j)]
                  · simp
                  · intro k _ hne; simp [hne]
                  · intro hnm; exact absurd hmem hnm
      rw [hswap]
      have hdesc_eq : ∀ i : Fin (D + 1), (Nat.descFactorial i.val j : ℚ) =
          (j.factorial : ℚ) * (Nat.choose i.val j : ℚ) := fun i => by
        exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose i.val j
      have hresQ : (∑ i : Fin (D + 1),
          if (i.val - j) % q p = u then (f i : ℚ) * (Nat.choose i.val j : ℚ) else 0) =
          ∑ i : Fin (D + 1),
            if (i.val - j) % q p = u then (g i : ℚ) * (Nat.choose i.val j : ℚ) else 0 := by
        have h := congrArg (fun x : ℕ => (x : ℚ)) (hres_eq u hu)
        push_cast at h
        have hl : (∑ i : Fin (D + 1), (if (i.val - j) % q p = u then f i * Nat.choose i.val j else 0 : ℚ)) =
            ∑ i : Fin (D + 1), if (i.val - j) % q p = u then (f i : ℚ) * (Nat.choose i.val j : ℚ) else 0 := by
          refine Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
        have hr : (∑ i : Fin (D + 1), (if (i.val - j) % q p = u then g i * Nat.choose i.val j else 0 : ℚ)) =
            ∑ i : Fin (D + 1), if (i.val - j) % q p = u then (g i : ℚ) * (Nat.choose i.val j : ℚ) else 0 := by
          refine Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
        simpa [hl, hr] using h
      calc (∑ i : Fin (D + 1),
            if (i.val - j) % q p = u then ((f i : ℚ) - (g i : ℚ)) * (Nat.descFactorial i.val j : ℚ) else 0)
          = (j.factorial : ℚ) *
              ((∑ i : Fin (D + 1), if (i.val - j) % q p = u then (f i : ℚ) * (Nat.choose i.val j : ℚ) else 0) -
               (∑ i : Fin (D + 1), if (i.val - j) % q p = u then (g i : ℚ) * (Nat.choose i.val j : ℚ) else 0)) := by
                rw [← Finset.sum_sub_distrib, Finset.mul_sum]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [hdesc_eq i]
                split_ifs <;> ring
        _ = 0 := by rw [hresQ, sub_self, mul_zero]
    have hphi_dvd_Xq : phiPoly (q p) ∣ (Polynomial.X ^ (q p) - 1) :=
      ⟨Polynomial.X - 1, by rw [mul_comm, X_sub_one_mul_phiPoly]⟩
    exact dvd_trans hphi_dvd_Xq hXq_dvd
  have hprod_B_dvd : (∏ p ∈ primes, (phiPoly (q p)) ^ (depth p)) ∣ H := by
    apply Finset.prod_dvd_of_coprime
    · intro p1 hp1 p2 hp2 hne
      rcases hpr p1 hp1 with ⟨hp1_pr, hb1⟩
      rcases hpr p2 hp2 with ⟨hp2_pr, hb2⟩
      have hq1_gt : 1 < q p1 := by
        have hp2 := hp1_pr.two_le
        calc 1 < p1 := by omega
          _ = p1 ^ 1 := (pow_one p1).symm
          _ ≤ p1 ^ (b p1) := Nat.pow_le_pow_right hp1_pr.pos hb1
      have hq2_gt : 1 < q p2 := by
        have hp2' := hp2_pr.two_le
        calc 1 < p2 := by omega
          _ = p2 ^ 1 := (pow_one p2).symm
          _ ≤ p2 ^ (b p2) := Nat.pow_le_pow_right hp2_pr.pos hb2
      have hcop_q : Nat.Coprime (q p1) (q p2) :=
        ((Nat.coprime_primes hp1_pr hp2_pr).mpr hne).pow (b p1) (b p2)
      exact ((isCoprime_phiPoly_of_coprime hq1_gt hq2_gt hcop_q).pow_left).pow_right
    · exact fun p hp => hdvd_B p hp
  have hcop_AB : IsCoprime ((Polynomial.X - 1 : Polynomial ℚ) ^ (d + 1))
      (∏ p ∈ primes, (phiPoly (q p)) ^ (depth p)) := by
    apply IsCoprime.prod_right
    intro p hp
    rcases hpr p hp with ⟨hp_pr, hbp⟩
    have hq_pos : 0 < q p := pow_pos hp_pr.pos (b p)
    exact ((isCoprime_X_sub_one_phiPoly hq_pos).pow_left).pow_right
  let Q : Polynomial ℚ :=
    (Polynomial.X - 1 : Polynomial ℚ) ^ (d + 1) * ∏ p ∈ primes, (phiPoly (q p)) ^ (depth p)
  have hQ_dvd : Q ∣ H := hcop_AB.mul_dvd hdvd_A hprod_B_dvd
  have hX1_monic : (Polynomial.X - 1 : Polynomial ℚ).Monic := by
    rw [← map_one Polynomial.C]; exact Polynomial.monic_X_sub_C (1 : ℚ)
  have hX1_deg : (Polynomial.X - 1 : Polynomial ℚ).natDegree = 1 := by
    rw [← map_one Polynomial.C]; exact Polynomial.natDegree_X_sub_C (1 : ℚ)
  have hA_monic : ((Polynomial.X - 1 : Polynomial ℚ) ^ (d + 1)).Monic :=
    hX1_monic.pow (d + 1)
  have hB_monic : ∀ p ∈ primes, ((phiPoly (q p)) ^ (depth p)).Monic := by
    intro p hp
    rcases hpr p hp with ⟨hp_pr, hbp⟩
    exact (phiPoly_monic (pow_pos hp_pr.pos (b p))).pow (depth p)
  have hprodB_monic : (∏ p ∈ primes, (phiPoly (q p)) ^ (depth p)).Monic :=
    Polynomial.monic_prod_of_monic _ _ hB_monic
  have hQ_deg : Q.natDegree = d + 1 + ∑ p ∈ primes, depth p * (q p - 1) := by
    dsimp only [Q]
    rw [Polynomial.Monic.natDegree_mul hA_monic hprodB_monic,
      Polynomial.Monic.natDegree_pow hX1_monic,
      hX1_deg, mul_one,
      Polynomial.natDegree_prod_of_monic _ _ hB_monic]
    congr 1
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rcases hpr p hp with ⟨hp_pr, hbp⟩
    have hq_pos : 0 < q p := pow_pos hp_pr.pos (b p)
    rw [Polynomial.Monic.natDegree_pow (phiPoly_monic hq_pos), phiPoly_natDegree hq_pos]
  have hH_zero : H = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd hQ_dvd hne
    rw [hQ_deg] at hle
    change D < d + 1 + ∑ p ∈ primes, depth p * (q p - 1) at hD
    omega
  funext i
  have hc := congrArg (fun P : Polynomial ℚ => P.coeff i.val) hH_zero
  rw [hH_coeff i.val, Polynomial.coeff_zero] at hc
  simp only [i.isLt, ↓reduceDIte] at hc
  have hQ : (f i : ℚ) = (g i : ℚ) := sub_eq_zero.mp hc
  exact_mod_cast hQ
