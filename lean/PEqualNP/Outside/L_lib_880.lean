import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_880

private lemma ceil_div_mul_ge (s D : ℕ) (hD : 0 < D) : s ≤ D * ((s + D - 1) / D) := by
  have h1 := Nat.div_add_mod (s + D - 1) D
  have h2 := Nat.mod_lt (s + D - 1) hD
  omega

private lemma ceil_div_le (s n D : ℕ) (hD : 0 < D) (hs : s ≤ n * D) : (s + D - 1) / D ≤ n := by
  have h1 := Nat.div_add_mod (s + D - 1) D
  by_contra h
  have hge : n + 1 ≤ (s + D - 1) / D := by omega
  have hmul : n * D + D ≤ D * ((s + D - 1) / D) := by nlinarith
  omega

private lemma exists_perm_ge (D s : ℕ) (hD : 0 < D) (f : Fin D → ℕ)
    (hsum : s ≤ ∑ u : Fin D, f u) : ∃ u : Fin D, (s + D - 1) / D ≤ f u := by
  by_contra hall
  push_neg at hall
  set m := (s + D - 1) / D
  by_cases hs0 : s = 0
  · subst hs0
    have hm0 : m = 0 := Nat.div_eq_of_lt (by omega)
    have h0 := hall ⟨0, hD⟩
    omega
  · have h1 : ∑ u : Fin D, (f u + 1) ≤ ∑ _u : Fin D, m :=
      Finset.sum_le_sum (fun u _ => hall u)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h1
    have h2 : D * m ≤ s + D - 1 := Nat.mul_div_le (s + D - 1) D
    omega

private lemma cost_tangent (d q v : ℕ) :
    (((q + 1) * (q + 1 - d) : ℕ) : ℤ) * ((v : ℤ) - (q : ℤ)) -
    ((q * (q - d) : ℕ) : ℤ) * ((v : ℤ) - (q : ℤ)) ≤
    ((v * (v - d) : ℕ) : ℤ) - ((q * (q - d) : ℕ) : ℤ) := by
  by_cases hq : q < d
  · have hq1 : q - d = 0 := Nat.sub_eq_zero_of_le (le_of_lt hq)
    have hq2 : q + 1 - d = 0 := Nat.sub_eq_zero_of_le hq
    rw [hq1, hq2]
    simp
    positivity
  · have hqd : d ≤ q := le_of_not_gt hq
    have hq1 : ((q - d : ℕ) : ℤ) = (q : ℤ) - (d : ℤ) := Int.ofNat_sub hqd
    have hq2 : ((q + 1 - d : ℕ) : ℤ) = (q : ℤ) + 1 - (d : ℤ) := by omega
    have hbase : ((v : ℤ) - (q : ℤ)) * ((v : ℤ) - (q : ℤ) - 1) ≥ 0 := by
      by_cases hvq : (v : ℤ) ≤ (q : ℤ)
      · nlinarith
      · nlinarith
    by_cases hv : v < d
    · have hv0 : v - d = 0 := Nat.sub_eq_zero_of_le (le_of_lt hv)
      rw [hv0]
      have hneg : (v : ℤ) * ((v : ℤ) - (d : ℤ)) ≤ 0 := by nlinarith
      push_cast
      rw [hq1, hq2]
      nlinarith
    · have hvd : d ≤ v := le_of_not_gt hv
      have hv1 : ((v - d : ℕ) : ℤ) = (v : ℤ) - (d : ℤ) := Int.ofNat_sub hvd
      push_cast
      rw [hq1, hq2, hv1]
      nlinarith

private lemma convex_cost_sum (t d m : ℕ) (ht : 0 < t) (a : Fin t → ℕ)
    (hsum : ∑ j : Fin t, a j = m) :
    (t - m % t) * ((m / t) * (m / t - d)) + (m % t) * ((m / t + 1) * (m / t + 1 - d)) ≤
      ∑ j : Fin t, a j * (a j - d) := by
  set q := m / t
  set rem := m % t
  have hrem_lt : rem < t := Nat.mod_lt m ht
  have hdiv : t * q + rem = m := by
    have := Nat.div_add_mod m t
    omega
  have hstep :
      ∑ j : Fin t, ((((q + 1) * (q + 1 - d) : ℕ) : ℤ) * ((a j : ℤ) - (q : ℤ)) -
        ((q * (q - d) : ℕ) : ℤ) * ((a j : ℤ) - (q : ℤ))) ≤
      ∑ j : Fin t, (((a j * (a j - d) : ℕ) : ℤ) - ((q * (q - d) : ℕ) : ℤ)) :=
    Finset.sum_le_sum (fun j _ => cost_tangent d q (a j))
  have hlhs :
      ∑ j : Fin t, ((((q + 1) * (q + 1 - d) : ℕ) : ℤ) * ((a j : ℤ) - (q : ℤ)) -
        ((q * (q - d) : ℕ) : ℤ) * ((a j : ℤ) - (q : ℤ))) =
      ((((q + 1) * (q + 1 - d) : ℕ) : ℤ) - ((q * (q - d) : ℕ) : ℤ)) * (rem : ℤ) := by
    have hfactor : ∀ j : Fin t,
        (((q + 1) * (q + 1 - d) : ℕ) : ℤ) * ((a j : ℤ) - (q : ℤ)) -
        ((q * (q - d) : ℕ) : ℤ) * ((a j : ℤ) - (q : ℤ)) =
        ((((q + 1) * (q + 1 - d) : ℕ) : ℤ) - ((q * (q - d) : ℕ) : ℤ)) * ((a j : ℤ) - (q : ℤ)) := by
      intro j; ring
    simp_rw [hfactor, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsumZ : ∑ j : Fin t, (a j : ℤ) = (m : ℤ) := by exact_mod_cast hsum
    rw [hsumZ]
    have hremZ : (m : ℤ) - (t : ℤ) * (q : ℤ) = (rem : ℤ) := by omega
    rw [hremZ]
  have hrhs :
      ∑ j : Fin t, (((a j * (a j - d) : ℕ) : ℤ) - ((q * (q - d) : ℕ) : ℤ)) =
      (∑ j : Fin t, ((a j * (a j - d) : ℕ) : ℤ)) - (t : ℤ) * ((q * (q - d) : ℕ) : ℤ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hlhs, hrhs] at hstep
  have hsub : ((t - rem : ℕ) : ℤ) = (t : ℤ) - (rem : ℤ) := Int.ofNat_sub (le_of_lt hrem_lt)
  have hZ : (((t - rem) * (q * (q - d)) + rem * ((q + 1) * (q + 1 - d)) : ℕ) : ℤ) ≤
      ((∑ j : Fin t, a j * (a j - d) : ℕ) : ℤ) := by
    push_cast at hstep ⊢
    rw [hsub]
    linarith
  exact_mod_cast hZ

private def sz (t m : ℕ) (j : Fin t) : ℕ :=
  if j.val < m % t then m / t + 1 else m / t

private def off (t m : ℕ) (i : ℕ) : ℕ :=
  if i ≤ m % t then i * (m / t + 1) else (m % t) * (m / t + 1) + (i - m % t) * (m / t)

private lemma off_zero (t m : ℕ) : off t m 0 = 0 := by
  simp [off]

private lemma off_succ (t m : ℕ) (j : Fin t) :
    off t m (j.val + 1) = off t m j.val + sz t m j := by
  unfold off sz
  by_cases h1 : j.val < m % t
  · have h2 : j.val ≤ m % t := le_of_lt h1
    have h3 : j.val + 1 ≤ m % t := h1
    simp only [h1, h2, h3, ite_true]
    ring
  · by_cases h2 : j.val ≤ m % t
    · have heq : j.val = m % t := by omega
      have h3 : ¬ j.val + 1 ≤ m % t := by omega
      simp only [h1, h2, h3, ite_true, ite_false, heq]
      simp
    · have h3 : ¬ j.val + 1 ≤ m % t := by omega
      simp only [h1, h2, h3, ite_false]
      have hsub : j.val + 1 - m % t = (j.val - m % t) + 1 := by omega
      rw [hsub]
      ring

private lemma off_end (t m : ℕ) (ht : 0 < t) : off t m t = m := by
  unfold off
  have hrem : m % t < t := Nat.mod_lt m ht
  have hnot : ¬ t ≤ m % t := by omega
  simp only [hnot, ite_false]
  have hdiv := Nat.div_add_mod m t
  have hle : m % t ≤ t := le_of_lt hrem
  zify [hle]
  linarith

private lemma off_mono (t m : ℕ) {i₁ i₂ : ℕ} (h : i₁ ≤ i₂) : off t m i₁ ≤ off t m i₂ := by
  unfold off
  by_cases h1 : i₁ ≤ m % t
  · by_cases h2 : i₂ ≤ m % t
    · simp only [h1, h2, ite_true]
      exact Nat.mul_le_mul_right _ h
    · simp only [h1, h2, ite_true, ite_false]
      have h12 : i₁ * (m / t + 1) ≤ (m % t) * (m / t + 1) := Nat.mul_le_mul_right _ h1
      omega
  · have h2 : ¬ i₂ ≤ m % t := by omega
    simp only [h1, h2, ite_false]
    have hsub : i₁ - m % t ≤ i₂ - m % t := Nat.sub_le_sub_right h _
    have hmul : (i₁ - m % t) * (m / t) ≤ (i₂ - m % t) * (m / t) := Nat.mul_le_mul_right _ hsub
    omega

private def blkIdx (t m : ℕ) (ht : 0 < t) (x : ℕ) (hx : x < m) : Fin t :=
  if h : x < (m % t) * (m / t + 1) then
    ⟨x / (m / t + 1), by
      have h1 : x / (m / t + 1) < m % t := by
        rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
        exact h
      exact lt_trans h1 (Nat.mod_lt m ht)⟩
  else
    ⟨m % t + (x - (m % t) * (m / t + 1)) / (m / t), by
      have hrem : m % t < t := Nat.mod_lt m ht
      have hqpos : 0 < m / t := by
        by_contra hq0
        have hqeq : m / t = 0 := Nat.eq_zero_of_not_pos hq0
        have hdiv := Nat.div_add_mod m t
        simp only [hqeq, mul_zero, zero_add, mul_one] at hdiv h
        omega
      have hdiff : x - (m % t) * (m / t + 1) < (t - m % t) * (m / t) := by
        have hdiv := Nat.div_add_mod m t
        have hle : m % t ≤ t := le_of_lt hrem
        zify [hle] at hdiv ⊢
        have hge : (m % t) * (m / t + 1) ≤ x := le_of_not_gt h
        zify [hge]
        linarith
      have hdiv_lt : (x - (m % t) * (m / t + 1)) / (m / t) < t - m % t := by
        rw [Nat.div_lt_iff_lt_mul hqpos]
        exact hdiff
      omega⟩

private lemma blkIdx_mem (t m : ℕ) (ht : 0 < t) (x : ℕ) (hx : x < m) :
    off t m (blkIdx t m ht x hx).val ≤ x ∧ x < off t m ((blkIdx t m ht x hx).val + 1) := by
  unfold blkIdx
  split_ifs with h
  · dsimp only
    set j := x / (m / t + 1)
    have hjlt : j < m % t := by
      rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
      exact h
    have hoff1 : off t m j = j * (m / t + 1) := by
      unfold off; simp only [le_of_lt hjlt, ite_true]
    have hoff2 : off t m (j + 1) = (j + 1) * (m / t + 1) := by
      unfold off
      have hj1 : j + 1 ≤ m % t := hjlt
      simp only [hj1, ite_true]
    rw [hoff1, hoff2]
    have hdm : (m / t + 1) * j + x % (m / t + 1) = x := Nat.div_add_mod x (m / t + 1)
    rw [Nat.mul_comm] at hdm
    have hmlt : x % (m / t + 1) < m / t + 1 := Nat.mod_lt x (Nat.succ_pos (m / t))
    have hexp : (j + 1) * (m / t + 1) = j * (m / t + 1) + (m / t + 1) := by ring
    constructor <;> omega
  · dsimp only
    have hrem : m % t < t := Nat.mod_lt m ht
    have hge : (m % t) * (m / t + 1) ≤ x := le_of_not_gt h
    have hqpos : 0 < m / t := by
      by_contra hq0
      have hqeq : m / t = 0 := Nat.eq_zero_of_not_pos hq0
      have hdiv := Nat.div_add_mod m t
      simp only [hqeq, mul_zero, zero_add, mul_one] at hdiv hge
      omega
    set y := x - (m % t) * (m / t + 1)
    set k := y / (m / t)
    have hoff1 : off t m (m % t + k) = (m % t) * (m / t + 1) + k * (m / t) := by
      unfold off
      by_cases hk : k = 0
      · rw [hk]; simp
      · have hnot : ¬ m % t + k ≤ m % t := Nat.not_le.mpr (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hk))
        simp only [hnot, ite_false, Nat.add_sub_cancel_left]
    have hoff2 : off t m (m % t + k + 1) = (m % t) * (m / t + 1) + (k + 1) * (m / t) := by
      unfold off
      have hnot : ¬ m % t + k + 1 ≤ m % t := by
        rw [Nat.add_assoc]
        exact Nat.not_le.mpr (Nat.lt_add_of_pos_right (Nat.succ_pos k))
      simp only [hnot, ite_false]
      have hsub : m % t + k + 1 - m % t = k + 1 := by
        rw [Nat.add_assoc, Nat.add_sub_cancel_left]
      rw [hsub]
    rw [hoff1, hoff2]
    have hdm : (m / t) * k + y % (m / t) = y := Nat.div_add_mod y (m / t)
    rw [Nat.mul_comm] at hdm
    have hmlt : y % (m / t) < m / t := Nat.mod_lt y hqpos
    have hydef : x = (m % t) * (m / t + 1) + y := by omega
    have hexp : (k + 1) * (m / t) = k * (m / t) + m / t := by ring
    constructor <;> omega

private lemma blkIdx_unique (t m : ℕ) (ht : 0 < t) {x : ℕ} (hx : x < m) {j : Fin t}
    (h1 : off t m j.val ≤ x) (h2 : x < off t m (j.val + 1)) :
    j = blkIdx t m ht x hx := by
  have hb := blkIdx_mem t m ht x hx
  set j₀ := blkIdx t m ht x hx
  ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle := off_mono t m (show j.val + 1 ≤ j₀.val by omega)
    omega
  · have hle := off_mono t m (show j₀.val + 1 ≤ j.val by omega)
    omega

private lemma blk_card (n t m : ℕ) (ht : 0 < t) (hmn : m ≤ n) (j : Fin t) :
    (Finset.univ.filter (fun x : Fin n => off t m j.val ≤ x.val ∧ x.val < off t m (j.val + 1))).card =
      sz t m j := by
  have hend : off t m (j.val + 1) ≤ n :=
    (off_mono t m j.isLt).trans ((off_end t m ht).le.trans hmn)
  have hsucc := off_succ t m j
  set B := Finset.univ.filter (fun x : Fin n => off t m j.val ≤ x.val ∧ x.val < off t m (j.val + 1))
  have hbij : Finset.card B = Finset.card (Finset.univ : Finset (Fin (sz t m j))) := by
    refine Finset.card_bij (fun x hx => ⟨x.val - off t m j.val, by
        have hm := (Finset.mem_filter.mp hx).2
        omega⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ hx₁ x₂ hx₂ heq => by
        have h1 := (Finset.mem_filter.mp hx₁).2
        have h2 := (Finset.mem_filter.mp hx₂).2
        have hval : x₁.val - off t m j.val = x₂.val - off t m j.val := congrArg Fin.val heq
        ext; omega)
      (fun k _ => by
        refine ⟨⟨off t m j.val + k.val, by omega⟩, ?_, ?_⟩
        · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · ext; dsimp only; omega)
  rw [hbij, Finset.card_univ, Fintype.card_fin]

private def shiftAmt (t m d D : ℕ) (j : Fin t) (u : Fin D) : ℕ :=
  if u.val < min (sz t m j) d then u.val else 0

private def permFun (n t m d D : ℕ) (ht : 0 < t) (hmn : m ≤ n) (u : Fin D) (x : Fin n) : Fin n :=
  if hx : x.val < m then
    let j := blkIdx t m ht x.val hx
    ⟨off t m j.val + (x.val - off t m j.val + shiftAmt t m d D j u) % sz t m j, by
      have hsucc := off_succ t m j
      have hb : off t m j.val ≤ x.val ∧ x.val < off t m (j.val + 1) := blkIdx_mem t m ht x.val hx
      have hszpos : 0 < sz t m j := by omega
      have hmod := Nat.mod_lt (x.val - off t m j.val + shiftAmt t m d D j u) hszpos
      have hend : off t m (j.val + 1) ≤ n :=
        (off_mono t m j.isLt).trans ((off_end t m ht).le.trans hmn)
      omega⟩
  else
    x

private def permInv (n t m d D : ℕ) (ht : 0 < t) (hmn : m ≤ n) (u : Fin D) (x : Fin n) : Fin n :=
  if hx : x.val < m then
    let j := blkIdx t m ht x.val hx
    ⟨off t m j.val + (x.val - off t m j.val + (sz t m j - shiftAmt t m d D j u)) % sz t m j, by
      have hsucc := off_succ t m j
      have hb : off t m j.val ≤ x.val ∧ x.val < off t m (j.val + 1) := blkIdx_mem t m ht x.val hx
      have hszpos : 0 < sz t m j := by omega
      have hmod := Nat.mod_lt (x.val - off t m j.val + (sz t m j - shiftAmt t m d D j u)) hszpos
      have hend : off t m (j.val + 1) ≤ n :=
        (off_mono t m j.isLt).trans ((off_end t m ht).le.trans hmn)
      omega⟩
  else
    x

private lemma shiftAmt_lt_sz (t m d D : ℕ) (j : Fin t) (u : Fin D) (hpos : 0 < sz t m j) :
    shiftAmt t m d D j u < sz t m j := by
  unfold shiftAmt
  split_ifs with h
  · exact lt_of_lt_of_le h (min_le_left _ _)
  · exact hpos

private lemma permFun_blk (n t m d D : ℕ) (ht : 0 < t) (hmn : m ≤ n) (u : Fin D) (x : Fin n)
    (j : Fin t) (h1 : off t m j.val ≤ x.val) (h2 : x.val < off t m (j.val + 1)) :
    (permFun n t m d D ht hmn u x).val =
      off t m j.val + (x.val - off t m j.val + shiftAmt t m d D j u) % sz t m j := by
  have hx : x.val < m := lt_of_lt_of_le h2 ((off_mono t m j.isLt).trans (off_end t m ht).le)
  unfold permFun
  rw [dif_pos hx]
  dsimp only
  have huniq : j = blkIdx t m ht x.val hx := blkIdx_unique t m ht hx h1 h2
  rw [← huniq]

private lemma permInv_blk (n t m d D : ℕ) (ht : 0 < t) (hmn : m ≤ n) (u : Fin D) (x : Fin n)
    (j : Fin t) (h1 : off t m j.val ≤ x.val) (h2 : x.val < off t m (j.val + 1)) :
    (permInv n t m d D ht hmn u x).val =
      off t m j.val + (x.val - off t m j.val + (sz t m j - shiftAmt t m d D j u)) % sz t m j := by
  have hx : x.val < m := lt_of_lt_of_le h2 ((off_mono t m j.isLt).trans (off_end t m ht).le)
  unfold permInv
  rw [dif_pos hx]
  dsimp only
  have huniq : j = blkIdx t m ht x.val hx := blkIdx_unique t m ht hx h1 h2
  rw [← huniq]

private def mkPerm (n t m d D : ℕ) (ht : 0 < t) (hmn : m ≤ n) (u : Fin D) : Equiv.Perm (Fin n) where
  toFun := permFun n t m d D ht hmn u
  invFun := permInv n t m d D ht hmn u
  left_inv x := by
    by_cases hx : x.val < m
    · set j := blkIdx t m ht x.val hx
      have hb : off t m j.val ≤ x.val ∧ x.val < off t m (j.val + 1) := blkIdx_mem t m ht x.val hx
      have hsucc := off_succ t m j
      have hszpos : 0 < sz t m j := by omega
      have hsh : shiftAmt t m d D j u < sz t m j := shiftAmt_lt_sz t m d D j u hszpos
      have hy := permFun_blk n t m d D ht hmn u x j hb.1 hb.2
      have hmod := Nat.mod_lt (x.val - off t m j.val + shiftAmt t m d D j u) hszpos
      have hy1 : off t m j.val ≤ (permFun n t m d D ht hmn u x).val := by omega
      have hy2 : (permFun n t m d D ht hmn u x).val < off t m (j.val + 1) := by omega
      have hz := permInv_blk n t m d D ht hmn u (permFun n t m d D ht hmn u x) j hy1 hy2
      ext
      rw [hz, hy, Nat.add_sub_cancel_left]
      have hadd : ((x.val - off t m j.val + shiftAmt t m d D j u) % sz t m j +
          (sz t m j - shiftAmt t m d D j u)) % sz t m j =
          x.val - off t m j.val := by
        rw [Nat.mod_add_mod]
        have hrew : x.val - off t m j.val + shiftAmt t m d D j u +
            (sz t m j - shiftAmt t m d D j u) =
            (x.val - off t m j.val) + sz t m j := by omega
        rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hadd]
      omega
    · unfold permInv permFun
      rw [dif_neg hx, dif_neg hx]
  right_inv x := by
    by_cases hx : x.val < m
    · set j := blkIdx t m ht x.val hx
      have hb : off t m j.val ≤ x.val ∧ x.val < off t m (j.val + 1) := blkIdx_mem t m ht x.val hx
      have hsucc := off_succ t m j
      have hszpos : 0 < sz t m j := by omega
      have hsh : shiftAmt t m d D j u < sz t m j := shiftAmt_lt_sz t m d D j u hszpos
      have hy := permInv_blk n t m d D ht hmn u x j hb.1 hb.2
      have hmod := Nat.mod_lt (x.val - off t m j.val + (sz t m j - shiftAmt t m d D j u)) hszpos
      have hy1 : off t m j.val ≤ (permInv n t m d D ht hmn u x).val := by omega
      have hy2 : (permInv n t m d D ht hmn u x).val < off t m (j.val + 1) := by omega
      have hz := permFun_blk n t m d D ht hmn u (permInv n t m d D ht hmn u x) j hy1 hy2
      ext
      rw [hz, hy, Nat.add_sub_cancel_left]
      have hadd : ((x.val - off t m j.val + (sz t m j - shiftAmt t m d D j u)) % sz t m j +
          shiftAmt t m d D j u) % sz t m j =
          x.val - off t m j.val := by
        rw [Nat.mod_add_mod]
        have hrew : x.val - off t m j.val + (sz t m j - shiftAmt t m d D j u) +
            shiftAmt t m d D j u =
            (x.val - off t m j.val) + sz t m j := by omega
        rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hadd]
      omega
    · unfold permFun permInv
      rw [dif_neg hx, dif_neg hx]

private lemma mkPerm_image_card_in_blk (n t m d D : ℕ) (ht : 0 < t) (hd : 0 < d) (hdD : d ≤ D)
    (hmn : m ≤ n) (j : Fin t) (x : Fin n)
    (h1 : off t m j.val ≤ x.val) (h2 : x.val < off t m (j.val + 1)) :
    (Finset.univ.image (fun u : Fin D => mkPerm n t m d D ht hmn u x)).card =
      min (sz t m j) d := by
  have hsucc := off_succ t m j
  have hszpos : 0 < sz t m j := by omega
  have hmin_pos : 0 < min (sz t m j) d := lt_min hszpos hd
  have hmin_le_D : min (sz t m j) d ≤ D := (min_le_right _ _).trans hdD
  have hmin_le_sz : min (sz t m j) d ≤ sz t m j := min_le_left _ _
  set img := Finset.univ.image (fun u : Fin D => mkPerm n t m d D ht hmn u x)
  set F : Fin (min (sz t m j) d) → Fin n := fun r =>
    mkPerm n t m d D ht hmn ⟨r.val, lt_of_lt_of_le r.isLt hmin_le_D⟩ x
  have himg_eq : img = Finset.univ.image F := by
    ext y
    simp only [img, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩
      by_cases hu : u.val < min (sz t m j) d
      · exact ⟨⟨u.val, hu⟩, rfl⟩
      · refine ⟨⟨0, hmin_pos⟩, ?_⟩
        ext
        change (permFun n t m d D ht hmn ⟨0, lt_of_lt_of_le hmin_pos hmin_le_D⟩ x).val =
          (permFun n t m d D ht hmn u x).val
        rw [permFun_blk n t m d D ht hmn _ x j h1 h2, permFun_blk n t m d D ht hmn _ x j h1 h2]
        unfold shiftAmt
        simp only [hmin_pos, hu, ite_true, ite_false]
    · rintro ⟨r, rfl⟩
      exact ⟨⟨r.val, lt_of_lt_of_le r.isLt hmin_le_D⟩, rfl⟩
  rw [himg_eq, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro r₁ r₂ heq
    have hval : (permFun n t m d D ht hmn ⟨r₁.val, lt_of_lt_of_le r₁.isLt hmin_le_D⟩ x).val =
        (permFun n t m d D ht hmn ⟨r₂.val, lt_of_lt_of_le r₂.isLt hmin_le_D⟩ x).val :=
      congrArg Fin.val heq
    rw [permFun_blk n t m d D ht hmn _ x j h1 h2, permFun_blk n t m d D ht hmn _ x j h1 h2] at hval
    have hsh1 : shiftAmt t m d D j ⟨r₁.val, lt_of_lt_of_le r₁.isLt hmin_le_D⟩ = r₁.val := by
      unfold shiftAmt; simp only [r₁.isLt, ite_true]
    have hsh2 : shiftAmt t m d D j ⟨r₂.val, lt_of_lt_of_le r₂.isLt hmin_le_D⟩ = r₂.val := by
      unfold shiftAmt; simp only [r₂.isLt, ite_true]
    rw [hsh1, hsh2] at hval
    have hmod_eq : (x.val - off t m j.val + r₁.val) % sz t m j =
        (x.val - off t m j.val + r₂.val) % sz t m j := by omega
    have hr1 : r₁.val < sz t m j := lt_of_lt_of_le r₁.isLt hmin_le_sz
    have hr2 : r₂.val < sz t m j := lt_of_lt_of_le r₂.isLt hmin_le_sz
    have hk : x.val - off t m j.val < sz t m j := by omega
    ext
    have hmod_inv : ∀ r < sz t m j,
        ((x.val - off t m j.val + r) % sz t m j + (sz t m j - (x.val - off t m j.val))) % sz t m j = r := by
      intro r hr
      rw [Nat.mod_add_mod]
      have hrew : x.val - off t m j.val + r + (sz t m j - (x.val - off t m j.val)) = r + sz t m j := by omega
      rw [hrew, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
    have e1 := hmod_inv r₁.val hr1
    have e2 := hmod_inv r₂.val hr2
    rw [hmod_eq] at e1
    omega

end PEqualNP.Outside.L_lib_880

theorem PEqualNP.Outside.L_lib_880 :
    ∀ n t D d s : ℕ, 0 < t → 0 < d → d ≤ D → s ≤ n*D →
      let X := Fin n
      let stats := fun (p : Fin D → Equiv.Perm X) (A B : Fin t → Finset X) =>
        let covered := fun (x y : X) => ∃ j : Fin t, x ∈ A j ∧ y ∈ B j
        let hits := ∑ u : Fin D, (Finset.univ.filter (fun x : X => covered x (p u x))).card
        let holes := (Finset.univ.filter (fun xy : X × X =>
          covered xy.1 xy.2 ∧ ∀ u : Fin D, p u xy.1 ≠ xy.2)).card
        (hits, holes)
      let cap := fun (p : Fin D → Equiv.Perm X) =>
        ∀ x : X, (Finset.univ.image (fun u : Fin D => p u x)).card ≤ d
      let m := (s+D-1)/D
      let q := m/t
      let rem := m % t
      let cost := fun (v : ℕ) => v*(v-d)
      let best := (t-rem)*cost q + rem*cost (q+1)
      (∀ (p : Fin D → Equiv.Perm X) (A B : Fin t → Finset X),
        cap p → s ≤ (stats p A B).1 → best ≤ (stats p A B).2) ∧
      ∃ (p : Fin D → Equiv.Perm X) (A B : Fin t → Finset X),
        cap p ∧ s ≤ (stats p A B).1 ∧ (stats p A B).2 = best := by
  intro n t D d s ht hd hdD hs
  dsimp only
  have hD : 0 < D := lt_of_lt_of_le hd hdD
  set m := (s + D - 1) / D
  set q := m / t
  set rem := m % t
  have hmn : m ≤ n := PEqualNP.Outside.L_lib_880.ceil_div_le s n D hD hs
  constructor
  · intro p A B hcap hhits
    set covered : Fin n → Fin n → Prop := fun x y => ∃ j : Fin t, x ∈ A j ∧ y ∈ B j
    have hex_u : ∃ u : Fin D,
        m ≤ (Finset.univ.filter (fun x : Fin n => covered x (p u x))).card :=
      PEqualNP.Outside.L_lib_880.exists_perm_ge D s hD
        (fun u => (Finset.univ.filter (fun x : Fin n => covered x (p u x))).card) hhits
    rcases hex_u with ⟨u₀, hu₀⟩
    set Sfull := Finset.univ.filter (fun x : Fin n => covered x (p u₀ x))
    rcases Finset.exists_subset_card_eq hu₀ with ⟨S, hSsub, hScard⟩
    have hScov : ∀ x ∈ S, ∃ j : Fin t, x ∈ A j ∧ p u₀ x ∈ B j := fun x hx =>
      (Finset.mem_filter.mp (hSsub hx)).2
    let cls : Fin n → Fin t := fun x =>
      if hx : x ∈ S then Classical.choose (hScov x hx) else ⟨0, ht⟩
    have hcls : ∀ x ∈ S, x ∈ A (cls x) ∧ p u₀ x ∈ B (cls x) := by
      intro x hx
      have heq : cls x = Classical.choose (hScov x hx) := dif_pos hx
      rw [heq]
      exact Classical.choose_spec (hScov x hx)
    set C : Fin t → Finset (Fin n) := fun j => S.filter (fun x => cls x = j)
    have hCdisj : ∀ j₁ j₂ : Fin t, j₁ ≠ j₂ → Disjoint (C j₁) (C j₂) := by
      intro j₁ j₂ hne
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := (Finset.mem_filter.mp hx1).2
      have h2 := (Finset.mem_filter.mp hx2).2
      exact hne (h1.symm.trans h2)
    have hCsum : ∑ j : Fin t, (C j).card = m := by
      rw [← hScard]
      have hbi : Finset.univ.biUnion C = S := by
        ext x
        simp only [C, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
        exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨cls x, hx, rfl⟩⟩
      rw [← hbi, Finset.card_biUnion]
      intro j₁ _ j₂ _ hne
      exact hCdisj j₁ j₂ hne
    set H := Finset.univ.filter (fun xy : Fin n × Fin n =>
      covered xy.1 xy.2 ∧ ∀ u : Fin D, p u xy.1 ≠ xy.2)
    set R : Fin t → Finset (Fin n × Fin n) := fun j =>
      ((C j) ×ˢ ((C j).image (p u₀))) ∩ H
    have hRsub : Finset.univ.biUnion R ⊆ H := by
      intro xy hxy
      rcases Finset.mem_biUnion.mp hxy with ⟨j, _, hmem⟩
      exact (Finset.mem_inter.mp hmem).2
    have hRdisj : ∀ j₁ ∈ (Finset.univ : Finset (Fin t)), ∀ j₂ ∈ (Finset.univ : Finset (Fin t)),
        j₁ ≠ j₂ → Disjoint (R j₁) (R j₂) := by
      intro j₁ _ j₂ _ hne
      rw [Finset.disjoint_left]
      intro xy h1 h2
      have hx1 : xy.1 ∈ C j₁ := (Finset.mem_product.mp (Finset.mem_inter.mp h1).1).1
      have hx2 : xy.1 ∈ C j₂ := (Finset.mem_product.mp (Finset.mem_inter.mp h2).1).1
      exact Finset.disjoint_left.mp (hCdisj j₁ j₂ hne) hx1 hx2
    have hRcard : ∀ j : Fin t, (C j).card * ((C j).card - d) ≤ (R j).card := by
      intro j
      set Y := (C j).image (p u₀)
      have hYcard : Y.card = (C j).card := Finset.card_image_of_injective (C j) (p u₀).injective
      set fiber : Fin n → Finset (Fin n × Fin n) := fun x =>
        (Y \ Finset.univ.image (fun u : Fin D => p u x)).image (fun y => (x, y))
      have hfsub : (C j).biUnion fiber ⊆ R j := by
        intro xy hxy
        rcases Finset.mem_biUnion.mp hxy with ⟨x, hx, hfx⟩
        rcases Finset.mem_image.mp hfx with ⟨y, hy, rfl⟩
        have hyY : y ∈ Y := (Finset.mem_sdiff.mp hy).1
        have hyBad : y ∉ Finset.univ.image (fun u : Fin D => p u x) := (Finset.mem_sdiff.mp hy).2
        rw [Finset.mem_inter, Finset.mem_product]
        refine ⟨⟨hx, hyY⟩, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · rcases Finset.mem_image.mp hyY with ⟨x', hx', rfl⟩
          have h1 := Finset.mem_filter.mp hx
          have h2 := Finset.mem_filter.mp hx'
          refine ⟨j, ?_, ?_⟩
          · rw [← h1.2]; exact (hcls x h1.1).1
          · rw [← h2.2]; exact (hcls x' h2.1).2
        · intro u heq
          exact hyBad (Finset.mem_image.mpr ⟨u, Finset.mem_univ u, heq⟩)
      have hfdisj : ∀ x₁ ∈ C j, ∀ x₂ ∈ C j, x₁ ≠ x₂ → Disjoint (fiber x₁) (fiber x₂) := by
        intro x₁ _ x₂ _ hne
        rw [Finset.disjoint_left]
        intro xy h1 h2
        rcases Finset.mem_image.mp h1 with ⟨y₁, _, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨y₂, _, heq⟩
        exact hne (congrArg Prod.fst heq).symm
      have hfcard : ∀ x ∈ C j, (C j).card - d ≤ (fiber x).card := by
        intro x _
        have hinj : Function.Injective (fun y : Fin n => (x, y)) := fun _ _ h => congrArg Prod.snd h
        rw [Finset.card_image_of_injective _ hinj]
        have hsdiff := Finset.le_card_sdiff (Finset.univ.image (fun u : Fin D => p u x)) Y
        have hc := hcap x
        omega
      calc (C j).card * ((C j).card - d)
          = ∑ _x ∈ C j, ((C j).card - d) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ C j, (fiber x).card := Finset.sum_le_sum hfcard
        _ = ((C j).biUnion fiber).card := (Finset.card_biUnion hfdisj).symm
        _ ≤ (R j).card := Finset.card_le_card hfsub
    have hconv := PEqualNP.Outside.L_lib_880.convex_cost_sum t d m ht (fun j => (C j).card) hCsum
    calc (t - rem) * (q * (q - d)) + rem * ((q + 1) * (q + 1 - d))
        ≤ ∑ j : Fin t, (C j).card * ((C j).card - d) := hconv
      _ ≤ ∑ j : Fin t, (R j).card := Finset.sum_le_sum (fun j _ => hRcard j)
      _ = (Finset.univ.biUnion R).card := (Finset.card_biUnion hRdisj).symm
      _ ≤ H.card := Finset.card_le_card hRsub
  · set blk : Fin t → Finset (Fin n) := fun j =>
      Finset.univ.filter (fun x : Fin n =>
        PEqualNP.Outside.L_lib_880.off t m j.val ≤ x.val ∧
        x.val < PEqualNP.Outside.L_lib_880.off t m (j.val + 1))
    set p : Fin D → Equiv.Perm (Fin n) := fun u =>
      PEqualNP.Outside.L_lib_880.mkPerm n t m d D ht hmn u
    refine ⟨p, blk, blk, ?_, ?_, ?_⟩
    · intro x
      by_cases hx : x.val < m
      · set j := PEqualNP.Outside.L_lib_880.blkIdx t m ht x.val hx
        have hb := PEqualNP.Outside.L_lib_880.blkIdx_mem t m ht x.val hx
        rw [PEqualNP.Outside.L_lib_880.mkPerm_image_card_in_blk n t m d D ht hd hdD hmn j x hb.1 hb.2]
        exact min_le_right _ _
      · have himg : Finset.univ.image (fun u : Fin D => p u x) ⊆ {x} := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨u, _, rfl⟩
          rw [Finset.mem_singleton]
          change PEqualNP.Outside.L_lib_880.permFun n t m d D ht hmn u x = x
          unfold PEqualNP.Outside.L_lib_880.permFun
          rw [dif_neg hx]
        calc (Finset.univ.image (fun u : Fin D => p u x)).card
            ≤ ({x} : Finset (Fin n)).card := Finset.card_le_card himg
          _ = 1 := Finset.card_singleton x
          _ ≤ d := hd
    · have hu_ge : ∀ u : Fin D,
          m ≤ (Finset.univ.filter (fun x : Fin n => ∃ j : Fin t, x ∈ blk j ∧ p u x ∈ blk j)).card := by
        intro u
        set pre := Finset.univ.filter (fun x : Fin n => x.val < m)
        have hpre_card : pre.card = m := by
          have hbij : pre.card = (Finset.univ : Finset (Fin m)).card := by
            refine Finset.card_bij (fun x hx => ⟨x.val, (Finset.mem_filter.mp hx).2⟩)
              (fun _ _ => Finset.mem_univ _)
              (fun x₁ _ x₂ _ heq => Fin.ext (Fin.mk.inj heq))
              (fun k _ => ⟨⟨k.val, lt_of_lt_of_le k.isLt hmn⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩)
          rw [hbij, Finset.card_univ, Fintype.card_fin]
        rw [← hpre_card]
        refine Finset.card_le_card ?_
        intro x hx
        have hxlt : x.val < m := (Finset.mem_filter.mp hx).2
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        set j := PEqualNP.Outside.L_lib_880.blkIdx t m ht x.val hxlt
        have hb : PEqualNP.Outside.L_lib_880.off t m j.val ≤ x.val ∧
            x.val < PEqualNP.Outside.L_lib_880.off t m (j.val + 1) :=
          PEqualNP.Outside.L_lib_880.blkIdx_mem t m ht x.val hxlt
        refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hval := PEqualNP.Outside.L_lib_880.permFun_blk n t m d D ht hmn u x j hb.1 hb.2
        have hsucc := PEqualNP.Outside.L_lib_880.off_succ t m j
        have hszpos : 0 < PEqualNP.Outside.L_lib_880.sz t m j := by omega
        have hmod := Nat.mod_lt (x.val - PEqualNP.Outside.L_lib_880.off t m j.val +
          PEqualNP.Outside.L_lib_880.shiftAmt t m d D j u) hszpos
        change PEqualNP.Outside.L_lib_880.off t m j.val ≤ (PEqualNP.Outside.L_lib_880.permFun n t m d D ht hmn u x).val ∧
          (PEqualNP.Outside.L_lib_880.permFun n t m d D ht hmn u x).val < PEqualNP.Outside.L_lib_880.off t m (j.val + 1)
        omega
      calc s ≤ D * m := PEqualNP.Outside.L_lib_880.ceil_div_mul_ge s D hD
        _ = ∑ _u : Fin D, m := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ ∑ u : Fin D, (Finset.univ.filter (fun x : Fin n => ∃ j : Fin t, x ∈ blk j ∧ p u x ∈ blk j)).card :=
            Finset.sum_le_sum (fun u _ => hu_ge u)
    · set H := Finset.univ.filter (fun xy : Fin n × Fin n =>
        (∃ j : Fin t, xy.1 ∈ blk j ∧ xy.2 ∈ blk j) ∧ ∀ u : Fin D, p u xy.1 ≠ xy.2)
      set Hj : Fin t → Finset (Fin n × Fin n) := fun j =>
        (blk j).biUnion (fun x =>
          (blk j \ Finset.univ.image (fun u : Fin D => p u x)).image (fun y => (x, y)))
      have hblk_disj : ∀ j₁ j₂ : Fin t, j₁ ≠ j₂ → Disjoint (blk j₁) (blk j₂) := by
        intro j₁ j₂ hne
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have h1 := (Finset.mem_filter.mp hx1).2
        have h2 := (Finset.mem_filter.mp hx2).2
        have hxlt : x.val < m := lt_of_lt_of_le h1.2
          ((PEqualNP.Outside.L_lib_880.off_mono t m j₁.isLt).trans
            (PEqualNP.Outside.L_lib_880.off_end t m ht).le)
        have e1 := PEqualNP.Outside.L_lib_880.blkIdx_unique t m ht hxlt h1.1 h1.2
        have e2 := PEqualNP.Outside.L_lib_880.blkIdx_unique t m ht hxlt h2.1 h2.2
        exact hne (e1.trans e2.symm)
      have hHeq : H = Finset.univ.biUnion Hj := by
        ext ⟨x, y⟩
        simp only [H, Hj, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_image, Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨j, hx, hy⟩, hne⟩
          refine ⟨j, x, hx, y, ⟨hy, ?_⟩, rfl⟩
          intro himg
          rcases himg with ⟨u, hu⟩
          exact hne u hu
        · rintro ⟨j, x', hx', y', ⟨hy', hnot⟩, heq⟩
          have hxe : x' = x := congrArg Prod.fst heq
          have hye : y' = y := congrArg Prod.snd heq
          subst hxe; subst hye
          refine ⟨⟨j, hx', hy'⟩, ?_⟩
          intro u hu
          exact hnot ⟨u, hu⟩
      have hHj_disj : ∀ j₁ ∈ (Finset.univ : Finset (Fin t)), ∀ j₂ ∈ (Finset.univ : Finset (Fin t)),
          j₁ ≠ j₂ → Disjoint (Hj j₁) (Hj j₂) := by
        intro j₁ _ j₂ _ hne
        rw [Finset.disjoint_left]
        intro xy h1 h2
        rcases Finset.mem_biUnion.mp h1 with ⟨x₁, hx₁, hf₁⟩
        rcases Finset.mem_image.mp hf₁ with ⟨y₁, _, rfl⟩
        rcases Finset.mem_biUnion.mp h2 with ⟨x₂, hx₂, hf₂⟩
        rcases Finset.mem_image.mp hf₂ with ⟨y₂, _, heq⟩
        have hxeq : x₂ = x₁ := congrArg Prod.fst heq
        subst hxeq
        exact Finset.disjoint_left.mp (hblk_disj j₁ j₂ hne) hx₁ hx₂
      have hHj_card : ∀ j : Fin t,
          (Hj j).card = PEqualNP.Outside.L_lib_880.sz t m j * (PEqualNP.Outside.L_lib_880.sz t m j - d) := by
        intro j
        rw [Finset.card_biUnion]
        · have hterm : ∀ x ∈ blk j,
              ((blk j \ Finset.univ.image (fun u : Fin D => p u x)).image (fun y => (x, y))).card =
                PEqualNP.Outside.L_lib_880.sz t m j - d := by
            intro x hx
            have hinj : Function.Injective (fun y : Fin n => (x, y)) := fun _ _ h => congrArg Prod.snd h
            rw [Finset.card_image_of_injective _ hinj]
            have hxb := (Finset.mem_filter.mp hx).2
            have himg_sub : Finset.univ.image (fun u : Fin D => p u x) ⊆ blk j := by
              intro y hy
              rcases Finset.mem_image.mp hy with ⟨u, _, rfl⟩
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have hval := PEqualNP.Outside.L_lib_880.permFun_blk n t m d D ht hmn u x j hxb.1 hxb.2
              have hsucc := PEqualNP.Outside.L_lib_880.off_succ t m j
              have hszpos : 0 < PEqualNP.Outside.L_lib_880.sz t m j := by omega
              have hmod := Nat.mod_lt (x.val - PEqualNP.Outside.L_lib_880.off t m j.val +
                PEqualNP.Outside.L_lib_880.shiftAmt t m d D j u) hszpos
              change PEqualNP.Outside.L_lib_880.off t m j.val ≤ (PEqualNP.Outside.L_lib_880.permFun n t m d D ht hmn u x).val ∧
                (PEqualNP.Outside.L_lib_880.permFun n t m d D ht hmn u x).val < PEqualNP.Outside.L_lib_880.off t m (j.val + 1)
              omega
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr himg_sub]
            rw [PEqualNP.Outside.L_lib_880.blk_card n t m ht hmn j]
            rw [PEqualNP.Outside.L_lib_880.mkPerm_image_card_in_blk n t m d D ht hd hdD hmn j x hxb.1 hxb.2]
            omega
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
            PEqualNP.Outside.L_lib_880.blk_card n t m ht hmn j]
        · intro x₁ _ x₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro xy h1 h2
          rcases Finset.mem_image.mp h1 with ⟨y₁, _, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨y₂, _, heq⟩
          exact hne (congrArg Prod.fst heq).symm
      rw [hHeq, Finset.card_biUnion hHj_disj]
      rw [Finset.sum_congr rfl (fun j _ => hHj_card j)]
      set P : Fin t → Prop := fun j => j.val < rem
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin t)) P]
      have hhi : ∑ j ∈ Finset.univ.filter P,
          PEqualNP.Outside.L_lib_880.sz t m j * (PEqualNP.Outside.L_lib_880.sz t m j - d) =
          rem * ((q + 1) * (q + 1 - d)) := by
        have hcongr : ∀ j ∈ Finset.univ.filter P,
            PEqualNP.Outside.L_lib_880.sz t m j * (PEqualNP.Outside.L_lib_880.sz t m j - d) =
              (q + 1) * (q + 1 - d) := by
          intro j hj
          have hlt : j.val < m % t := (Finset.mem_filter.mp hj).2
          unfold PEqualNP.Outside.L_lib_880.sz
          simp only [hlt, ite_true]
          rfl
        rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]
        congr 1
        have hrem_le : rem ≤ t := le_of_lt (Nat.mod_lt m ht)
        have hbij : (Finset.univ.filter P).card = (Finset.univ : Finset (Fin rem)).card := by
          refine Finset.card_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩)
            (fun _ _ => Finset.mem_univ _)
            (fun j₁ _ j₂ _ heq => Fin.ext (Fin.mk.inj heq))
            (fun k _ => ⟨⟨k.val, lt_of_lt_of_le k.isLt hrem_le⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩)
        rw [hbij, Finset.card_univ, Fintype.card_fin]
      have hlo : ∑ j ∈ Finset.univ.filter (fun j => ¬ P j),
          PEqualNP.Outside.L_lib_880.sz t m j * (PEqualNP.Outside.L_lib_880.sz t m j - d) =
          (t - rem) * (q * (q - d)) := by
        have hcongr : ∀ j ∈ Finset.univ.filter (fun j => ¬ P j),
            PEqualNP.Outside.L_lib_880.sz t m j * (PEqualNP.Outside.L_lib_880.sz t m j - d) =
              q * (q - d) := by
          intro j hj
          have hnot : ¬ j.val < m % t := (Finset.mem_filter.mp hj).2
          unfold PEqualNP.Outside.L_lib_880.sz
          simp only [hnot, ite_false]
          rfl
        rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]
        congr 1
        have hrem_le : rem ≤ t := le_of_lt (Nat.mod_lt m ht)
        have hsum_cards : (Finset.univ.filter P).card + (Finset.univ.filter (fun j => ¬ P j)).card = t := by
          have := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin t)) P (fun _ => (1 : ℕ))
          simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at this
          exact this
        have hPcard : (Finset.univ.filter P).card = rem := by
          have hbij : (Finset.univ.filter P).card = (Finset.univ : Finset (Fin rem)).card := by
            refine Finset.card_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩)
              (fun _ _ => Finset.mem_univ _)
              (fun j₁ _ j₂ _ heq => Fin.ext (Fin.mk.inj heq))
              (fun k _ => ⟨⟨k.val, lt_of_lt_of_le k.isLt hrem_le⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩)
          rw [hbij, Finset.card_univ, Fintype.card_fin]
        omega
      rw [hhi, hlo, Nat.add_comm]
