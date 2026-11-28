import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_239_aux

open Finset PEqualNP.ProofComplexity

/-! Part 1: Balancing and strict convexity of clause and literal counts -/

def clCost (b h : ℕ) : ℕ :=
  (if b = 1 then 7 else 9) * 2 ^ (h - 1) - h - 4

def litCost (b h : ℕ) : ℕ :=
  if h = 1 then (if b = 1 then 4 else 12)
  else (if b = 1 then 7 * h else 9 * h + 6) * 2 ^ (h - 1) - 4

private lemma nine_pow_ge (h : ℕ) (hh : 1 ≤ h) : h + 4 ≤ 9 * 2 ^ (h - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hh
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [Nat.add_succ, Nat.succ_add, Nat.add_zero] at ih ⊢
    rw [show k + 1 + 1 - 1 = k + 1 by omega, pow_succ]
    rw [show k + 1 - 1 = k by omega] at ih
    omega

private lemma clCost_strict_convex (b : ℕ) (hb : 2 ≤ b) (x : ℕ) (hx : 1 ≤ x) :
    2 * clCost b (x + 1) < clCost b x + clCost b (x + 2) := by
  have hb1 : b ≠ 1 := by omega
  have h0 := nine_pow_ge x hx
  have h1 : x + 1 + 4 ≤ 9 * 2 ^ x := by simpa [Nat.add_sub_cancel] using nine_pow_ge (x + 1) (by omega)
  have h2 : x + 2 + 4 ≤ 9 * 2 ^ (x + 1) := by
    simpa [show x + 2 - 1 = x + 1 by omega] using nine_pow_ge (x + 2) (by omega)
  have h0n : clCost b x + (x + 4) = 9 * 2 ^ (x - 1) := by
    simp only [clCost, hb1, ↓reduceIte, Nat.sub_sub]; exact Nat.sub_add_cancel h0
  have h1n : clCost b (x + 1) + (x + 1 + 4) = 9 * 2 ^ x := by
    simp only [clCost, hb1, ↓reduceIte, Nat.add_sub_cancel, Nat.sub_sub]
    exact Nat.sub_add_cancel h1
  have h2n : clCost b (x + 2) + (x + 2 + 4) = 9 * 2 ^ (x + 1) := by
    simp only [clCost, hb1, ↓reduceIte, show x + 2 - 1 = x + 1 by omega, Nat.sub_sub]
    exact Nat.sub_add_cancel h2
  have h0z : (clCost b x : ℤ) + x + 4 = 9 * (2 : ℤ) ^ (x - 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) h0n; push_cast at this; linarith
  have h1z : (clCost b (x + 1) : ℤ) + ((x : ℤ) + 1) + 4 = 9 * (2 : ℤ) ^ x := by
    have := congrArg (Nat.cast : ℕ → ℤ) h1n; push_cast at this; linarith
  have h2z : (clCost b (x + 2) : ℤ) + ((x : ℤ) + 2) + 4 = 9 * (2 : ℤ) ^ (x + 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) h2n; push_cast at this; linarith
  have hpow1 : (2 : ℤ) ^ x = 2 * (2 : ℤ) ^ (x - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hx]
  have hpow2 : (2 : ℤ) ^ (x + 1) = 4 * (2 : ℤ) ^ (x - 1) := by
    rw [pow_succ', hpow1]; ring
  rw [hpow1] at h1z
  rw [hpow2] at h2z
  have hpos : (0 : ℤ) < 2 ^ (x - 1) := by positivity
  zify; linarith

private lemma litCost_strict_convex (b : ℕ) (hb : 2 ≤ b) (x : ℕ) (hx : 1 ≤ x) :
    2 * litCost b (x + 1) < litCost b x + litCost b (x + 2) := by
  have hb1 : b ≠ 1 := by omega
  rcases eq_or_lt_of_le hx with rfl | hx2
  · simp [litCost, hb1]
  · have hx_ne1 : x ≠ 1 := by omega
    have hx1_ne1 : x + 1 ≠ 1 := by omega
    have hx2_ne1 : x + 2 ≠ 1 := by omega
    have hg0 : 4 ≤ (9 * x + 6) * 2 ^ (x - 1) := by
      have : 1 ≤ 2 ^ (x - 1) := Nat.one_le_two_pow; nlinarith
    have hg1 : 4 ≤ (9 * (x + 1) + 6) * 2 ^ x := by
      have : 1 ≤ 2 ^ x := Nat.one_le_two_pow; nlinarith
    have hg2 : 4 ≤ (9 * (x + 2) + 6) * 2 ^ (x + 1) := by
      have : 1 ≤ 2 ^ (x + 1) := Nat.one_le_two_pow; nlinarith
    have h0n : litCost b x + 4 = (9 * x + 6) * 2 ^ (x - 1) := by
      simp only [litCost, hx_ne1, hb1, ↓reduceIte]; exact Nat.sub_add_cancel hg0
    have h1n : litCost b (x + 1) + 4 = (9 * (x + 1) + 6) * 2 ^ x := by
      simp only [litCost, hx1_ne1, hb1, ↓reduceIte, Nat.add_sub_cancel]
      exact Nat.sub_add_cancel hg1
    have h2n : litCost b (x + 2) + 4 = (9 * (x + 2) + 6) * 2 ^ (x + 1) := by
      simp only [litCost, hx2_ne1, hb1, ↓reduceIte, show x + 2 - 1 = x + 1 by omega]
      exact Nat.sub_add_cancel hg2
    have h0z : (litCost b x : ℤ) = (9 * (x : ℤ) + 6) * (2 : ℤ) ^ (x - 1) - 4 :=
      eq_sub_of_add_eq (by exact_mod_cast h0n)
    have h1z : (litCost b (x + 1) : ℤ) = (9 * ((x : ℤ) + 1) + 6) * (2 : ℤ) ^ x - 4 :=
      eq_sub_of_add_eq (by exact_mod_cast h1n)
    have h2z : (litCost b (x + 2) : ℤ) = (9 * ((x : ℤ) + 2) + 6) * (2 : ℤ) ^ (x + 1) - 4 :=
      eq_sub_of_add_eq (by exact_mod_cast h2n)
    have hpow1 : (2 : ℤ) ^ x = 2 * (2 : ℤ) ^ (x - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hx]
    have hpow2 : (2 : ℤ) ^ (x + 1) = 4 * (2 : ℤ) ^ (x - 1) := by
      rw [pow_succ', hpow1]; ring
    have hpos : (0 : ℤ) < (2 : ℤ) ^ (x - 1) := by positivity
    have hdiff : (litCost b x : ℤ) + litCost b (x + 2) - 2 * litCost b (x + 1) =
        (9 * (x : ℤ) + 42) * (2 : ℤ) ^ (x - 1) := by
      rw [h0z, h1z, h2z, hpow1, hpow2]; ring
    have hpos2 : (0 : ℤ) < (9 * (x : ℤ) + 42) * (2 : ℤ) ^ (x - 1) := by nlinarith
    zify; linarith

private lemma convex_step {f : ℕ → ℕ}
    (hconv : ∀ x, 1 ≤ x → 2 * f (x + 1) < f x + f (x + 2)) :
    ∀ x y, 1 ≤ x → x + 2 ≤ y → f (x + 1) + f (y - 1) < f x + f y := by
  intro x y hx hxy
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hxy
  have hstep : ∀ k, (f (x + 1) : ℤ) - f x < f (x + k + 2) - f (x + k + 1) := by
    intro k
    induction k with
    | zero =>
      have := hconv x hx
      zify at this ⊢; linarith
    | succ k ih =>
      have hk := hconv (x + k + 1) (by omega)
      have e1 : x + (k + 1) + 1 = x + k + 2 := by omega
      have e2 : x + (k + 1) + 2 = x + k + 3 := by omega
      have e3 : x + k + 1 + 1 = x + k + 2 := by omega
      have e4 : x + k + 1 + 2 = x + k + 3 := by omega
      rw [e3, e4] at hk
      rw [e1, e2]
      zify at hk ⊢; linarith
  have h := hstep d
  have hy1 : y = x + d + 2 := by omega
  have hy2 : y - 1 = x + d + 1 := by omega
  rw [← hy1, ← hy2] at h
  zify; linarith

def ValidGap (n b : ℕ) (gap : Fin b → ℕ) : Prop :=
  (∀ i, 0 < gap i) ∧ (∑ i, gap i) = n

def BalancedGap (b : ℕ) (gap : Fin b → ℕ) : Prop :=
  ∀ i j, gap i ≤ gap j + 1

private lemma exists_balanced_gap (n b : ℕ) (hb : 0 < b) (hbn : b ≤ n) :
    ∃ gap : Fin b → ℕ, ValidGap n b gap ∧ BalancedGap b gap := by
  refine ⟨fun i => n / b + if i.val < n % b then 1 else 0, ⟨?_, ?_⟩, ?_⟩
  · intro i
    have : 0 < n / b := Nat.div_pos hbn hb
    dsimp only; split_ifs <;> omega
  · rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hrem : ∑ i : Fin b, (if i.val < n % b then 1 else 0) = n % b := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      have hlt : n % b < b := Nat.mod_lt _ hb
      exact (Finset.card_nbij' (fun i : Fin b => i.val)
        (fun k => if h : k < b then ⟨k, h⟩ else ⟨0, hb⟩)
        (fun i hi => by
          dsimp only
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hi
          exact mem_coe.mpr (mem_range.mpr hi))
        (fun k hk => by
          have hk' := Finset.mem_range.mp (mem_coe.mp hk)
          have hkb : k < b := lt_trans hk' hlt
          dsimp only; split_ifs
          simp only [mem_coe, mem_filter, mem_univ, true_and]; exact hk')
        (fun i _ => by have hi' := i.isLt; dsimp only; split_ifs; rfl)
        (fun k hk => by
          have hk' := Finset.mem_range.mp (mem_coe.mp hk)
          have hkb : k < b := lt_trans hk' hlt
          dsimp only; split_ifs; rfl)).trans
        (Finset.card_range _)
    rw [hrem, Nat.div_add_mod]
  · intro i j
    dsimp only; split_ifs <;> omega

private lemma balanced_sum_eq (n b : ℕ) (hb : 0 < b) (f : ℕ → ℕ)
    (gap : Fin b → ℕ) (hv : ValidGap n b gap) (hbal : BalancedGap b gap) :
    ∑ i, f (gap i) = (b - n % b) * f (n / b) + n % b * f (n / b + 1) := by
  have hne : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  obtain ⟨imin, _, himin⟩ := Finset.exists_min_image Finset.univ gap Finset.univ_nonempty
  let m := gap imin
  have hm_le : ∀ i, m ≤ gap i := fun i => himin i (mem_univ i)
  have hle_m1 : ∀ i, gap i ≤ m + 1 := fun i => hbal i imin
  let A := Finset.univ.filter (fun i : Fin b => gap i = m + 1)
  have hsum_parts : ∑ i : Fin b, gap i = b * m + A.card := by
    have hsplit : ∀ i : Fin b, gap i = m + if i ∈ A then 1 else 0 := by
      intro i
      simp only [A, mem_filter, mem_univ, true_and]
      have h1 := hm_le i; have h2 := hle_m1 i
      split_ifs <;> omega
    calc ∑ i : Fin b, gap i
        = ∑ i : Fin b, (m + if i ∈ A then 1 else 0) := sum_congr rfl fun i _ => hsplit i
      _ = b * m + A.card := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
              ← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, smul_eq_mul, mul_one]
  rw [hv.2] at hsum_parts
  have hAc_lt : A.card < b := by
    have himin_nA : imin ∉ A := by simp [A, m]
    have hss : A ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, fun h => by
      rw [h] at himin_nA; exact himin_nA (mem_univ _)⟩
    simpa [Fintype.card_fin] using card_lt_card hss
  have hdiv : n / b = m := by
    rw [hsum_parts, Nat.mul_add_div hb, Nat.div_eq_of_lt hAc_lt, add_zero]
  have hmod : n % b = A.card := by
    rw [hsum_parts, Nat.mul_add_mod, Nat.mod_eq_of_lt hAc_lt]
  have hsplit_f : ∀ i : Fin b, f (gap i) = if i ∈ A then f (m + 1) else f m := by
    intro i
    simp only [A, mem_filter, mem_univ, true_and]
    have h1 := hm_le i; have h2 := hle_m1 i
    split_ifs with h
    · rw [h]
    · rw [show gap i = m by omega]
  calc ∑ i : Fin b, f (gap i)
      = ∑ i ∈ Finset.univ, if i ∈ A then f (m + 1) else f m :=
          sum_congr rfl fun i _ => hsplit_f i
    _ = ∑ i ∈ A, f (m + 1) + ∑ i ∈ Finset.univ \ A, f m := by
          rw [← sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
          congr 1
          · rw [filter_mem_eq_inter, univ_inter]
            exact sum_congr rfl fun x hx => if_pos hx
          · simp only [sdiff_eq_filter]
            refine sum_congr (by ext x; simp) fun x hx => ?_
            exact if_neg (by simp only [mem_filter, mem_univ, true_and] at hx; exact hx)
    _ = A.card * f (m + 1) + (b - A.card) * f m := by
          rw [sum_const, smul_eq_mul, sum_const, card_sdiff, inter_univ, card_univ,
              Fintype.card_fin, smul_eq_mul]
    _ = (b - n % b) * f (n / b) + n % b * f (n / b + 1) := by
          rw [hdiv, hmod]; ring

private lemma convex_balance_opt (n b : ℕ) (hb : 0 < b) (f : ℕ → ℕ)
    (hconv : ∀ x, 1 ≤ x → 2 * f (x + 1) < f x + f (x + 2)) :
    ∀ gap : Fin b → ℕ, ValidGap n b gap →
      (b - n % b) * f (n / b) + n % b * f (n / b + 1) ≤ ∑ i, f (gap i) ∧
      (∑ i, f (gap i) = (b - n % b) * f (n / b) + n % b * f (n / b + 1) ↔ BalancedGap b gap) := by
  have hpot : ∀ (M : ℕ) (gap : Fin b → ℕ), (∑ i, gap i ^ 2) ≤ M → ValidGap n b gap →
      (b - n % b) * f (n / b) + n % b * f (n / b + 1) ≤ ∑ i, f (gap i) ∧
      (∑ i, f (gap i) = (b - n % b) * f (n / b) + n % b * f (n / b + 1) ↔ BalancedGap b gap) := by
    intro M
    induction M using Nat.strong_induction_on with
    | ind M ih =>
      intro gap hleM hv
      by_cases hbal : BalancedGap b gap
      · have heq := balanced_sum_eq n b hb f gap hv hbal
        exact ⟨le_of_eq heq.symm, ⟨fun _ => hbal, fun _ => heq⟩⟩
      · unfold BalancedGap at hbal
        push_neg at hbal
        obtain ⟨i0, j0, hij⟩ := hbal
        have hne : i0 ≠ j0 := fun h => by subst h; omega
        let gap' : Fin b → ℕ := fun k =>
          if k = i0 then gap i0 - 1 else if k = j0 then gap j0 + 1 else gap k
        have hv' : ValidGap n b gap' := by
          refine ⟨fun k => ?_, ?_⟩
          · dsimp only [gap']; split_ifs <;> have := hv.1 k <;> omega
          · have hsum_diff : ∑ k : Fin b, gap' k + 1 = ∑ k : Fin b, gap k + 1 := by
              have hi0 : i0 ∈ (Finset.univ : Finset (Fin b)) := mem_univ _
              have hj0 : j0 ∈ (Finset.univ.erase i0) := mem_erase.mpr ⟨hne.symm, mem_univ _⟩
              rw [← add_sum_erase Finset.univ gap' hi0, ← add_sum_erase Finset.univ gap hi0]
              rw [← add_sum_erase _ gap' hj0, ← add_sum_erase _ gap hj0]
              have hrest : ∑ x ∈ (Finset.univ.erase i0).erase j0, gap' x =
                  ∑ x ∈ (Finset.univ.erase i0).erase j0, gap x := by
                refine sum_congr rfl fun x hx => ?_
                have hx1 : x ≠ i0 := (mem_erase.mp (mem_erase.mp hx).2).1
                have hx2 : x ≠ j0 := (mem_erase.mp hx).1
                simp [gap', hx1, hx2]
              have hgi : gap' i0 = gap i0 - 1 := by simp [gap']
              have hgj : gap' j0 = gap j0 + 1 := by simp [gap', hne.symm]
              rw [hrest, hgi, hgj]
              have : 1 ≤ gap i0 := hv.1 i0
              omega
            have hgv := hv.2
            omega
        have hlt_pot : ∑ k : Fin b, gap' k ^ 2 < ∑ k : Fin b, gap k ^ 2 := by
          have hi0 : i0 ∈ (Finset.univ : Finset (Fin b)) := mem_univ _
          have hj0 : j0 ∈ (Finset.univ.erase i0) := mem_erase.mpr ⟨hne.symm, mem_univ _⟩
          rw [← add_sum_erase Finset.univ (fun k => gap' k ^ 2) hi0,
              ← add_sum_erase Finset.univ (fun k => gap k ^ 2) hi0]
          rw [← add_sum_erase _ (fun k => gap' k ^ 2) hj0,
              ← add_sum_erase _ (fun k => gap k ^ 2) hj0]
          have hrest : ∑ x ∈ (Finset.univ.erase i0).erase j0, gap' x ^ 2 =
              ∑ x ∈ (Finset.univ.erase i0).erase j0, gap x ^ 2 := by
            refine sum_congr rfl fun x hx => ?_
            have hx1 : x ≠ i0 := (mem_erase.mp (mem_erase.mp hx).2).1
            have hx2 : x ≠ j0 := (mem_erase.mp hx).1
            simp [gap', hx1, hx2]
          have hgi : gap' i0 = gap i0 - 1 := by simp [gap']
          have hgj : gap' j0 = gap j0 + 1 := by simp [gap', hne.symm]
          rw [hrest, hgi, hgj]
          have hsub_sq : (gap i0 - 1) ^ 2 + (gap j0 + 1) ^ 2 < gap i0 ^ 2 + gap j0 ^ 2 := by
            have h1 : 1 ≤ gap j0 := hv.1 j0
            have h2 : gap j0 + 2 ≤ gap i0 := hij
            zify [show 1 ≤ gap i0 by omega]
            nlinarith
          omega
        have hlt_f : ∑ k : Fin b, f (gap' k) < ∑ k : Fin b, f (gap k) := by
          have hi0 : i0 ∈ (Finset.univ : Finset (Fin b)) := mem_univ _
          have hj0 : j0 ∈ (Finset.univ.erase i0) := mem_erase.mpr ⟨hne.symm, mem_univ _⟩
          rw [← add_sum_erase Finset.univ (fun k => f (gap' k)) hi0,
              ← add_sum_erase Finset.univ (fun k => f (gap k)) hi0]
          rw [← add_sum_erase _ (fun k => f (gap' k)) hj0,
              ← add_sum_erase _ (fun k => f (gap k)) hj0]
          have hrest : ∑ x ∈ (Finset.univ.erase i0).erase j0, f (gap' x) =
              ∑ x ∈ (Finset.univ.erase i0).erase j0, f (gap x) := by
            refine sum_congr rfl fun x hx => ?_
            have hx1 : x ≠ i0 := (mem_erase.mp (mem_erase.mp hx).2).1
            have hx2 : x ≠ j0 := (mem_erase.mp hx).1
            simp [gap', hx1, hx2]
          have hgi : gap' i0 = gap i0 - 1 := by simp [gap']
          have hgj : gap' j0 = gap j0 + 1 := by simp [gap', hne.symm]
          rw [hrest, hgi, hgj]
          have hstep := convex_step hconv (gap j0) (gap i0) (hv.1 j0) hij
          omega
        have hrec := ih (∑ k, gap' k ^ 2) (lt_of_lt_of_le hlt_pot hleM) gap' le_rfl hv'
        refine ⟨hrec.1.trans hlt_f.le,
          ⟨fun h => (lt_irrefl _ (hrec.1.trans_lt (h ▸ hlt_f))).elim,
           fun h => absurd (h i0 j0) (by omega)⟩⟩
  intro gap hv
  exact hpot (∑ i, gap i ^ 2) gap le_rfl hv

private lemma b1_balance_opt (n : ℕ) (hn : 0 < n) (f : ℕ → ℕ) (gap : Fin 1 → ℕ)
    (hv : ValidGap n 1 gap) :
    (1 - n % 1) * f (n / 1) + n % 1 * f (n / 1 + 1) ≤ ∑ i, f (gap i) ∧
    (∑ i, f (gap i) = (1 - n % 1) * f (n / 1) + n % 1 * f (n / 1 + 1) ↔ BalancedGap 1 gap) := by
  have hbal : BalancedGap 1 gap := fun i j => by
    rw [Fin.eq_zero i, Fin.eq_zero j]; omega
  have heq := balanced_sum_eq n 1 Nat.one_pos f gap hv hbal
  exact ⟨le_of_eq heq.symm, ⟨fun _ => hbal, fun _ => heq⟩⟩

/-! Part 2: Cycle partition for an arbitrary valid gap layout -/

section Layout

variable (n b : ℕ) (hn : 0 < n) (hb : 0 < b) (origin : Fin n) (gap : Fin b → ℕ)

def posN (idx : ℕ) : Fin n := ⟨idx % n, Nat.mod_lt _ hn⟩

def nextGap (i : Fin b) : Fin b := ⟨(i.val + 1) % b, Nat.mod_lt _ hb⟩

def gapStart (i : Fin b) : ℕ :=
  origin.val + ∑ j ∈ Finset.univ.filter (fun z : Fin b => z.val < i.val), gap j

def gapSite (i : Fin b) (k : ℕ) : Fin n :=
  posN n hn (gapStart n b origin gap i + k)

private lemma gapStart_succ_eq (hv : ValidGap n b gap) (i : Fin b) (hi : i.val + 1 < b) :
    gapStart n b origin gap ⟨i.val + 1, hi⟩ = gapStart n b origin gap i + gap i := by
  unfold gapStart
  have hsplit : Finset.univ.filter (fun z : Fin b => z.val < i.val + 1) =
      insert i (Finset.univ.filter (fun z : Fin b => z.val < i.val)) := by
    ext z; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
  have hni : i ∉ Finset.univ.filter (fun z : Fin b => z.val < i.val) := by simp
  rw [hsplit, sum_insert hni]
  omega

private lemma gapStart_last_add (hv : ValidGap n b gap) (i : Fin b) (hi : i.val + 1 = b) :
    gapStart n b origin gap i + gap i = origin.val + n := by
  unfold gapStart
  have hun : insert i (Finset.univ.filter (fun z : Fin b => z.val < i.val)) = Finset.univ := by
    ext z; simp only [mem_insert, mem_filter, mem_univ, true_and, Fin.ext_iff, iff_true]
    have hz := z.isLt
    omega
  have hni : i ∉ Finset.univ.filter (fun z : Fin b => z.val < i.val) := by simp
  rw [add_assoc, add_comm (∑ j ∈ _, gap j) (gap i), ← sum_insert hni, hun, hv.2]

private lemma gapSite_end (hv : ValidGap n b gap) (i : Fin b) :
    gapSite n b hn origin gap i (gap i) =
      posN n hn (gapStart n b origin gap (nextGap b hb i)) := by
  unfold gapSite nextGap
  by_cases hi : i.val + 1 < b
  · have hnext : (⟨(i.val + 1) % b, Nat.mod_lt _ hb⟩ : Fin b) = ⟨i.val + 1, hi⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hi)
    rw [hnext, gapStart_succ_eq n b origin gap hv i hi]
  · have hi_eq : i.val + 1 = b := by have := i.isLt; omega
    have hmod : (i.val + 1) % b = 0 := by rw [hi_eq, Nat.mod_self]
    have hstart0 : gapStart n b origin gap ⟨0, hb⟩ = origin.val := by
      simp [gapStart]
    rw [gapStart_last_add n b origin gap hv i hi_eq]
    apply Fin.ext
    simp only [posN, hmod, hstart0, Nat.add_mod_right]

private lemma gapSite_next (k : ℕ) (i : Fin b) :
    posN n hn ((gapSite n b hn origin gap i k).val + 1) =
      gapSite n b hn origin gap i (k + 1) := by
  apply Fin.ext
  simp [gapSite, posN, Nat.add_assoc, Nat.mod_add_mod]

private lemma gapStart_sub_add_sum (hv : ValidGap n b gap) (i : Fin b) :
    gapStart n b origin gap i - origin.val +
      ∑ j ∈ Finset.univ.filter (fun z : Fin b => i.val ≤ z.val), gap j = n := by
  have hun : Finset.univ.filter (fun z : Fin b => z.val < i.val) ∪
      Finset.univ.filter (fun z : Fin b => i.val ≤ z.val) = Finset.univ := by
    ext z; simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]; omega
  have hdisj : Disjoint (Finset.univ.filter (fun z : Fin b => z.val < i.val))
      (Finset.univ.filter (fun z : Fin b => i.val ≤ z.val)) := by
    rw [Finset.disjoint_left]; intro z h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2; omega
  have hs : gapStart n b origin gap i - origin.val =
      ∑ j ∈ Finset.univ.filter (fun z : Fin b => z.val < i.val), gap j := by
    simp [gapStart]
  rw [hs, ← sum_union hdisj, hun, hv.2]

private lemma add_mod_eq_add_mod_cancel {a u v n : ℕ} (hu : u < n) (hv : v < n)
    (h : (a + u) % n = (a + v) % n) : u = v := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le u) hu
  have hm1 : (a + u) % n = (a % n + u) % n := by rw [Nat.add_mod, Nat.mod_eq_of_lt hu]
  have hm2 : (a + v) % n = (a % n + v) % n := by rw [Nat.add_mod, Nat.mod_eq_of_lt hv]
  rw [hm1, hm2] at h
  have ha := Nat.mod_lt a hn
  by_cases h1 : a % n + u < n <;> by_cases h2 : a % n + v < n
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · have hlt : a % n + v - n < n := by omega
    have hmv : (a % n + v) % n = a % n + v - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt]
    rw [Nat.mod_eq_of_lt h1, hmv] at h; omega
  · have hlt : a % n + u - n < n := by omega
    have hmu : (a % n + u) % n = a % n + u - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt]
    rw [hmu, Nat.mod_eq_of_lt h2] at h; omega
  · have hlt1 : a % n + u - n < n := by omega
    have hlt2 : a % n + v - n < n := by omega
    have hmu : (a % n + u) % n = a % n + u - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1]
    have hmv : (a % n + v) % n = a % n + v - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
    rw [hmu, hmv] at h; omega

private lemma gapSite_inj (hv : ValidGap n b gap) :
    Function.Injective (fun p : Σ i : Fin b, Fin (gap i) =>
      gapSite n b hn origin gap p.1 p.2.val) := by
  rintro ⟨i1, k1⟩ ⟨i2, k2⟩ h
  let u1 := ∑ j ∈ Finset.univ.filter (fun z : Fin b => z.val < i1.val), gap j + k1.val
  let u2 := ∑ j ∈ Finset.univ.filter (fun z : Fin b => z.val < i2.val), gap j + k2.val
  have hlt1 : u1 < n := by
    have hs := gapStart_sub_add_sum n b origin gap hv i1
    have hi1 : gap i1 ≤ ∑ j ∈ Finset.univ.filter (fun z : Fin b => i1.val ≤ z.val), gap j :=
      single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.mpr ⟨mem_univ _, le_rfl⟩)
    have hge : origin.val ≤ gapStart n b origin gap i1 := by simp [gapStart]
    dsimp only [u1]; simp only [gapStart] at hs; omega
  have hlt2 : u2 < n := by
    have hs := gapStart_sub_add_sum n b origin gap hv i2
    have hi2 : gap i2 ≤ ∑ j ∈ Finset.univ.filter (fun z : Fin b => i2.val ≤ z.val), gap j :=
      single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.mpr ⟨mem_univ _, le_rfl⟩)
    dsimp only [u2]; simp only [gapStart] at hs; omega
  have hmod : (origin.val + u1) % n = (origin.val + u2) % n := by
    have hv' := congrArg Fin.val h
    simp only [gapSite, posN, gapStart, Nat.add_assoc] at hv'
    exact hv'
  have hueq : u1 = u2 := add_mod_eq_add_mod_cancel hlt1 hlt2 hmod
  have hi_eq : i1 = i2 := by
    by_contra hne
    have hord : ∀ a c : Fin b, a.val < c.val →
        ∑ j ∈ Finset.univ.filter (fun z : Fin b => z.val < a.val), gap j + gap a ≤
        ∑ j ∈ Finset.univ.filter (fun z : Fin b => z.val < c.val), gap j := by
      intro a c hac
      have hsub : insert a (Finset.univ.filter (fun z : Fin b => z.val < a.val)) ⊆
          Finset.univ.filter (fun z : Fin b => z.val < c.val) := by
        intro z hz; simp only [mem_insert, mem_filter, mem_univ, true_and] at hz ⊢
        rcases hz with rfl | hz <;> omega
      have ha_n : a ∉ Finset.univ.filter (fun z : Fin b => z.val < a.val) := by simp
      calc ∑ j ∈ Finset.univ.filter (fun z : Fin b => z.val < a.val), gap j + gap a
          = ∑ j ∈ insert a (Finset.univ.filter (fun z : Fin b => z.val < a.val)), gap j := by
              rw [sum_insert ha_n]; omega
        _ ≤ ∑ j ∈ Finset.univ.filter (fun z : Fin b => z.val < c.val), gap j :=
              sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
    rcases Nat.lt_or_gt_of_ne (fun he => hne (Fin.ext he)) with hlt | hgt
    · have := hord i1 i2 hlt; have hk1 := k1.isLt; dsimp only [u1, u2] at hueq; omega
    · have := hord i2 i1 hgt; have hk2 := k2.isLt; dsimp only [u1, u2] at hueq; omega
  subst hi_eq
  have hk_eq : k1 = k2 := Fin.ext (by dsimp only [u1, u2] at hueq; omega)
  subst hk_eq; rfl

private lemma gapSite_same_inj (hv : ValidGap n b gap) {i : Fin b} {k1 k2 : Fin (gap i)}
    (h : gapSite n b hn origin gap i k1.val = gapSite n b hn origin gap i k2.val) : k1 = k2 := by
  have heq : (⟨i, k1⟩ : Σ j : Fin b, Fin (gap j)) = ⟨i, k2⟩ :=
    @gapSite_inj n b hn origin gap hv ⟨i, k1⟩ ⟨i, k2⟩ h
  exact eq_of_heq (Sigma.ext_iff.mp heq).2

private lemma gapSite_fst_eq (hv : ValidGap n b gap) {i1 i2 : Fin b} {k1 : Fin (gap i1)} {k2 : Fin (gap i2)}
    (h : gapSite n b hn origin gap i1 k1.val = gapSite n b hn origin gap i2 k2.val) : i1 = i2 :=
  congrArg Sigma.fst (@gapSite_inj n b hn origin gap hv ⟨i1, k1⟩ ⟨i2, k2⟩ h)

noncomputable def siteEquiv (hv : ValidGap n b gap) :
    (Σ i : Fin b, Fin (gap i)) ≃ Fin n :=
  Equiv.ofBijective
    (fun p => gapSite n b hn origin gap p.1 p.2.val)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨gapSite_inj n b hn origin gap hv, by simp [Fintype.card_sigma, hv.2]⟩)

end Layout

/-! Part 3: Canonical cut codes, layers, clauses, counts, and injectivity -/

inductive CutCode (h : ℕ) : Type
  | t1 (f : Fin (h + 1) → Bool)
  | t2 (s : Fin (h - 1)) (f : Fin (s.val + 1) → Bool)
  | t3 (t_off : Fin (h - 1)) (f : Fin (t_off.val + 1) → Bool)
  | t4 (a_off : Fin (h - 2)) (p_off : Fin (a_off.val + 1)) (f : Fin p_off.val → Bool)
  deriving DecidableEq

def cutEquiv (h : ℕ) : CutCode h ≃
    (Fin (h + 1) → Bool) ⊕
    (Σ s : Fin (h - 1), Fin (s.val + 1) → Bool) ⊕
    (Σ t_off : Fin (h - 1), Fin (t_off.val + 1) → Bool) ⊕
    (Σ a_off : Fin (h - 2), Σ p_off : Fin (a_off.val + 1), Fin p_off.val → Bool) where
  toFun
    | .t1 f => Sum.inl f
    | .t2 s f => Sum.inr (Sum.inl ⟨s, f⟩)
    | .t3 t_off f => Sum.inr (Sum.inr (Sum.inl ⟨t_off, f⟩))
    | .t4 a_off p_off f => Sum.inr (Sum.inr (Sum.inr ⟨a_off, p_off, f⟩))
  invFun
    | Sum.inl f => .t1 f
    | Sum.inr (Sum.inl ⟨s, f⟩) => .t2 s f
    | Sum.inr (Sum.inr (Sum.inl ⟨t_off, f⟩)) => .t3 t_off f
    | Sum.inr (Sum.inr (Sum.inr ⟨a_off, p_off, f⟩)) => .t4 a_off p_off f
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _, _⟩ <;> rfl

noncomputable instance (h : ℕ) : Fintype (CutCode h) :=
  Fintype.ofEquiv _ (cutEquiv h).symm

def validCut (h : ℕ) (b1 : Bool) : CutCode h → Bool
  | .t1 f => if b1 then decide (f ⟨h, Nat.lt_succ_self h⟩ = !(f 0)) else true
  | _ => true

def cutR {h : ℕ} (c : CutCode h) (k : Fin (h + 1)) : Finset Bool :=
  match c with
  | .t1 f => {f k}
  | .t2 s f =>
      if hk : k.val ≤ s.val then {f ⟨k.val, Nat.lt_succ_of_le hk⟩}
      else if k.val = s.val + 1 then ∅ else Finset.univ
  | .t3 t_off f =>
      let t := h - t_off.val
      if hk : k.val < t then Finset.univ
      else {f ⟨k.val - t, by have := t_off.isLt; have := k.isLt; omega⟩}
  | .t4 a_off p_off f =>
      let a := a_off.val + 2
      let p := a - p_off.val
      if hkp : k.val < p then Finset.univ
      else if hk : k.val < a then {f ⟨k.val - p, by dsimp only [p, a] at *; have := p_off.isLt; omega⟩}
      else if k.val = a then ∅ else Finset.univ

def cutReqU {h : ℕ} : CutCode h → Option Bool
  | .t1 f => some (f 0)
  | .t2 _ f => some (f 0)
  | .t3 _ _ => none
  | .t4 _ _ _ => none

def cutReqV {h : ℕ} : CutCode h → Option Bool
  | .t1 f => some (!(f ⟨h, Nat.lt_succ_self h⟩))
  | .t2 _ _ => none
  | .t3 t_off f => some (!(f ⟨t_off.val, Nat.lt_succ_self t_off.val⟩))
  | .t4 _ _ _ => none

def cutEdges {h : ℕ} (c : CutCode h) : Finset (Fin h × Bool × Bool) :=
  Finset.univ.filter fun e => e.2.1 ∈ cutR c e.1.castSucc ∧ e.2.2 ∉ cutR c e.1.succ

private lemma mem_cutEdges {h : ℕ} (c : CutCode h) (e : Fin h × Bool × Bool) :
    e ∈ cutEdges c ↔ e.2.1 ∈ cutR c e.1.castSucc ∧ e.2.2 ∉ cutR c e.1.succ := by
  simp [cutEdges]

private lemma card_univ_bool : (Finset.univ : Finset Bool).card = 2 := by decide

private lemma card_layer_cutEdges {h : ℕ} (c : CutCode h) (k : Fin h) :
    ((cutEdges c).filter (fun e => e.1 = k)).card =
      (cutR c k.castSucc).card * (2 - (cutR c k.succ).card) := by
  let L := Finset.univ.filter (fun x : Bool => x ∈ cutR c k.castSucc)
  let R := Finset.univ.filter (fun y : Bool => y ∉ cutR c k.succ)
  have hbij : ((cutEdges c).filter (fun e => e.1 = k)).card = (L ×ˢ R).card := by
    refine Finset.card_nbij' (fun e => e.2) (fun p => (k, p)) ?_ ?_ ?_ ?_
    · intro e he
      simp only [mem_coe, mem_filter, mem_cutEdges] at he
      rcases he with ⟨⟨h1, h2⟩, rfl⟩
      exact mem_coe.mpr (mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, h1⟩,
        mem_filter.mpr ⟨mem_univ _, h2⟩⟩)
    · intro p hp
      dsimp only [L, R] at hp
      simp only [mem_coe, mem_product, mem_filter, mem_univ, true_and] at hp
      exact mem_coe.mpr (mem_filter.mpr ⟨(mem_cutEdges c (k, p)).mpr hp, rfl⟩)
    · rintro ⟨k', p⟩ he
      simp only [mem_coe, mem_filter] at he
      exact Prod.ext he.2.symm rfl
    · intro p _; rfl
  rw [hbij, card_product]
  have hL : L.card = (cutR c k.castSucc).card := by
    congr 1; ext x; simp [L]
  have hR : R.card = 2 - (cutR c k.succ).card := by
    have hun : R = Finset.univ \ cutR c k.succ := by ext y; simp [R]
    rw [hun, card_sdiff, inter_univ, card_univ_bool]
  rw [hL, hR]

private lemma cutEdges_card_sum {h : ℕ} (c : CutCode h) :
    (cutEdges c).card = ∑ k : Fin h, ((cutEdges c).filter (fun e => e.1 = k)).card := by
  rw [← card_biUnion]
  · congr 1; ext e; simp
  · intro k1 _ k2 _ hne
    dsimp only [Function.onFun]; rw [disjoint_left]; intro e h1 h2
    exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)

private lemma cutEdges_layer_t1 {h : ℕ} (f : Fin (h + 1) → Bool) (k : Fin h) :
    ((cutEdges (CutCode.t1 f)).filter (fun e => e.1 = k)).card = 1 := by
  rw [card_layer_cutEdges]
  simp only [cutR, card_singleton]

private lemma cutEdges_card_t1 {h : ℕ} (f : Fin (h + 1) → Bool) :
    (cutEdges (CutCode.t1 f)).card = h := by
  rw [cutEdges_card_sum]
  calc ∑ k : Fin h, ((cutEdges (CutCode.t1 f)).filter (fun e => e.1 = k)).card
      = ∑ k : Fin h, 1 := sum_congr rfl fun k _ => cutEdges_layer_t1 f k
    _ = h := by simp

private lemma cutEdges_layer_t2 {h : ℕ} (s : Fin (h - 1)) (f : Fin (s.val + 1) → Bool) (k : Fin h) :
    ((cutEdges (CutCode.t2 s f)).filter (fun e => e.1 = k)).card =
      if k.val = s.val then 2 else if k.val < s.val then 1 else 0 := by
  rw [card_layer_cutEdges]
  simp only [cutR, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp only [card_univ_bool, card_empty, card_singleton] <;> omega

private lemma cutEdges_card_t2 {h : ℕ} (s : Fin (h - 1)) (f : Fin (s.val + 1) → Bool) :
    (cutEdges (CutCode.t2 s f)).card = s.val + 2 := by
  rw [cutEdges_card_sum]
  have hs_lt : s.val + 1 < h := by have := s.isLt; omega
  calc ∑ k : Fin h, ((cutEdges (CutCode.t2 s f)).filter (fun e => e.1 = k)).card
      = ∑ k : Fin h, (if k.val = s.val then 2 else if k.val < s.val then 1 else 0) :=
          sum_congr rfl fun k _ => cutEdges_layer_t2 s f k
    _ = (∑ k : Fin h, if k.val = s.val then 1 else 0) +
          (∑ k : Fin h, if k.val ≤ s.val then 1 else 0) := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun k _ => ?_
          by_cases heq : k.val = s.val <;> by_cases hlt : k.val < s.val <;> simp [heq, hlt] <;> omega
    _ = 1 + (s.val + 1) := by
          have hA : ∑ k : Fin h, (if k.val = s.val then 1 else 0) = 1 := by
            rw [← sum_filter, sum_const, smul_eq_mul, mul_one]
            have hunq : Finset.univ.filter (fun k : Fin h => k.val = s.val) =
                {⟨s.val, by omega⟩} := by
              ext k; simp [Fin.ext_iff]
            rw [hunq, card_singleton]
          have hB : ∑ k : Fin h, (if k.val ≤ s.val then 1 else 0) = s.val + 1 := by
            rw [← sum_filter, sum_const, smul_eq_mul, mul_one]
            have hcard : (Finset.univ.filter (fun k : Fin h => k.val ≤ s.val)).card =
                (Finset.range (s.val + 1)).card := by
              refine card_nbij' (fun k => k.val)
                (fun m => if hm : m < h then ⟨m, hm⟩ else ⟨0, by omega⟩)
                (fun k hk => by
                  dsimp only
                  simp only [mem_coe, mem_filter, mem_univ, true_and] at hk
                  exact mem_coe.mpr (mem_range.mpr (by omega)))
                (fun m hm => by
                  have hm' := mem_range.mp (mem_coe.mp hm)
                  have hmh : m < h := by omega
                  dsimp only; split_ifs
                  simp only [mem_coe, mem_filter, mem_univ, true_and]; omega)
                (fun k _ => by have hk := k.isLt; dsimp only; split_ifs; rfl)
                (fun m hm => by
                  have hm' := mem_range.mp (mem_coe.mp hm)
                  have hmh : m < h := by omega
                  dsimp only; split_ifs; rfl)
            rw [hcard, card_range]
          rw [hA, hB]
    _ = s.val + 2 := by ring

private lemma cutEdges_layer_t3 {h : ℕ} (t_off : Fin (h - 1)) (f : Fin (t_off.val + 1) → Bool) (k : Fin h) :
    ((cutEdges (CutCode.t3 t_off f)).filter (fun e => e.1 = k)).card =
      if k.val = h - t_off.val - 1 then 2 else if h - t_off.val ≤ k.val then 1 else 0 := by
  have ht_lt : t_off.val + 1 < h := by have := t_off.isLt; omega
  rw [card_layer_cutEdges]
  simp only [cutR, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp only [card_univ_bool, card_singleton] <;> omega

private lemma cutEdges_card_t3 {h : ℕ} (t_off : Fin (h - 1)) (f : Fin (t_off.val + 1) → Bool) :
    (cutEdges (CutCode.t3 t_off f)).card = t_off.val + 2 := by
  rw [cutEdges_card_sum]
  have ht_lt : t_off.val + 1 < h := by have := t_off.isLt; omega
  let t := h - t_off.val
  calc ∑ k : Fin h, ((cutEdges (CutCode.t3 t_off f)).filter (fun e => e.1 = k)).card
      = ∑ k : Fin h, (if k.val = t - 1 then 2 else if t ≤ k.val then 1 else 0) :=
          sum_congr rfl fun k _ => cutEdges_layer_t3 t_off f k
    _ = (∑ k : Fin h, if k.val = t - 1 then 1 else 0) +
          (∑ k : Fin h, if t - 1 ≤ k.val then 1 else 0) := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun k _ => ?_
          by_cases heq : k.val = t - 1 <;> by_cases hge : t ≤ k.val <;> simp [heq, hge] <;> omega
    _ = 1 + (t_off.val + 1) := by
          have hA : ∑ k : Fin h, (if k.val = t - 1 then 1 else 0) = 1 := by
            rw [← sum_filter, sum_const, smul_eq_mul, mul_one]
            have hunq : Finset.univ.filter (fun k : Fin h => k.val = t - 1) =
                {⟨t - 1, by omega⟩} := by
              ext k; simp [Fin.ext_iff]
            rw [hunq, card_singleton]
          have hB : ∑ k : Fin h, (if t - 1 ≤ k.val then 1 else 0) = t_off.val + 1 := by
            rw [← sum_filter, sum_const, smul_eq_mul, mul_one]
            have hcard : (Finset.univ.filter (fun k : Fin h => t - 1 ≤ k.val)).card =
                (Finset.range (t_off.val + 1)).card := by
              refine card_nbij' (fun k => k.val - (t - 1))
                (fun m => if hm : t - 1 + m < h then ⟨t - 1 + m, hm⟩ else ⟨0, by omega⟩)
                (fun k hk => by
                  dsimp only [t] at *
                  simp only [mem_coe, mem_filter, mem_univ, true_and] at hk
                  have := k.isLt
                  exact mem_coe.mpr (mem_range.mpr (by omega)))
                (fun m hm => by
                  have hm' := mem_range.mp (mem_coe.mp hm)
                  have hmh : t - 1 + m < h := by dsimp only [t]; omega
                  dsimp only; split_ifs
                  simp only [mem_coe, mem_filter, mem_univ, true_and]; omega)
                (fun k hk => by
                  simp only [mem_coe, mem_filter, mem_univ, true_and] at hk
                  have hkh : t - 1 + (k.val - (t - 1)) < h := by have := k.isLt; dsimp only [t] at *; omega
                  dsimp only; split_ifs
                  apply Fin.ext; dsimp only [t] at *; omega)
                (fun m hm => by
                  have hm' := mem_range.mp (mem_coe.mp hm)
                  have hmh : t - 1 + m < h := by dsimp only [t]; omega
                  dsimp only; split_ifs
                  dsimp only; omega)
            rw [hcard, card_range]
          rw [hA, hB]
    _ = t_off.val + 2 := by ring

private lemma cutEdges_layer_t4 {h : ℕ} (a_off : Fin (h - 2)) (p_off : Fin (a_off.val + 1))
    (f : Fin p_off.val → Bool) (k : Fin h) :
    ((cutEdges (CutCode.t4 a_off p_off f)).filter (fun e => e.1 = k)).card =
      if p_off.val = 0 then (if k.val = a_off.val + 1 then 4 else 0)
      else if k.val = a_off.val + 2 - p_off.val - 1 then 2
      else if k.val = a_off.val + 1 then 2
      else if a_off.val + 2 - p_off.val ≤ k.val ∧ k.val < a_off.val + 1 then 1 else 0 := by
  have ha_lt := a_off.isLt; have hp_le := Nat.lt_succ_iff.mp p_off.isLt
  rw [card_layer_cutEdges]
  simp only [cutR, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp only [card_univ_bool, card_empty, card_singleton] <;> omega

private lemma cutEdges_card_t4 {h : ℕ} (a_off : Fin (h - 2)) (p_off : Fin (a_off.val + 1))
    (f : Fin p_off.val → Bool) :
    (cutEdges (CutCode.t4 a_off p_off f)).card =
      if p_off.val = 0 then 4 else p_off.val + 3 := by
  rw [cutEdges_card_sum]
  have ha_lt : a_off.val + 2 < h := by have := a_off.isLt; omega
  have hp_le : p_off.val ≤ a_off.val := Nat.lt_succ_iff.mp p_off.isLt
  let a := a_off.val + 2
  let p := a - p_off.val
  by_cases hp0 : p_off.val = 0
  · simp only [hp0, ↓reduceIte]
    calc ∑ k : Fin h, ((cutEdges (CutCode.t4 a_off p_off f)).filter (fun e => e.1 = k)).card
        = ∑ k : Fin h, if k.val = a - 1 then 4 else 0 :=
            sum_congr rfl fun k _ => by
              rw [cutEdges_layer_t4 a_off p_off f k]
              simp only [hp0, ↓reduceIte]
              dsimp only [a]; simp only [show a_off.val + 2 - 1 = a_off.val + 1 by omega]
      _ = 4 := by
          have hunq : Finset.univ.filter (fun k : Fin h => k.val = a - 1) = {⟨a - 1, by omega⟩} := by
            ext k; simp [Fin.ext_iff]
          rw [← sum_filter, hunq, sum_singleton]
  · simp only [hp0, ↓reduceIte]
    have hsplit_sum : ∀ k : Fin h,
        (if k.val = p - 1 then 2 else if k.val = a - 1 then 2 else
          if p ≤ k.val ∧ k.val < a - 1 then 1 else 0) =
        (if k.val = p - 1 then 2 else 0) + (if k.val = a - 1 then 2 else 0) +
          (if p ≤ k.val ∧ k.val < a - 1 then 1 else 0) := by
      intro k
      split_ifs <;> omega
    calc ∑ k : Fin h, ((cutEdges (CutCode.t4 a_off p_off f)).filter (fun e => e.1 = k)).card
        = ∑ k : Fin h, ((if k.val = p - 1 then 2 else 0) + (if k.val = a - 1 then 2 else 0) +
            (if p ≤ k.val ∧ k.val < a - 1 then 1 else 0)) := by
            refine sum_congr rfl fun k _ => ?_
            rw [cutEdges_layer_t4 a_off p_off f k]
            simp only [hp0, ↓reduceIte]
            dsimp only [p, a]
            simp only [show a_off.val + 2 - 1 = a_off.val + 1 by omega]
            exact hsplit_sum k
      _ = 2 + 2 + (p_off.val - 1) := by
          rw [sum_add_distrib, sum_add_distrib]
          have hA : ∑ k : Fin h, (if k.val = p - 1 then 2 else 0) = 2 := by
            have hunq : Finset.univ.filter (fun k : Fin h => k.val = p - 1) = {⟨p - 1, by omega⟩} := by
              ext k; simp [Fin.ext_iff]
            rw [← sum_filter, hunq, sum_singleton]
          have hB : ∑ k : Fin h, (if k.val = a - 1 then 2 else 0) = 2 := by
            have hunq : Finset.univ.filter (fun k : Fin h => k.val = a - 1) = {⟨a - 1, by omega⟩} := by
              ext k; simp [Fin.ext_iff]
            rw [← sum_filter, hunq, sum_singleton]
          have hC : ∑ k : Fin h, (if p ≤ k.val ∧ k.val < a - 1 then 1 else 0) = p_off.val - 1 := by
            rw [← sum_filter, sum_const, smul_eq_mul, mul_one]
            have hcard : (Finset.univ.filter (fun k : Fin h => p ≤ k.val ∧ k.val < a - 1)).card =
                (Finset.range (p_off.val - 1)).card := by
              refine card_nbij' (fun k => k.val - p)
                (fun m => if hm : p + m < h then ⟨p + m, hm⟩ else ⟨0, by omega⟩)
                (fun k hk => by
                  dsimp only [p, a] at *
                  simp only [mem_coe, mem_filter, mem_univ, true_and] at hk
                  exact mem_coe.mpr (mem_range.mpr (by omega)))
                (fun m hm => by
                  have hm' := mem_range.mp (mem_coe.mp hm)
                  have hmh : p + m < h := by dsimp only [p, a]; omega
                  dsimp only; split_ifs
                  simp only [mem_coe, mem_filter, mem_univ, true_and]; dsimp only [p, a]; omega)
                (fun k hk => by
                  simp only [mem_coe, mem_filter, mem_univ, true_and] at hk
                  have hkh : p + (k.val - p) < h := by have := k.isLt; dsimp only [p, a] at *; omega
                  dsimp only; split_ifs
                  apply Fin.ext; dsimp only [p, a] at *; omega)
                (fun m hm => by
                  have hm' := mem_range.mp (mem_coe.mp hm)
                  have hmh : p + m < h := by dsimp only [p, a]; omega
                  dsimp only; split_ifs
                  dsimp only; omega)
            rw [hcard, card_range]
          rw [hA, hB, hC]
      _ = p_off.val + 3 := by omega

private lemma cutEdges_layer_t4_zero {h : ℕ} (a_off : Fin (h - 2)) (p_off : Fin (a_off.val + 1))
    (f : Fin p_off.val → Bool) (k0 : Fin h) (hk0 : k0.val = 0) :
    ((cutEdges (CutCode.t4 a_off p_off f)).filter (fun e => e.1 = k0)).card = 0 := by
  have hp := p_off.isLt
  rw [cutEdges_layer_t4, hk0]
  split_ifs <;> omega

private lemma cutEdges_layer_t4_above {h : ℕ} (a_off : Fin (h - 2)) (p_off : Fin (a_off.val + 1))
    (f : Fin p_off.val → Bool) (k : Fin h) (hk : a_off.val + 1 < k.val) :
    ((cutEdges (CutCode.t4 a_off p_off f)).filter (fun e => e.1 = k)).card = 0 := by
  rw [cutEdges_layer_t4]
  split_ifs <;> omega

private lemma cutEdges_layer_t4_at_a {h : ℕ} (a_off : Fin (h - 2)) (p_off : Fin (a_off.val + 1))
    (f : Fin p_off.val → Bool) (k : Fin h) (hk : k.val = a_off.val + 1) :
    ((cutEdges (CutCode.t4 a_off p_off f)).filter (fun e => e.1 = k)).card =
      if p_off.val = 0 then 4 else 2 := by
  have hp := p_off.isLt
  rw [cutEdges_layer_t4, hk]
  split_ifs <;> omega

private lemma cutEdges_inj {h : ℕ} (hh : 0 < h) (b1 : Bool) {c1 c2 : CutCode h}
    (hv1 : validCut h b1 c1 = true) (hv2 : validCut h b1 c2 = true)
    (heq : cutEdges c1 = cutEdges c2) : c1 = c2 := by
  have hl : ∀ k : Fin h, ((cutEdges c1).filter (fun e => e.1 = k)).card =
      ((cutEdges c2).filter (fun e => e.1 = k)).card := fun k => by rw [heq]
  have hlayer_ne0_t1 := @cutEdges_layer_t1 h
  have hlayer_t2 := @cutEdges_layer_t2 h
  have hlayer_t3 := @cutEdges_layer_t3 h
  have hlayer_t4 := @cutEdges_layer_t4 h
  -- Helper: layer membership characterizes cutR!
  let k0 : Fin h := ⟨0, hh⟩
  let kl : Fin h := ⟨h - 1, Nat.sub_lt hh Nat.one_pos⟩
  have hmem_t1 : ∀ f (k : Fin h) x y, (k, x, y) ∈ cutEdges (CutCode.t1 f) ↔
      x = f k.castSucc ∧ y = !(f k.succ) := by
    intro f k x y; rw [mem_cutEdges]; simp only [cutR, mem_singleton]
    cases y <;> cases f k.succ <;> simp
  cases c1 with
  | t1 f1 =>
    cases c2 with
    | t1 f2 =>
      congr 1; funext i
      refine Fin.lastCases ?_ ?_ i
      · have hex : (kl, f1 kl.castSucc, !(f1 kl.succ)) ∈ cutEdges (CutCode.t1 f1) :=
          (hmem_t1 f1 kl _ _).mpr ⟨rfl, rfl⟩
        rw [heq] at hex
        have h2 := (hmem_t1 f2 kl _ _).mp hex
        have hkl : kl.succ = Fin.last h := by apply Fin.ext; simp [kl]; omega
        rw [hkl] at h2
        have hb : (!(f1 (Fin.last h))) = !(f2 (Fin.last h)) := h2.2
        cases h1b : f1 (Fin.last h) <;> cases h2b : f2 (Fin.last h) <;>
          simp only [h1b, h2b, Bool.not_true, Bool.not_false] at hb <;> first | rfl | cases hb
      · intro j
        have hex : (j, f1 j.castSucc, !(f1 j.succ)) ∈ cutEdges (CutCode.t1 f1) :=
          (hmem_t1 f1 j _ _).mpr ⟨rfl, rfl⟩
        rw [heq] at hex
        exact ((hmem_t1 f2 j _ _).mp hex).1
    | t2 s2 f2 =>
      have hkl := hl kl
      rw [hlayer_ne0_t1, hlayer_t2] at hkl
      have hs := s2.isLt
      have hklv : kl.val = h - 1 := rfl
      rw [hklv] at hkl; split_ifs at hkl <;> omega
    | t3 t2 f2 =>
      have hk0 := hl k0
      rw [hlayer_ne0_t1, hlayer_t3] at hk0
      have ht := t2.isLt
      have hk0v : k0.val = 0 := rfl
      rw [hk0v] at hk0; split_ifs at hk0 <;> omega
    | t4 a2 p2 f2 =>
      have hk0 := hl k0
      rw [hlayer_ne0_t1, cutEdges_layer_t4_zero a2 p2 f2 k0 rfl] at hk0
      omega
  | t2 s1 f1 =>
    cases c2 with
    | t1 f2 =>
      have hkl := hl kl
      rw [hlayer_t2, hlayer_ne0_t1] at hkl
      have hs := s1.isLt
      have hklv : kl.val = h - 1 := rfl
      rw [hklv] at hkl; split_ifs at hkl <;> omega
    | t2 s2 f2 =>
      have hs_eq : s1 = s2 := by
        have h1 := hl ⟨s1.val, by have := s1.isLt; omega⟩
        rw [hlayer_t2, hlayer_t2] at h1
        apply Fin.ext
        dsimp only at h1
        split_ifs at h1 <;> omega
      subst hs_eq
      congr 1; funext j
      by_cases hj : j.val = s1.val
      · have hj_eq : j = ⟨s1.val, Nat.lt_succ_self s1.val⟩ := Fin.ext hj
        subst hj_eq
        have hex : (⟨s1.val, by have := s1.isLt; omega⟩, f1 ⟨s1.val, Nat.lt_succ_self _⟩, false) ∈
            cutEdges (CutCode.t2 s1 f1) := by
          rw [mem_cutEdges]; simp [cutR]
        rw [heq, mem_cutEdges] at hex
        simpa [cutR] using hex.1
      · have hj_lt : j.val < s1.val := by have := j.isLt; omega
        let kj : Fin h := ⟨j.val, by have := s1.isLt; omega⟩
        have hex : (kj, f1 j, !(f1 ⟨j.val + 1, by omega⟩)) ∈ cutEdges (CutCode.t2 s1 f1) := by
          rw [mem_cutEdges]; simp [cutR, kj, show j.val ≤ s1.val by omega,
            show j.val + 1 ≤ s1.val by omega]
        rw [heq, mem_cutEdges] at hex
        simpa [cutR, kj, show j.val ≤ s1.val by omega] using hex.1
    | t3 t2 f2 =>
      have hk0 := hl k0
      rw [hlayer_t2, hlayer_t3] at hk0
      have hs := s1.isLt; have ht := t2.isLt
      have hk0v : k0.val = 0 := rfl
      rw [hk0v] at hk0; split_ifs at hk0 <;> omega
    | t4 a2 p2 f2 =>
      have hk0 := hl k0
      rw [hlayer_t2, cutEdges_layer_t4_zero a2 p2 f2 k0 rfl] at hk0
      have hk0v : k0.val = 0 := rfl
      rw [hk0v] at hk0; split_ifs at hk0 <;> omega
  | t3 t1 f1 =>
    cases c2 with
    | t1 f2 =>
      have hk0 := hl k0
      rw [hlayer_t3, hlayer_ne0_t1] at hk0
      have ht := t1.isLt
      have hk0v : k0.val = 0 := rfl
      rw [hk0v] at hk0; split_ifs at hk0 <;> omega
    | t2 s2 f2 =>
      have hk0 := hl k0
      rw [hlayer_t3, hlayer_t2] at hk0
      have ht := t1.isLt; have hs := s2.isLt
      have hk0v : k0.val = 0 := rfl
      rw [hk0v] at hk0; split_ifs at hk0 <;> omega
    | t3 t2 f2 =>
      have ht_eq : t1 = t2 := by
        have ht1 := t1.isLt; have ht2 := t2.isLt
        have h1 := hl ⟨h - t1.val - 1, by omega⟩
        rw [hlayer_t3, hlayer_t3] at h1
        apply Fin.ext
        dsimp only at h1
        split_ifs at h1 <;> omega
      subst ht_eq
      congr 1; funext j
      have ht1 := t1.isLt
      rcases eq_or_lt_of_le (Nat.zero_le j.val) with hj0 | hjpos
      · have : j = 0 := Fin.ext hj0.symm
        subst this
        have hex : (⟨h - t1.val - 1, by omega⟩, false, !(f1 0)) ∈ cutEdges (CutCode.t3 t1 f1) := by
          rw [mem_cutEdges]
          simp [cutR, show h - t1.val - 1 < h - t1.val by omega,
            show ¬ h - t1.val - 1 + 1 < h - t1.val by omega,
            show h - t1.val - 1 + 1 - (h - t1.val) = 0 by omega]
        rw [heq, mem_cutEdges] at hex
        have hmem := hex.2
        simp [cutR, show ¬ h - t1.val - 1 + 1 < h - t1.val by omega,
          show h - t1.val - 1 + 1 - (h - t1.val) = 0 by omega] at hmem
        cases h1b : f1 0 <;> cases h2b : f2 0 <;>
          simp only [h1b, h2b, Bool.not_true, Bool.not_false, mem_singleton, Bool.false_eq_true] at hmem <;>
          first | rfl | exact absurd rfl hmem | contradiction
      · let kj : Fin h := ⟨h - t1.val + j.val - 1, by have := j.isLt; omega⟩
        have hkj1 : kj.castSucc.val = h - t1.val + (j.val - 1) := by
          rw [Fin.val_castSucc]; dsimp [kj]; omega
        have hkj2 : kj.succ.val = h - t1.val + j.val := by
          rw [Fin.val_succ]; dsimp [kj]; omega
        have hex : (kj, f1 ⟨j.val - 1, by omega⟩, !(f1 j)) ∈ cutEdges (CutCode.t3 t1 f1) := by
          rw [mem_cutEdges]
          simp only [cutR, hkj1, hkj2]
          rw [dif_neg (by omega), dif_neg (by omega)]
          simp only [mem_singleton]
          refine ⟨congrArg f1 (Fin.ext (by dsimp only; omega)), ?_⟩
          intro heqe
          rw [show (⟨h - t1.val + j.val - (h - t1.val), _⟩ : Fin (t1.val + 1)) = j by
            apply Fin.ext; dsimp only; omega] at heqe
          cases hf1 : f1 j <;> rw [hf1] at heqe <;> cases heqe
        rw [heq, mem_cutEdges] at hex
        have hmem := hex.2
        simp only [cutR, hkj2] at hmem
        rw [dif_neg (by omega)] at hmem
        rw [show (⟨h - t1.val + j.val - (h - t1.val), _⟩ : Fin (t1.val + 1)) = j by
          apply Fin.ext; dsimp only; omega] at hmem
        simp only [mem_singleton] at hmem
        cases h1b : f1 j <;> cases h2b : f2 j <;>
          simp only [h1b, h2b, Bool.not_true, Bool.not_false] at hmem
        all_goals first | rfl | exact absurd rfl hmem | contradiction
    | t4 a2 p2 f2 =>
      have hkl := hl kl
      rw [hlayer_t3, cutEdges_layer_t4_above a2 p2 f2 kl (by have := a2.isLt; dsimp [kl]; omega)] at hkl
      have ht := t1.isLt
      have hklv : kl.val = h - 1 := rfl
      rw [hklv] at hkl; split_ifs at hkl <;> omega
  | t4 a1 p1 f1 =>
    cases c2 with
    | t1 f2 =>
      have hk0 := hl k0
      rw [cutEdges_layer_t4_zero a1 p1 f1 k0 rfl, hlayer_ne0_t1] at hk0
      omega
    | t2 s2 f2 =>
      have hk0 := hl k0
      rw [cutEdges_layer_t4_zero a1 p1 f1 k0 rfl, hlayer_t2] at hk0
      have hs := s2.isLt
      have hk0v : k0.val = 0 := rfl
      rw [hk0v] at hk0; split_ifs at hk0 <;> omega
    | t3 t2 f2 =>
      have hkl := hl kl
      rw [cutEdges_layer_t4_above a1 p1 f1 kl (by have := a1.isLt; dsimp [kl]; omega), hlayer_t3] at hkl
      have ht := t2.isLt
      have hklv : kl.val = h - 1 := rfl
      rw [hklv] at hkl; split_ifs at hkl <;> omega
    | t4 a2 p2 f2 =>
      have ha1 := a1.isLt; have hp1 := p1.isLt
      have ha2 := a2.isLt; have hp2 := p2.isLt
      have ha_eq : a1 = a2 := by
        apply Fin.ext
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have h2 := hl ⟨a2.val + 1, by omega⟩
          rw [cutEdges_layer_t4_above a1 p1 f1 _ (by dsimp; omega),
              cutEdges_layer_t4_at_a a2 p2 f2 _ rfl] at h2
          split_ifs at h2 <;> omega
        · have h1 := hl ⟨a1.val + 1, by omega⟩
          rw [cutEdges_layer_t4_at_a a1 p1 f1 _ rfl,
              cutEdges_layer_t4_above a2 p2 f2 _ (by dsimp; omega)] at h1
          split_ifs at h1 <;> omega
      subst ha_eq
      have hp_eq : p1 = p2 := by
        apply Fin.ext
        by_cases h01 : p1.val = 0 <;> by_cases h02 : p2.val = 0
        · omega
        · have h1 := hl ⟨a1.val + 1, by omega⟩
          rw [cutEdges_layer_t4_at_a a1 p1 f1 _ rfl,
              cutEdges_layer_t4_at_a a1 p2 f2 _ rfl] at h1
          simp [h01, h02] at h1
        · have h1 := hl ⟨a1.val + 1, by omega⟩
          rw [cutEdges_layer_t4_at_a a1 p1 f1 _ rfl,
              cutEdges_layer_t4_at_a a1 p2 f2 _ rfl] at h1
          simp [h01, h02] at h1
        · have hcard := congrArg Finset.card heq
          rw [cutEdges_card_t4, cutEdges_card_t4] at hcard
          simp [h01, h02] at hcard
          omega
      subst hp_eq
      congr 1; funext j
      have hppos : 0 < p1.val := by have := j.isLt; omega
      let a := a1.val + 2
      let p := a - p1.val
      rcases eq_or_lt_of_le (Nat.zero_le j.val) with hj0 | hjpos
      · have : j = ⟨0, hppos⟩ := Fin.ext hj0.symm
        subst this
        have hex : (⟨p - 1, by omega⟩, false, !(f1 ⟨0, hppos⟩)) ∈ cutEdges (CutCode.t4 a1 p1 f1) := by
          rw [mem_cutEdges]
          simp [cutR, a, p, show p - 1 < p by omega, show ¬ p - 1 + 1 < p by omega,
            show p - 1 + 1 < a by omega, show p - 1 + 1 - p = 0 by omega]
        rw [heq, mem_cutEdges] at hex
        have hmem := hex.2
        simp [cutR, a, p, show ¬ p - 1 + 1 < p by omega, show p - 1 + 1 < a by omega,
          show p - 1 + 1 - p = 0 by omega] at hmem
        cases h1b : f1 ⟨0, hppos⟩ <;> cases h2b : f2 ⟨0, hppos⟩ <;>
          simp only [h1b, h2b, Bool.not_true, Bool.not_false] at hmem ⊢ <;>
          first | rfl | exact absurd hmem (by decide)
      · let kj : Fin h := ⟨p + j.val - 1, by have := j.isLt; omega⟩
        have hkj1 : kj.castSucc.val = p + j.val - 1 := by rw [Fin.val_castSucc]
        have hkj2 : kj.succ.val = p + j.val := by rw [Fin.val_succ]; dsimp [kj]; omega
        have hex : (kj, f1 ⟨j.val - 1, by omega⟩, !(f1 j)) ∈ cutEdges (CutCode.t4 a1 p1 f1) := by
          rw [mem_cutEdges]
          simp only [cutR, hkj1, hkj2]
          dsimp only [p, a]
          rw [dif_neg (by omega), dif_pos (by omega),
              dif_neg (by omega), dif_pos (by have := j.isLt; omega)]
          simp only [mem_singleton]
          refine ⟨congrArg f1 (Fin.ext (by dsimp [p, a]; omega)), ?_⟩
          intro heqe
          rw [show (⟨p + j.val - p, _⟩ : Fin p1.val) = j by apply Fin.ext; dsimp [p, a]; omega] at heqe
          cases hf1 : f1 j <;> rw [hf1] at heqe <;> cases heqe
        rw [heq, mem_cutEdges] at hex
        have hmem := hex.2
        simp only [cutR, hkj2] at hmem
        dsimp only [p, a] at hmem
        rw [dif_neg (by omega), dif_pos (by have := j.isLt; omega)] at hmem
        rw [show (⟨p + j.val - p, _⟩ : Fin p1.val) = j by apply Fin.ext; dsimp [p, a]; omega] at hmem
        simp only [mem_singleton] at hmem
        cases h1b : f1 j <;> cases h2b : f2 j <;>
          simp only [h1b, h2b, Bool.not_true, Bool.not_false] at hmem ⊢ <;>
          first | rfl | exact absurd hmem (by decide)

/-! Part 4: Exact cardinality and literal counts of CutCode -/

private lemma sum_t2_card (h : ℕ) (hh : 1 ≤ h) :
    ∑ s : Fin (h - 1), 2 ^ (s.val + 1) = 2 ^ h - 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hh
  induction m with
  | zero => simp
  | succ m ih =>
    have hih := ih (by omega)
    rw [show (m + 1) + 1 - 1 = (m + 1 - 1) + 1 by omega, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [show m + 1 - 1 = m by omega] at hih ⊢
    rw [hih, pow_succ]
    have hp : 2 ≤ 2 ^ (m + 1) := by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow; rw [pow_succ']; omega
    omega

private lemma sum_t2_lits (h : ℕ) (hh : 2 ≤ h) :
    ∑ s : Fin (h - 1), (s.val + 3) * 2 ^ (s.val + 1) = h * 2 ^ h - 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hh
  induction m with
  | zero => simp
  | succ m ih =>
    have hih := ih (by omega)
    rw [show (m + 2) + 1 - 1 = (m + 2 - 1) + 1 by omega, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [show m + 2 - 1 = m + 1 by omega] at hih ⊢
    rw [hih]
    have hp : 2 ≤ (m + 2) * 2 ^ (m + 2) := by
      have : 1 ≤ 2 ^ (m + 2) := Nat.one_le_two_pow; nlinarith
    zify [hp, show 2 ≤ (m + 2 + 1) * 2 ^ (m + 2 + 1) by
      have : 1 ≤ 2 ^ (m + 2 + 1) := Nat.one_le_two_pow; nlinarith]
    rw [show m + 1 + 1 = m + 2 by omega]
    push_cast; rw [pow_succ']; ring

private lemma sum_t4_inner_card (a : ℕ) :
    ∑ p : Fin (a + 1), 2 ^ p.val = 2 ^ (a + 1) - 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ]
    have : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
    omega

private lemma two_pow_ge_add_one (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ']; omega

private lemma sum_t4_card_aux (k : ℕ) :
    ∑ a : Fin k, ∑ p : Fin (a.val + 1), 2 ^ p.val = 2 ^ (k + 1) - (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, sum_t4_inner_card]
    have hp1 : k + 2 ≤ 2 ^ (k + 1) := two_pow_ge_add_one (k + 1)
    have hp2 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl, pow_succ]
    omega

private lemma sum_t4_card (h : ℕ) (hh : 2 ≤ h) :
    ∑ a : Fin (h - 2), ∑ p : Fin (a.val + 1), 2 ^ p.val = 2 ^ (h - 1) - h := by
  rw [sum_t4_card_aux (h - 2), show h - 2 + 1 = h - 1 by omega, show h - 2 + 2 = h by omega]

private lemma sum_t4_inner_lits (a : ℕ) :
    ∑ p : Fin (a + 1), (if p.val = 0 then 4 else p.val + 3) * 2 ^ p.val = (a + 2) * 2 ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, if_neg (Nat.succ_ne_zero a)]
    rw [pow_succ', pow_succ']
    ring

private lemma sum_t4_lits_aux (k : ℕ) :
    ∑ a : Fin k, ∑ p : Fin (a.val + 1), (if p.val = 0 then 4 else p.val + 3) * 2 ^ p.val =
      k * 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, sum_t4_inner_lits]
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl, pow_succ']
    ring

private lemma sum_t4_lits (h : ℕ) (hh : 3 ≤ h) :
    ∑ a : Fin (h - 2), ∑ p : Fin (a.val + 1), (if p.val = 0 then 4 else p.val + 3) * 2 ^ p.val =
      (h - 2) * 2 ^ (h - 1) := by
  rw [sum_t4_lits_aux (h - 2), show h - 2 + 1 = h - 1 by omega]

private def cutLitNum {h : ℕ} (b1 : Bool) : CutCode h → ℕ
  | .t1 _ => if b1 then h + 1 else h + 2
  | .t2 s _ => s.val + 3
  | .t3 t_off _ => t_off.val + 3
  | .t4 _ p_off _ => if p_off.val = 0 then 4 else p_off.val + 3

private lemma cut_counts (h : ℕ) (hh : 1 ≤ h) (b : ℕ) (hb : 0 < b) :
    let b1 := decide (b = 1)
    let U := Finset.univ.filter (fun c : CutCode h => validCut h b1 c = true)
    U.card = clCost b h ∧ (∑ c ∈ U, cutLitNum b1 c) = litCost b h := by
  intro b1 U
  -- Partition U into t1, t2, t3, t4!
  let S1 := (Finset.univ : Finset (Fin (h + 1) → Bool)).filter
      (fun f => if b1 then decide (f ⟨h, Nat.lt_succ_self h⟩ = !(f 0)) else true)
  let S2 := (Finset.univ : Finset (Σ s : Fin (h - 1), Fin (s.val + 1) → Bool))
  let S3 := (Finset.univ : Finset (Σ t_off : Fin (h - 1), Fin (t_off.val + 1) → Bool))
  let S4 := (Finset.univ : Finset (Σ a_off : Fin (h - 2), Σ p_off : Fin (a_off.val + 1), Fin p_off.val → Bool))
  have hS1_card : S1.card = if b1 then 2 ^ h else 2 ^ (h + 1) := by
    by_cases hb1 : b1 = true
    · rw [if_pos hb1]
      have hnb : S1.card = (Finset.univ : Finset (Fin h → Bool)).card := by
        refine card_nbij'
          (fun f (i : Fin h) => f i.castSucc)
          (fun g (i : Fin (h + 1)) => if hi : i.val < h then g ⟨i.val, hi⟩ else !(g ⟨0, hh⟩))
          (fun _ _ => mem_coe.mpr (mem_univ _))
          (fun g _ => by
            simp only [S1, mem_coe, mem_filter, mem_univ, true_and, hb1, ↓reduceIte,
              decide_eq_true_eq]
            have h0 : 0 < h := hh
            rw [Fin.val_zero, dif_neg (lt_irrefl h), dif_pos h0])
          (fun f hf => by
            simp only [S1, mem_coe, mem_filter, mem_univ, true_and, hb1, ↓reduceIte,
              decide_eq_true_eq] at hf
            funext i
            by_cases hi : i.val < h
            · simp [hi, Fin.castSucc]
            · have hi_eq : i = ⟨h, Nat.lt_succ_self h⟩ := Fin.ext (by dsimp; have := i.isLt; omega)
              subst hi_eq
              simp [hi, hf, Fin.castSucc])
          (fun g _ => by
            funext i; simp [i.isLt, Fin.castSucc])
      rw [hnb, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    · simp only [S1, hb1, ↓reduceIte, Bool.false_eq_true]
      simp
  let emb1 : (Fin (h + 1) → Bool) ↪ CutCode h :=
    ⟨CutCode.t1, fun _ _ h => by cases h; rfl⟩
  let emb2 : (Σ s : Fin (h - 1), Fin (s.val + 1) → Bool) ↪ CutCode h :=
    ⟨fun p => CutCode.t2 p.1 p.2, by rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h; cases h; rfl⟩
  let emb3 : (Σ t_off : Fin (h - 1), Fin (t_off.val + 1) → Bool) ↪ CutCode h :=
    ⟨fun p => CutCode.t3 p.1 p.2, by rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h; cases h; rfl⟩
  let emb4 : (Σ a_off : Fin (h - 2), Σ p_off : Fin (a_off.val + 1), Fin p_off.val → Bool) ↪ CutCode h :=
    ⟨fun p => CutCode.t4 p.1 p.2.1 p.2.2, by rintro ⟨a1, p1, f1⟩ ⟨a2, p2, f2⟩ h; cases h; rfl⟩
  have hU_eq : U = S1.map emb1 ∪ (S2.map emb2 ∪ (S3.map emb3 ∪ S4.map emb4)) := by
    ext c; cases c with
    | t1 f =>
      simp only [U, validCut, mem_filter, mem_univ, true_and, mem_union, mem_map,
        emb1, emb2, emb3, emb4, Function.Embedding.coeFn_mk]
      constructor
      · intro hf
        left; exact ⟨f, by simpa [S1] using hf, rfl⟩
      · rintro (⟨a, ha, he⟩ | ⟨⟨a, b⟩, _, he⟩ | ⟨⟨a, b⟩, _, he⟩ | ⟨⟨a, p, f'⟩, _, he⟩)
        · cases he; simpa [S1] using ha
        · cases he
        · cases he
        · cases he
    | t2 s f =>
      simp only [U, mem_filter, mem_univ, true_and, mem_union, mem_map,
        emb1, emb2, emb3, emb4, Function.Embedding.coeFn_mk]
      refine ⟨fun _ => Or.inr (Or.inl ⟨⟨s, f⟩, by simp [S2], rfl⟩), fun _ => by simp [validCut]⟩
    | t3 t f =>
      simp only [U, mem_filter, mem_univ, true_and, mem_union, mem_map,
        emb1, emb2, emb3, emb4, Function.Embedding.coeFn_mk]
      refine ⟨fun _ => Or.inr (Or.inr (Or.inl ⟨⟨t, f⟩, by simp [S3], rfl⟩)), fun _ => by simp [validCut]⟩
    | t4 a p f =>
      simp only [U, mem_filter, mem_univ, true_and, mem_union, mem_map,
        emb1, emb2, emb3, emb4, Function.Embedding.coeFn_mk]
      refine ⟨fun _ => Or.inr (Or.inr (Or.inr ⟨⟨a, p, f⟩, by simp [S4], rfl⟩)), fun _ => by simp [validCut]⟩
  have hdisj12 : Disjoint (S1.map emb1) (S2.map emb2 ∪ (S3.map emb3 ∪ S4.map emb4)) := by
    rw [disjoint_left]; intro c hc1 hc2; rcases hc2 with _
    simp only [mem_map, mem_union, emb1, emb2, emb3, emb4, Function.Embedding.coeFn_mk] at hc1 hc2
    rcases hc1 with ⟨_, _, rfl⟩
    rcases hc2 with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  have hdisj23 : Disjoint (S2.map emb2) (S3.map emb3 ∪ S4.map emb4) := by
    rw [disjoint_left]; intro c hc1 hc2
    simp only [mem_map, mem_union, emb2, emb3, emb4, Function.Embedding.coeFn_mk] at hc1 hc2
    rcases hc1 with ⟨_, _, rfl⟩
    rcases hc2 with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h
  have hdisj34 : Disjoint (S3.map emb3) (S4.map emb4) := by
    rw [disjoint_left]; intro c hc1 hc2
    simp only [mem_map, emb3, emb4, Function.Embedding.coeFn_mk] at hc1 hc2
    rcases hc1 with ⟨_, _, rfl⟩; rcases hc2 with ⟨_, _, h⟩; cases h
  have hS2_card : S2.card = 2 ^ h - 2 := by
    simp [S2, Fintype.card_sigma, Fintype.card_fun, sum_t2_card h hh]
  have hS3_card : S3.card = 2 ^ h - 2 := by
    simp [S3, Fintype.card_sigma, Fintype.card_fun, sum_t2_card h hh]
  have hS4_card : S4.card = if h ≤ 2 then 0 else 2 ^ (h - 1) - h := by
    by_cases hle : h ≤ 2
    · have hz : h - 2 = 0 := by omega
      simp [S4, hz, hle]
    · rw [if_neg hle]
      have hge2 : 2 ≤ h := by omega
      simp only [S4, card_univ, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool]
      exact sum_t4_card h hge2
  have hU_card : U.card = S1.card + S2.card + S3.card + S4.card := by
    rw [hU_eq, card_union_of_disjoint hdisj12, card_union_of_disjoint hdisj23,
        card_union_of_disjoint hdisj34, card_map, card_map, card_map, card_map]
    ring
  have hU_sum : ∑ c ∈ U, cutLitNum b1 c =
      (∑ f ∈ S1, (if b1 then h + 1 else h + 2)) +
      (∑ p ∈ S2, (p.1.val + 3)) +
      (∑ p ∈ S3, (p.1.val + 3)) +
      (∑ p ∈ S4, (if p.2.1.val = 0 then 4 else p.2.1.val + 3)) := by
    have hs1 : ∑ c ∈ S1.map emb1, cutLitNum b1 c = ∑ f ∈ S1, (if b1 then h + 1 else h + 2) := by
      rw [sum_map]; rfl
    have hs2 : ∑ c ∈ S2.map emb2, cutLitNum b1 c = ∑ p ∈ S2, (p.1.val + 3) := by
      rw [sum_map]; rfl
    have hs3 : ∑ c ∈ S3.map emb3, cutLitNum b1 c = ∑ p ∈ S3, (p.1.val + 3) := by
      rw [sum_map]; rfl
    have hs4 : ∑ c ∈ S4.map emb4, cutLitNum b1 c =
        ∑ p ∈ S4, (if p.2.1.val = 0 then 4 else p.2.1.val + 3) := by
      rw [sum_map]; rfl
    rw [hU_eq, sum_union hdisj12, sum_union hdisj23, sum_union hdisj34, hs1, hs2, hs3, hs4]
    ring
  have hS2_sum : ∑ p ∈ S2, (p.1.val + 3) = if h = 1 then 0 else h * 2 ^ h - 2 := by
    rcases eq_or_lt_of_le hh with rfl | hge2
    · simp [S2]
    · rw [if_neg (by omega)]
      simp only [S2, Fintype.sum_sigma, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool, smul_eq_mul]
      calc ∑ x : Fin (h - 1), 2 ^ (x.val + 1) * (x.val + 3)
          = ∑ x : Fin (h - 1), (x.val + 3) * 2 ^ (x.val + 1) :=
              sum_congr rfl fun _ _ => mul_comm _ _
        _ = h * 2 ^ h - 2 := sum_t2_lits h hge2
  have hS3_sum : ∑ p ∈ S3, (p.1.val + 3) = if h = 1 then 0 else h * 2 ^ h - 2 := by
    rcases eq_or_lt_of_le hh with rfl | hge2
    · simp [S3]
    · rw [if_neg (by omega)]
      simp only [S3, Fintype.sum_sigma, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool, smul_eq_mul]
      calc ∑ x : Fin (h - 1), 2 ^ (x.val + 1) * (x.val + 3)
          = ∑ x : Fin (h - 1), (x.val + 3) * 2 ^ (x.val + 1) :=
              sum_congr rfl fun _ _ => mul_comm _ _
        _ = h * 2 ^ h - 2 := sum_t2_lits h hge2
  have hS4_sum : ∑ p ∈ S4, (if p.2.1.val = 0 then 4 else p.2.1.val + 3) =
      if h ≤ 2 then 0 else (h - 2) * 2 ^ (h - 1) := by
    by_cases hle : h ≤ 2
    · have hz : h - 2 = 0 := by omega
      simp [S4, hz, hle]
    · rw [if_neg hle]
      simp only [S4, Fintype.sum_sigma, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool, smul_eq_mul]
      calc ∑ x : Fin (h - 2), ∑ y : Fin (x.val + 1),
              2 ^ y.val * (if y.val = 0 then 4 else y.val + 3)
          = ∑ x : Fin (h - 2), ∑ y : Fin (x.val + 1),
              (if y.val = 0 then 4 else y.val + 3) * 2 ^ y.val :=
              sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => mul_comm _ _
        _ = (h - 2) * 2 ^ (h - 1) := sum_t4_lits h (by omega)
  simp only [hU_card, hS1_card, hS2_card, hS3_card, hS4_card]
  simp only [hU_sum, sum_const, hS1_card, smul_eq_mul, hS2_sum, hS3_sum, hS4_sum]
  constructor
  · by_cases hb_eq1 : b = 1 <;> rcases eq_or_lt_of_le hh with rfl | hh2
    · simp [b1, hb_eq1, clCost]
    · simp only [b1, hb_eq1, decide_true, clCost, ↓reduceIte]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hh2) with rfl | hh3
      · simp
      · have hle2 : ¬ h ≤ 2 := by omega
        rw [if_neg hle2]
        have hp1 : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ', Nat.sub_add_cancel hh]
        have h4pow : 4 ≤ 2 ^ (h - 1) := by
          have : 2 ≤ h - 1 := by omega
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by omega) this
        have hle_h : h ≤ 2 ^ (h - 1) := by
          simpa [Nat.sub_add_cancel hh] using two_pow_ge_add_one (h - 1)
        have h2pow : 2 ≤ 2 * 2 ^ (h - 1) := by omega
        have hle_7 : h ≤ 7 * 2 ^ (h - 1) := by omega
        have h4_7 : 4 ≤ 7 * 2 ^ (h - 1) - h := by omega
        rw [hp1]
        zify [h2pow, hle_h, hle_7, h4_7]
        ring
    · simp [b1, hb_eq1, clCost]
    · simp only [b1, hb_eq1, decide_false, Bool.false_eq_true, clCost, ↓reduceIte]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hh2) with rfl | hh3
      · simp
      · have hle2 : ¬ h ≤ 2 := by omega
        rw [if_neg hle2]
        have hp1 : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ', Nat.sub_add_cancel hh]
        have hp2 : 2 ^ (h + 1) = 4 * 2 ^ (h - 1) := by rw [pow_succ', hp1]; ring
        have h4pow : 4 ≤ 2 ^ (h - 1) := by
          have : 2 ≤ h - 1 := by omega
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by omega) this
        have hle_h : h ≤ 2 ^ (h - 1) := by
          simpa [Nat.sub_add_cancel hh] using two_pow_ge_add_one (h - 1)
        have h2pow : 2 ≤ 2 * 2 ^ (h - 1) := by omega
        have hle_9 : h ≤ 9 * 2 ^ (h - 1) := by omega
        have h4_9 : 4 ≤ 9 * 2 ^ (h - 1) - h := by omega
        rw [hp1, hp2]
        zify [h2pow, hle_h, hle_9, h4_9]
        ring
  · by_cases hb_eq1 : b = 1 <;> rcases eq_or_lt_of_le hh with rfl | hh2
    · simp [b1, hb_eq1, litCost]
    · simp only [b1, hb_eq1, decide_true, litCost, ↓reduceIte, show h ≠ 1 by omega]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hh2) with rfl | hh3
      · simp
      · have hle2 : ¬ h ≤ 2 := by omega
        rw [if_neg hle2]
        have hp1 : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ', Nat.sub_add_cancel hh]
        have hge2 : 2 ≤ h * (2 * 2 ^ (h - 1)) := by
          have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow; nlinarith
        have h7 : 4 ≤ 7 * h * 2 ^ (h - 1) := by
          have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow; nlinarith
        rw [hp1]
        zify [show 2 ≤ h by omega, hge2, h7]
        ring
    · simp [b1, hb_eq1, litCost]
    · simp only [b1, hb_eq1, decide_false, Bool.false_eq_true, litCost, ↓reduceIte, show h ≠ 1 by omega]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hh2) with rfl | hh3
      · simp
      · have hle2 : ¬ h ≤ 2 := by omega
        rw [if_neg hle2]
        have hp1 : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ', Nat.sub_add_cancel hh]
        have hp2 : 2 ^ (h + 1) = 4 * 2 ^ (h - 1) := by rw [pow_succ', hp1]; ring
        have hge2 : 2 ≤ h * (2 * 2 ^ (h - 1)) := by
          have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow; nlinarith
        have h9 : 4 ≤ (9 * h + 6) * 2 ^ (h - 1) := by
          have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow; nlinarith
        rw [hp1, hp2]
        zify [show 2 ≤ h by omega, hge2, h9]
        ring

/-! Part 5: Turning CutCodes into Clauses of V and proving encoding + optimality -/

section CycleCNF

variable (n b : ℕ) (hn : 0 < n) (hb : 0 < b) (origin : Fin n) (gap : Fin b → ℕ)
  (hv : ValidGap n b gap)

abbrev VType (n b : ℕ) := Sum (Fin b) (Fin n × (Bool × Bool))

def cutBndLits (i : Fin b) (c : CutCode (gap i)) : Finset (Literal (VType n b)) :=
  (match cutReqU c with | some u0 => {(Sum.inl i, !u0)} | none => ∅) ∪
  (match cutReqV c with | some v0 => {(Sum.inl (nextGap b hb i), !v0)} | none => ∅)

def cutEdgeLits (i : Fin b) (c : CutCode (gap i)) : Finset (Literal (VType n b)) :=
  (cutEdges c).image (fun e => (Sum.inr (gapSite n b hn origin gap i e.1.val, e.2), true))

def toClause (i : Fin b) (c : CutCode (gap i)) : Clause (VType n b) :=
  cutBndLits n b hb gap i c ∪ cutEdgeLits n b hn origin gap i c

private lemma cutBndLits_card (i : Fin b) (c : CutCode (gap i))
    (hc : validCut (gap i) (decide (b = 1)) c = true) :
    (cutBndLits n b hb gap i c).card =
      match c with | .t1 _ => if b = 1 then 1 else 2 | .t2 _ _ => 1 | .t3 _ _ => 1 | .t4 _ _ _ => 0 := by
  by_cases hb1 : b = 1
  · subst hb1
    have hni : nextGap 1 hb i = i := Subsingleton.elim _ _
    cases c with
    | t1 f =>
      simp only [validCut, decide_true, ↓reduceIte, decide_eq_true_eq] at hc
      have hfu : (!(!(f ⟨gap i, Nat.lt_succ_self _⟩))) = !(f 0) := by
        rw [Bool.not_not, hc]
      simp [cutBndLits, cutReqU, cutReqV, hni, hfu]
    | t2 s f => simp [cutBndLits, cutReqU, cutReqV]
    | t3 t f => simp [cutBndLits, cutReqU, cutReqV]
    | t4 a p f => simp [cutBndLits, cutReqU, cutReqV]
  · have hni : nextGap b hb i ≠ i := by
      intro heq
      have hv_eq := congrArg Fin.val heq
      simp only [nextGap] at hv_eq
      by_cases hi : i.val + 1 < b
      · rw [Nat.mod_eq_of_lt hi] at hv_eq; omega
      · have hi_eq : i.val + 1 = b := by have := i.isLt; omega
        rw [hi_eq, Nat.mod_self] at hv_eq; omega
    cases c with
    | t1 f =>
      simp only [cutBndLits, cutReqU, cutReqV, hb1, ↓reduceIte]
      rw [card_union_of_disjoint]
      · simp
      · rw [disjoint_left]; intro x hx1 hx2
        simp only [mem_singleton] at hx1 hx2; rw [hx1] at hx2
        exact hni (Sum.inl.inj (congrArg Prod.fst hx2)).symm
    | t2 s f => simp [cutBndLits, cutReqU, cutReqV]
    | t3 t f => simp [cutBndLits, cutReqU, cutReqV]
    | t4 a p f => simp [cutBndLits, cutReqU, cutReqV]

private lemma cutEdgeLits_card (hv : ValidGap n b gap) (i : Fin b) (c : CutCode (gap i)) :
    (cutEdgeLits n b hn origin gap i c).card = (cutEdges c).card := by
  unfold cutEdgeLits
  rw [card_image_of_injective]
  intro e1 e2 he
  have h1 := Sum.inr.inj (congrArg Prod.fst he)
  have hfst := (Prod.ext_iff.mp h1).1
  have hsnd := (Prod.ext_iff.mp h1).2
  have he1 := gapSite_same_inj n b hn origin gap hv hfst
  exact Prod.ext he1 hsnd

private lemma toClause_card (hv : ValidGap n b gap) (i : Fin b) (c : CutCode (gap i))
    (hc : validCut (gap i) (decide (b = 1)) c = true) :
    (toClause n b hn hb origin gap i c).card = cutLitNum (decide (b = 1)) c := by
  unfold toClause
  rw [card_union_of_disjoint]
  · rw [cutBndLits_card n b hb gap i c hc, cutEdgeLits_card n b hn origin gap hv i c]
    cases c with
    | t1 f =>
      rw [cutEdges_card_t1]; simp only [cutLitNum]
      by_cases hb1 : b = 1 <;> simp [hb1] <;> ring
    | t2 s f => rw [cutEdges_card_t2]; simp [cutLitNum]; ring
    | t3 t f => rw [cutEdges_card_t3]; simp [cutLitNum]; ring
    | t4 a p f => rw [cutEdges_card_t4]; simp [cutLitNum]
  · rw [disjoint_left]; intro l hl1 hl2
    simp only [cutBndLits, cutEdgeLits, mem_union, mem_image] at hl1 hl2
    obtain ⟨e, _, rfl⟩ := hl2
    rcases hl1 with h | h <;> (split at h <;> simp at h)

private lemma toClause_inj (hv : ValidGap n b gap) :
    ∀ p1 p2 : Σ i : Fin b, { c : CutCode (gap i) // validCut (gap i) (decide (b = 1)) c = true },
      toClause n b hn hb origin gap p1.1 p1.2.val = toClause n b hn hb origin gap p2.1 p2.2.val →
      p1 = p2 := by
  rintro ⟨i1, ⟨c1, hv1⟩⟩ ⟨i2, ⟨c2, hv2⟩⟩ heq
  have hpos : (cutEdgeLits n b hn origin gap i1 c1) = cutEdgeLits n b hn origin gap i2 c2 := by
    have hf : ∀ i c, (toClause n b hn hb origin gap i c).filter (fun l => decide l.1.isRight) =
        cutEdgeLits n b hn origin gap i c := by
      intro i c; ext l; simp only [toClause, mem_filter, mem_union, cutBndLits, cutEdgeLits, mem_image]
      constructor
      · rintro ⟨h | ⟨e, he', rfl⟩, hr⟩
        · rcases h with hU | hV
          · split at hU <;> simp only [mem_singleton, notMem_empty] at hU
            subst hU; simp at hr
          · split at hV <;> simp only [mem_singleton, notMem_empty] at hV
            subst hV; simp at hr
        · exact ⟨e, he', rfl⟩
      · rintro ⟨e, he', rfl⟩; exact ⟨Or.inr ⟨e, he', rfl⟩, rfl⟩
    have := congrArg (fun C : Clause (VType n b) => C.filter fun l => decide l.1.isRight) heq
    rw [hf, hf] at this; exact this
  -- cutEdges is nonempty so an edge exists, forcing i1 = i2
  have hne1 : (cutEdges c1).Nonempty := by
    have hcard : 0 < (cutEdges c1).card := by
      cases c1 with
      | t1 => rw [cutEdges_card_t1]; exact hv.1 i1
      | t2 => rw [cutEdges_card_t2]; omega
      | t3 => rw [cutEdges_card_t3]; omega
      | t4 => rw [cutEdges_card_t4]; split_ifs <;> omega
    exact card_pos.mp hcard
  obtain ⟨e1, he1⟩ := hne1
  have hl1 : (Sum.inr (gapSite n b hn origin gap i1 e1.1.val, e1.2), true) ∈
      cutEdgeLits n b hn origin gap i1 c1 := mem_image_of_mem _ he1
  rw [hpos] at hl1
  obtain ⟨e2, _, he2⟩ := mem_image.mp hl1
  have hsite := (Prod.ext_iff.mp (Sum.inr.inj (congrArg Prod.fst he2))).1
  have hi_eq : i2 = i1 := gapSite_fst_eq n b hn origin gap hv hsite
  subst hi_eq
  have hce : cutEdges c1 = cutEdges c2 := by
    ext e; constructor <;> intro he
    · have hl : (Sum.inr (gapSite n b hn origin gap i2 e.1.val, e.2), true) ∈
          cutEdgeLits n b hn origin gap i2 c1 := mem_image_of_mem _ he
      rw [hpos] at hl; obtain ⟨e', he', heq'⟩ := mem_image.mp hl
      have hs := Prod.ext_iff.mp (Sum.inr.inj (congrArg Prod.fst heq'))
      have he1 := gapSite_same_inj n b hn origin gap hv hs.1
      have : e' = e := Prod.ext he1 hs.2
      subst this; exact he'
    · have hl : (Sum.inr (gapSite n b hn origin gap i2 e.1.val, e.2), true) ∈
          cutEdgeLits n b hn origin gap i2 c2 := mem_image_of_mem _ he
      rw [← hpos] at hl; obtain ⟨e', he', heq'⟩ := mem_image.mp hl
      have hs := Prod.ext_iff.mp (Sum.inr.inj (congrArg Prod.fst heq'))
      have he1 := gapSite_same_inj n b hn origin gap hv hs.1
      have : e' = e := Prod.ext he1 hs.2
      subst this; exact he'
  have hc_eq := cutEdges_inj (hv.1 i2) (decide (b = 1)) hv1 hv2 hce
  subst hc_eq; rfl

noncomputable def fullFormula (_ : ValidGap n b gap) : Finset (Clause (VType n b)) :=
  (Finset.univ : Finset (Σ i : Fin b, { c : CutCode (gap i) // validCut (gap i) (decide (b = 1)) c = true })).image
    (fun p => toClause n b hn hb origin gap p.1 p.2.val)

private lemma fullFormula_counts :
    (fullFormula n b hn hb origin gap hv).card = ∑ i, clCost b (gap i) ∧
    (∑ C ∈ fullFormula n b hn hb origin gap hv, C.card) = ∑ i, litCost b (gap i) := by
  unfold fullFormula
  rw [card_image_of_injective _ (toClause_inj n b hn hb origin gap hv),
      sum_image (fun x _ y _ h => toClause_inj n b hn hb origin gap hv x y h)]
  have h1 : (Finset.univ : Finset (Σ i : Fin b, { c : CutCode (gap i) // validCut (gap i) (decide (b = 1)) c = true })).card =
      ∑ i : Fin b, (Finset.univ.filter fun c : CutCode (gap i) => validCut (gap i) (decide (b = 1)) c = true).card := by
    rw [card_univ, Fintype.card_sigma]
    refine sum_congr rfl fun i _ => ?_
    rw [Fintype.card_subtype]
  have h2 : (∑ p : Σ i : Fin b, { c : CutCode (gap i) // validCut (gap i) (decide (b = 1)) c = true },
      (toClause n b hn hb origin gap p.1 p.2.val).card) =
      ∑ i : Fin b, ∑ c ∈ Finset.univ.filter (fun c : CutCode (gap i) => validCut (gap i) (decide (b = 1)) c = true),
        cutLitNum (decide (b = 1)) c := by
    rw [Fintype.sum_sigma]
    refine sum_congr rfl fun i _ => ?_
    let S := Finset.univ.filter (fun c : CutCode (gap i) => validCut (gap i) (decide (b = 1)) c = true)
    have hsub : (∑ c : {c : CutCode (gap i) // validCut (gap i) (decide (b = 1)) c = true},
        (toClause n b hn hb origin gap i c.val).card) =
        ∑ c ∈ S, (toClause n b hn hb origin gap i c).card :=
      (Finset.sum_subtype S
        (fun c => by simp [S] : ∀ c, c ∈ S ↔ validCut (gap i) (decide (b = 1)) c = true)
        (fun c => (toClause n b hn hb origin gap i c).card)).symm
    rw [hsub]
    refine sum_congr rfl fun c hc => ?_
    exact toClause_card n b hn hb origin gap hv i c (Finset.mem_filter.mp hc).2
  rw [h1, h2]
  constructor <;> refine sum_congr rfl fun i _ => ?_
  · exact (cut_counts (gap i) (hv.1 i) b hb).1
  · exact (cut_counts (gap i) (hv.1 i) b hb).2

-- Soundness and Completeness
private lemma cut_sound (hv : ValidGap n b gap) (i : Fin b) (c : CutCode (gap i)) (hc : validCut (gap i) (decide (b = 1)) c = true)
    (a : VType n b → Bool) (x : Fin n → Bool)
    (hx_edges : ∀ site : Fin n, a (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) = true)
    (hx_bnds : ∀ j : Fin b, x (posN n hn (gapStart n b origin gap j)) = a (Sum.inl j)) :
    ClauseSat a (toClause n b hn hb origin gap i c) := by
  let y : Fin (gap i + 1) → Bool := fun k => x (gapSite n b hn origin gap i k.val)
  have hy0 : y 0 = a (Sum.inl i) := by
    dsimp [y, gapSite]; exact hx_bnds i
  have hyh : y ⟨gap i, Nat.lt_succ_self (gap i)⟩ = a (Sum.inl (nextGap b hb i)) := by
    dsimp [y]; rw [gapSite_end n b hn hb origin gap hv i]; exact hx_bnds (nextGap b hb i)
  by_cases hU : match cutReqU c with | some u0 => y 0 ≠ u0 | none => False
  · cases hru : cutReqU c with
    | none => simp [hru] at hU
    | some u0 =>
      simp only [hru] at hU
      refine ⟨(Sum.inl i, !u0), mem_union_left _ (mem_union_left _ (by simp [cutBndLits, hru])), ?_⟩
      rw [← hy0]; cases h0 : y 0 <;> simp_all
  · by_cases hV : match cutReqV c with | some v0 => y ⟨gap i, Nat.lt_succ_self (gap i)⟩ ≠ v0 | none => False
    · cases hrv : cutReqV c with
      | none => simp [hrv] at hV
      | some v0 =>
        simp only [hrv] at hV
        refine ⟨(Sum.inl (nextGap b hb i), !v0), mem_union_left _ (mem_union_right _ (by simp [cutBndLits, hrv])), ?_⟩
        rw [← hyh]; cases hv0 : y ⟨gap i, Nat.lt_succ_self (gap i)⟩ <;> simp_all
    · -- Now y 0 ∈ cutR c 0 and ∃ m ≤ gap i, y m ∉ cutR c m
      have hstart : y 0 ∈ cutR c 0 := by
        cases c with
        | t1 f =>
          simp only [cutReqU] at hU; simp only [ne_eq, not_not] at hU
          simp [cutR, hU]
        | t2 s f =>
          simp only [cutReqU] at hU; simp only [ne_eq, not_not] at hU
          simp [cutR, hU]
        | t3 t f => simp [cutR, show 0 < gap i - t.val by have := t.isLt; omega]
        | t4 a0 p0 f => simp [cutR, show 0 < a0.val + 2 - p0.val by have := p0.isLt; omega]
      have hend : ∃ m : Fin (gap i + 1), y m ∉ cutR c m := by
        cases c with
        | t1 f =>
          refine ⟨⟨gap i, Nat.lt_succ_self _⟩, ?_⟩
          simp only [cutReqV] at hV; simp only [ne_eq, not_not] at hV
          simp [cutR, hV]
        | t2 s f =>
          refine ⟨⟨s.val + 1, by have := s.isLt; omega⟩, ?_⟩
          simp [cutR]
        | t3 t f =>
          refine ⟨⟨gap i, Nat.lt_succ_self _⟩, ?_⟩
          simp only [cutReqV] at hV; simp only [ne_eq, not_not] at hV
          have ht := t.isLt
          simp [cutR, show ¬ gap i < gap i - t.val by omega, hV,
            show gap i - (gap i - t.val) = t.val by omega]
        | t4 a0 p0 f =>
          refine ⟨⟨a0.val + 2, by have := a0.isLt; omega⟩, ?_⟩
          have hp := p0.isLt
          simp [cutR, show ¬ a0.val + 2 < a0.val + 2 - p0.val by omega]
      obtain ⟨m, hm⟩ := hend
      have hcross : ∃ k : Fin (gap i), y k.castSucc ∈ cutR c k.castSucc ∧ y k.succ ∉ cutR c k.succ := by
        induction m using Fin.induction with
        | zero => exact (hm hstart).elim
        | succ m' ih =>
          by_cases hm' : y m'.castSucc ∈ cutR c m'.castSucc
          · exact ⟨m', hm', hm⟩
          · exact ih hm'
      obtain ⟨k, hk1, hk2⟩ := hcross
      have he_mem : (k, y k.castSucc, y k.succ) ∈ cutEdges c := (mem_cutEdges c _).mpr ⟨hk1, hk2⟩
      refine ⟨(Sum.inr (gapSite n b hn origin gap i k.val, y k.castSucc, y k.succ), true),
        mem_union_right _ (mem_image_of_mem _ he_mem), ?_⟩
      change a (Sum.inr (gapSite n b hn origin gap i k.val, y k.castSucc, y k.succ)) = true
      have hs := hx_edges (gapSite n b hn origin gap i k.val)
      rw [gapSite_next] at hs
      exact hs

def reachLayer (i : Fin b) (a : VType n b → Bool) : Fin (gap i + 1) → Finset Bool :=
  Fin.induction {a (Sum.inl i)} (fun k prev =>
    Finset.univ.filter fun w => ∃ u ∈ prev, a (Sum.inr (gapSite n b hn origin gap i k.val, u, w)) = true)

private lemma reachLayer_spec (i : Fin b) (a : VType n b → Bool) :
    ∀ k : Fin (gap i + 1), ∀ w ∈ reachLayer n b hn origin gap i a k,
      ∃ path : Fin (k.val + 1) → Bool, path 0 = a (Sum.inl i) ∧
        path ⟨k.val, Nat.lt_succ_self k.val⟩ = w ∧
        ∀ j : Fin k.val, a (Sum.inr (gapSite n b hn origin gap i j.val,
          path ⟨j.val, by omega⟩, path ⟨j.val + 1, by omega⟩)) = true := by
  intro k
  induction k using Fin.induction with
  | zero =>
    intro w hw
    simp only [reachLayer, Fin.induction_zero, mem_singleton] at hw
    subst hw
    exact ⟨fun _ => a (Sum.inl i), rfl, rfl, fun j => Fin.elim0 j⟩
  | succ k ih =>
    intro w hw
    simp only [reachLayer, Fin.induction_succ, mem_filter, mem_univ, true_and] at hw
    obtain ⟨u, hu, he⟩ := hw
    obtain ⟨p0, hp0_0, hp0_last, hp0_e⟩ := ih u hu
    refine ⟨fun j => if hj : j.val ≤ k.val then p0 ⟨j.val, Nat.lt_succ_of_le hj⟩ else w, ?_, ?_, ?_⟩
    · simp [Nat.zero_le, hp0_0]
    · simp [show ¬ (k.val + 1) ≤ k.val by omega]
    · intro j
      have hjlt := j.isLt
      have hkc : k.castSucc.val = k.val := rfl
      have hks : k.succ.val = k.val + 1 := rfl
      by_cases hjk : j.val < k.val
      · simp only [show j.val ≤ k.val by omega, ↓reduceDIte, show j.val + 1 ≤ k.val by omega]
        exact hp0_e ⟨j.val, hjk⟩
      · have hjlt' : j.val < k.val + 1 := hjlt
        have hjeq : j.val = k.val := by omega
        simp only [show j.val ≤ k.val by omega, ↓reduceDIte, show ¬ j.val + 1 ≤ k.val by omega]
        have heq_last : p0 ⟨j.val, Nat.lt_succ_of_le (by omega)⟩ = u := by
          have : (⟨j.val, Nat.lt_succ_of_le (by omega)⟩ : Fin (k.castSucc.val + 1)) =
              ⟨k.castSucc.val, Nat.lt_succ_self k.castSucc.val⟩ := Fin.ext (by dsimp only; omega)
          rw [this, hp0_last]
        rw [heq_last, hjeq]; exact he

private lemma reach_empty_cut (hv : ValidGap n b gap) (i : Fin b) (a : VType n b → Bool)
    (hmiss : a (Sum.inl (nextGap b hb i)) ∉ reachLayer n b hn origin gap i a ⟨gap i, Nat.lt_succ_self _⟩) :
    ∃ c : CutCode (gap i), validCut (gap i) (decide (b = 1)) c = true ∧
      ¬ ClauseSat a (toClause n b hn hb origin gap i c) := by
  let R := reachLayer n b hn origin gap i a
  have hR0 : R 0 = {a (Sum.inl i)} := by simp [R, reachLayer]
  have hstep_false : ∀ (k : Fin (gap i)) x y,
      x ∈ R k.castSucc → y ∉ R k.succ →
      a (Sum.inr (gapSite n b hn origin gap i k.val, x, y)) = false := by
    intro k x y hx hy
    by_contra ht
    have htrue : a (Sum.inr (gapSite n b hn origin gap i k.val, x, y)) = true := by
      cases h : a (Sum.inr (gapSite n b hn origin gap i k.val, x, y)) <;> simp_all
    apply hy
    simp only [R, reachLayer, Fin.induction_succ, mem_filter, mem_univ, true_and]
    exact ⟨x, hx, htrue⟩
  have hfail_of_subset : ∀ c : CutCode (gap i), validCut (gap i) (decide (b = 1)) c = true →
      (∀ u0, cutReqU c = some u0 → u0 = a (Sum.inl i)) →
      (∀ v0, cutReqV c = some v0 → v0 = a (Sum.inl (nextGap b hb i))) →
      (∀ (k : Fin (gap i)) x y, x ∈ cutR c k.castSucc → y ∉ cutR c k.succ →
        x ∈ R k.castSucc ∧ y ∉ R k.succ) →
      ¬ ClauseSat a (toClause n b hn hb origin gap i c) := by
    intro c hc hU hV hcross ⟨l, hl, hla⟩
    simp only [toClause, cutBndLits, cutEdgeLits, mem_union, mem_image] at hl
    rcases hl with (hlU | hlV) | ⟨e, he, rfl⟩
    · cases hru : cutReqU c with
      | none => simp [hru] at hlU
      | some u0 =>
        simp only [hru, mem_singleton] at hlU; rw [hlU] at hla
        have := hU u0 hru; rw [this] at hla; cases a (Sum.inl i) <;> simp at hla
    · cases hrv : cutReqV c with
      | none => simp [hrv] at hlV
      | some v0 =>
        simp only [hrv, mem_singleton] at hlV; rw [hlV] at hla
        have := hV v0 hrv; rw [this] at hla
        cases a (Sum.inl (nextGap b hb i)) <;> simp at hla
    · have he' := (mem_cutEdges c e).mp he
      have ⟨h1, h2⟩ := hcross e.1 e.2.1 e.2.2 he'.1 he'.2
      have hfls := hstep_false e.1 e.2.1 e.2.2 h1 h2
      change a (Sum.inr (gapSite n b hn origin gap i e.1.val, e.2)) = true at hla
      rw [hfls] at hla; cases hla
  have hsingle : ∀ S : Finset Bool, S ≠ ∅ → S.card ≠ 2 → ∃ r : Bool, S = {r} := by
    intro S hne hc2
    have hle : S.card ≤ 2 := (card_le_univ S).trans (by rw [Fintype.card_bool])
    have hpos : 0 < S.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hne)
    exact card_eq_one.mp (by omega)
  have htwo : ∀ S : Finset Bool, S.card = 2 → S = Finset.univ := fun S hc2 =>
    eq_univ_of_card S (by rw [hc2, Fintype.card_bool])
  have hR_ne0 : R 0 ≠ ∅ := by rw [hR0]; exact singleton_ne_empty _
  have hR0_card : (R 0).card ≠ 2 := by rw [hR0, card_singleton]; omega
  let u := a (Sum.inl i)
  let v := a (Sum.inl (nextGap b hb i))
  have hb1_uv : decide (b = 1) = true → v = u := fun hb1 => by
    have hb_eq : b = 1 := decide_eq_true_eq.mp hb1
    have hni : nextGap b hb i = i := by
      have hi0 : i.val = 0 := by have := i.isLt; omega
      apply Fin.ext; simp [nextGap, hb_eq, hi0]
    dsimp [u, v]; rw [hni]
  by_cases hem : ∃ k : Fin (gap i + 1), R k = ∅
  · let Em := Finset.univ.filter (fun k : Fin (gap i + 1) => R k = ∅)
    have hEm : Em.Nonempty := let ⟨k, hk⟩ := hem; ⟨k, mem_filter.mpr ⟨mem_univ _, hk⟩⟩
    let k0 := Em.min' hEm
    have hk0_em : R k0 = ∅ := (mem_filter.mp (Em.min'_mem hEm)).2
    have hk0_pos : 0 < k0.val := by
      by_contra hle
      have hk0_z : k0 = 0 := Fin.ext (by change k0.val = 0; omega)
      rw [hk0_z] at hk0_em; exact hR_ne0 hk0_em
    have hprev_ne : ∀ j : Fin (gap i + 1), j.val < k0.val → R j ≠ ∅ := by
      intro j hj hje
      have hmem : j ∈ Em := mem_filter.mpr ⟨mem_univ _, hje⟩
      have := Em.min'_le j hmem
      change k0.val ≤ j.val at this; omega
    let Tw := Finset.univ.filter (fun p : Fin (gap i + 1) => p.val < k0.val ∧ (R p).card = 2)
    by_cases htw : Tw.Nonempty
    · let p := Tw.max' htw
      have hp_mem : p ∈ Tw := Tw.max'_mem htw
      simp only [Tw, mem_filter, mem_univ, true_and] at hp_mem
      have hp_pos : 0 < p.val := by
        by_contra hle
        have hp0 : p = 0 := Fin.ext (by change p.val = 0; omega)
        rw [hp0] at hp_mem; exact hR0_card hp_mem.2
      have hRp_univ : R p = Finset.univ := htwo _ hp_mem.2
      have haft_single : ∀ j : Fin (gap i + 1), p.val < j.val → j.val < k0.val →
          ∃ r : Bool, R j = {r} := by
        intro j h1 h2
        refine hsingle _ (hprev_ne j h2) ?_
        intro hc2
        have hmem : j ∈ Tw := mem_filter.mpr ⟨mem_univ _, h2, hc2⟩
        have := Tw.le_max' j hmem
        change j.val ≤ p.val at this; omega
      by_cases hk0_last : k0.val = gap i
      · -- CutCode.t3 with t = p + 1
        have hp_lt_h : p.val < gap i := by omega
        let t_off : Fin (gap i - 1) := ⟨gap i - (p.val + 1), by omega⟩
        have ht_val : gap i - t_off.val = p.val + 1 := by dsimp [t_off]; omega
        let f : Fin (t_off.val + 1) → Bool := fun j =>
          if hj : p.val + 1 + j.val < gap i then
            Classical.choose (haft_single ⟨p.val + 1 + j.val, by omega⟩ (by dsimp; omega) (by dsimp; omega))
          else !v
        have hf_last : f ⟨t_off.val, Nat.lt_succ_self _⟩ = !v := by
          have hnot : ¬ p.val + 1 + t_off.val < gap i := by dsimp [t_off]; omega
          dsimp only [f]; rw [dif_neg hnot]
        have hf_mem : ∀ j : Fin (t_off.val + 1), p.val + 1 + j.val < gap i →
            R ⟨p.val + 1 + j.val, by omega⟩ = {f j} := by
          intro j hj
          have hch := Classical.choose_spec (haft_single ⟨p.val + 1 + j.val, by omega⟩ (by dsimp; omega) (by dsimp; omega))
          simpa [f, hj] using hch
        refine ⟨CutCode.t3 t_off f, by simp [validCut], hfail_of_subset (CutCode.t3 t_off f) (by simp [validCut])
          (by intro _ h; simp [cutReqU] at h)
          (by intro v0 h; simp only [cutReqV, Option.some.injEq] at h
              rw [← h, hf_last, Bool.not_not]) ?_⟩
        intro k x y hx hy
        by_cases hkt : k.val < p.val + 1
        · by_cases hkp : k.val = p.val
          · have hke : k.castSucc = p := Fin.ext hkp
            have hks : k.succ = ⟨p.val + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
            have hsubL : x ∈ R k.castSucc := by rw [hke, hRp_univ]; exact mem_univ _
            refine ⟨hsubL, ?_⟩
            by_cases hp1 : p.val + 1 < gap i
            · have hR1 := hf_mem 0 hp1
              simp only [Fin.val_zero, Nat.add_zero] at hR1
              rw [hks, hR1]
              have hcy : cutR (CutCode.t3 t_off f) k.succ = {f 0} := by
                simp only [cutR, ht_val, Fin.val_succ]
                rw [dif_neg (by omega)]
                congr 1; exact congrArg f (Fin.ext (by dsimp; omega))
              rw [hcy] at hy; exact hy
            · have hks_end : k.succ = k0 := Fin.ext (by change k.val + 1 = k0.val; omega)
              rw [hks_end, hk0_em]; exact notMem_empty _
          · exfalso
            simp only [cutR, ht_val, Fin.val_succ] at hy
            rw [dif_pos (by omega)] at hy
            exact absurd (mem_univ y) hy
        · have hle : p.val + 1 ≤ k.val := by omega
          have hmemL : cutR (CutCode.t3 t_off f) k.castSucc =
              {f ⟨k.val - (p.val + 1), by omega⟩} := by
            simp only [cutR, ht_val, Fin.val_castSucc]
            rw [dif_neg (by omega)]
          rw [hmemL, mem_singleton] at hx; subst hx
          have hLx : R k.castSucc = {f ⟨k.val - (p.val + 1), by omega⟩} := by
            have hk_lt : p.val + 1 + (k.val - (p.val + 1)) < gap i := by omega
            have h1 := hf_mem ⟨k.val - (p.val + 1), by omega⟩ hk_lt
            have hke : k.castSucc = ⟨p.val + 1 + (k.val - (p.val + 1)), by omega⟩ :=
              Fin.ext (by simp only [Fin.val_castSucc]; omega)
            rw [hke, h1]
          refine ⟨by rw [hLx]; exact mem_singleton_self _, ?_⟩
          by_cases hk_end : k.val + 1 < gap i
          · have hR1 := hf_mem ⟨k.val + 1 - (p.val + 1), by dsimp [t_off]; omega⟩ (by dsimp [t_off]; omega)
            have hks : k.succ = ⟨p.val + 1 + (k.val + 1 - (p.val + 1)), by omega⟩ :=
              Fin.ext (by simp only [Fin.val_succ]; omega)
            have hmemR : cutR (CutCode.t3 t_off f) k.succ =
                {f ⟨k.val + 1 - (p.val + 1), by omega⟩} := by
              simp only [cutR, ht_val, Fin.val_succ]
              rw [dif_neg (by omega)]
            rw [hmemR] at hy
            rw [hks, hR1]; exact hy
          · have hks_end : k.succ = k0 := Fin.ext (by change k.val + 1 = k0.val; omega)
            rw [hks_end, hk0_em]; exact notMem_empty _
      · -- CutCode.t4 with a = k0, p_t4 = p + 1
        have hk0_lt_h : k0.val < gap i := by have := k0.isLt; omega
        have ha_pos : 2 ≤ k0.val := by omega
        let a_off : Fin (gap i - 2) := ⟨k0.val - 2, by omega⟩
        let p_off : Fin (a_off.val + 1) := ⟨k0.val - (p.val + 1), by dsimp [a_off]; omega⟩
        have ha_eq : a_off.val + 2 = k0.val := by dsimp [a_off]; omega
        have hp_eq : a_off.val + 2 - p_off.val = p.val + 1 := by dsimp [a_off, p_off]; omega
        let f : Fin p_off.val → Bool := fun j =>
          Classical.choose (haft_single ⟨p.val + 1 + j.val, by omega⟩ (by dsimp; omega) (by dsimp [p_off] at j; have := j.isLt; dsimp; omega))
        have hf_mem : ∀ j : Fin p_off.val, R ⟨p.val + 1 + j.val, by omega⟩ = {f j} := fun j =>
          Classical.choose_spec (haft_single ⟨p.val + 1 + j.val, by omega⟩ (by dsimp; omega) (by dsimp [p_off] at j; have := j.isLt; dsimp; omega))
        refine ⟨CutCode.t4 a_off p_off f, by simp [validCut], hfail_of_subset (CutCode.t4 a_off p_off f) (by simp [validCut])
          (by intro _ h; simp [cutReqU] at h) (by intro _ h; simp [cutReqV] at h) ?_⟩
        intro k x y hx hy
        by_cases hltp : k.val < p.val
        · exfalso
          simp only [cutR, ha_eq, hp_eq, Fin.val_succ] at hy
          rw [dif_pos (by omega)] at hy
          exact absurd (mem_univ y) hy
        · by_cases hgt : k0.val ≤ k.val
          · exfalso
            simp only [cutR, ha_eq, hp_eq, Fin.val_succ] at hy
            rw [dif_neg (by omega), dif_neg (by omega), if_neg (by omega)] at hy
            exact absurd (mem_univ y) hy
          · by_cases hkp : k.val = p.val
            · have hke : k.castSucc = p := Fin.ext hkp
              refine ⟨by rw [hke, hRp_univ]; exact mem_univ _, ?_⟩
              by_cases hp0 : p_off.val = 0
              · have hks : k.succ = k0 := Fin.ext (by change k.val + 1 = k0.val; dsimp [p_off] at hp0; omega)
                rw [hks, hk0_em]; exact notMem_empty _
              · have hRp1 := hf_mem ⟨0, Nat.pos_of_ne_zero hp0⟩
                have hmemR : cutR (CutCode.t4 a_off p_off f) k.succ =
                    {f ⟨0, Nat.pos_of_ne_zero hp0⟩} := by
                  simp only [cutR, ha_eq, hp_eq, Fin.val_succ]
                  rw [dif_neg (by omega), dif_pos (by omega)]
                  congr 1; exact congrArg f (Fin.ext (by dsimp; omega))
                rw [hmemR] at hy
                have hks : k.succ = ⟨p.val + 1 + 0, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
                rw [hks, hRp1]; exact hy
            · -- p + 1 ≤ k.val < k0.val
              have hmemL : cutR (CutCode.t4 a_off p_off f) k.castSucc =
                  {f ⟨k.val - (p.val + 1), by dsimp [p_off]; omega⟩} := by
                simp only [cutR, ha_eq, hp_eq, Fin.val_castSucc]
                rw [dif_neg (by omega), dif_pos (by omega)]
                congr 1; exact congrArg f (Fin.ext (by dsimp [a_off, p_off]; omega))
              rw [hmemL, mem_singleton] at hx; subst hx
              have hLk := hf_mem ⟨k.val - (p.val + 1), by dsimp [p_off]; omega⟩
              have hkl_eq : k.castSucc = ⟨p.val + 1 + (k.val - (p.val + 1)), by omega⟩ :=
                Fin.ext (by simp only [Fin.val_castSucc]; omega)
              refine ⟨by rw [hkl_eq, hLk]; exact mem_singleton_self _, ?_⟩
              by_cases hk_last : k.val + 1 = k0.val
              · have hks : k.succ = k0 := Fin.ext hk_last
                rw [hks, hk0_em]; exact notMem_empty _
              · have hRk1 := hf_mem ⟨k.val + 1 - (p.val + 1), by dsimp [p_off]; omega⟩
                have hmemR : cutR (CutCode.t4 a_off p_off f) k.succ =
                    {f ⟨k.val + 1 - (p.val + 1), by dsimp [p_off]; omega⟩} := by
                  simp only [cutR, ha_eq, hp_eq, Fin.val_succ]
                  rw [dif_neg (by omega), dif_pos (by omega)]
                  congr 1; exact congrArg f (Fin.ext (by dsimp [a_off, p_off]; omega))
                rw [hmemR] at hy
                have hks : k.succ = ⟨p.val + 1 + (k.val + 1 - (p.val + 1)), by omega⟩ :=
                  Fin.ext (by simp only [Fin.val_succ]; omega)
                rw [hks, hRk1]; exact hy
    · -- No card 2 below k0
      have hall_single : ∀ j : Fin (gap i + 1), j.val < k0.val → ∃ r : Bool, R j = {r} := by
        intro j hj
        refine hsingle _ (hprev_ne j hj) ?_
        intro hc2
        exact htw ⟨j, mem_filter.mpr ⟨mem_univ _, hj, hc2⟩⟩
      by_cases hk0_last : k0.val = gap i
      · -- CutCode.t1 with f j = r_j (j < h), f h = !v
        let f : Fin (gap i + 1) → Bool := fun j =>
          if hj : j.val < gap i then Classical.choose (hall_single j (by omega)) else !v
        have hf0 : f 0 = u := by
          have hch := Classical.choose_spec (hall_single 0 hk0_pos)
          have h0 : (0 : Fin (gap i + 1)).val < gap i := hv.1 i
          have hf0eq : f 0 = Classical.choose (hall_single 0 hk0_pos) := by
            dsimp only [f]; rw [dif_pos h0]
          rw [hf0eq]
          exact singleton_inj.mp (hch.symm.trans hR0)
        have hfl : f ⟨gap i, Nat.lt_succ_self _⟩ = !v := by
          dsimp only [f]; rw [dif_neg (lt_irrefl _)]
        have hf_valid : validCut (gap i) (decide (b = 1)) (CutCode.t1 f) = true := by
          simp only [validCut]
          split_ifs with hb1
          · rw [decide_eq_true_eq, hfl, hf0, hb1_uv hb1]
          · rfl
        refine ⟨CutCode.t1 f, hf_valid, hfail_of_subset (CutCode.t1 f) hf_valid
          (by intro u0 h; simp only [cutReqU, Option.some.injEq] at h; rw [← h, hf0])
          (by intro v0 h; simp only [cutReqV, Option.some.injEq] at h; rw [← h, hfl, Bool.not_not])
          ?_⟩
        intro k x y hx hy
        simp only [cutR] at hx hy
        rw [mem_singleton] at hx; subst hx
        have hLk : R k.castSucc = {f k.castSucc} := by
          have hklt : k.castSucc.val < gap i := k.isLt
          have hch := Classical.choose_spec (hall_single k.castSucc (by change k.val < k0.val; omega))
          have hfk : f k.castSucc = Classical.choose (hall_single k.castSucc (by change k.val < k0.val; omega)) := by
            dsimp only [f]; rw [dif_pos hklt]
          rw [hfk]; exact hch
        refine ⟨by rw [hLk]; exact mem_singleton_self _, ?_⟩
        by_cases hkl : k.val + 1 < gap i
        · have hRk : R k.succ = {f k.succ} := by
            have hch := Classical.choose_spec (hall_single k.succ (by change k.val + 1 < k0.val; omega))
            have hfk : f k.succ = Classical.choose (hall_single k.succ (by change k.val + 1 < k0.val; omega)) := by
              dsimp only [f]; rw [dif_pos (by change k.val + 1 < gap i; exact hkl)]
            rw [hfk]; exact hch
          rw [hRk]; exact hy
        · have hks : k.succ = k0 := Fin.ext (by change k.val + 1 = k0.val; omega)
          rw [hks, hk0_em]; exact notMem_empty _
      · -- CutCode.t2 with s = k0 - 1
        have hs_lt : k0.val - 1 < gap i - 1 := by have := k0.isLt; omega
        let s : Fin (gap i - 1) := ⟨k0.val - 1, hs_lt⟩
        let f : Fin (s.val + 1) → Bool := fun j =>
          Classical.choose (hall_single ⟨j.val, by have := k0.isLt; omega⟩ (by dsimp [s] at j; have := j.isLt; dsimp; omega))
        have hf0 : f 0 = u := by
          have hch := Classical.choose_spec (hall_single ⟨0, by have := k0.isLt; omega⟩ (by dsimp; exact hk0_pos))
          exact singleton_inj.mp (hch.symm.trans hR0)
        have hf_mem : ∀ j : Fin (s.val + 1), R ⟨j.val, by have := k0.isLt; omega⟩ = {f j} :=
          fun j => Classical.choose_spec (hall_single ⟨j.val, by have := k0.isLt; omega⟩ (by dsimp [s] at j; have := j.isLt; dsimp; omega))
        refine ⟨CutCode.t2 s f, by simp [validCut], hfail_of_subset (CutCode.t2 s f) (by simp [validCut])
          (by intro u0 h; simp only [cutReqU, Option.some.injEq] at h; rw [← h, hf0])
          (by intro _ h; simp [cutReqV] at h) ?_⟩
        intro k x y hx hy
        by_cases hks : k.val ≤ s.val
        · have hmemL : cutR (CutCode.t2 s f) k.castSucc = {f ⟨k.val, Nat.lt_succ_of_le hks⟩} := by
            simp only [cutR, Fin.val_castSucc]; rw [dif_pos hks]
          rw [hmemL, mem_singleton] at hx; subst hx
          have hLk := hf_mem ⟨k.val, Nat.lt_succ_of_le hks⟩
          refine ⟨by change f _ ∈ R ⟨k.val, _⟩; rw [hLk]; exact mem_singleton_self _, ?_⟩
          by_cases hkeq : k.val = s.val
          · have hkend : k.succ = k0 := Fin.ext (by change k.val + 1 = k0.val; dsimp [s] at hkeq; omega)
            rw [hkend, hk0_em]; exact notMem_empty _
          · have hmemR : cutR (CutCode.t2 s f) k.succ = {f ⟨k.val + 1, by omega⟩} := by
              simp only [cutR, Fin.val_succ]; rw [dif_pos (by omega)]
            rw [hmemR] at hy
            have hRk := hf_mem ⟨k.val + 1, by omega⟩
            have hks_eq : k.succ = ⟨(⟨k.val + 1, by omega⟩ : Fin (s.val + 1)).val, by have := k0.isLt; omega⟩ :=
              Fin.ext rfl
            rw [hks_eq, hRk]; exact hy
        · exfalso
          simp only [cutR, Fin.val_succ] at hy
          rw [dif_neg (by omega), if_neg (by omega)] at hy
          exact absurd (mem_univ y) hy
  · -- Case B: NO empty layer!
    have hne_all : ∀ k : Fin (gap i + 1), R k ≠ ∅ := fun k h => hem ⟨k, h⟩
    have hRh_single : R ⟨gap i, Nat.lt_succ_self _⟩ = {!v} := by
      have hc := hsingle _ (hne_all ⟨gap i, Nat.lt_succ_self _⟩) (fun hc2 =>
        hmiss (by change a (Sum.inl (nextGap b hb i)) ∈ R ⟨gap i, Nat.lt_succ_self _⟩; rw [htwo _ hc2]; exact mem_univ _))
      obtain ⟨r, hr⟩ := hc
      have hne : r ≠ v := fun h => hmiss (by change a (Sum.inl (nextGap b hb i)) ∈ R ⟨gap i, Nat.lt_succ_self _⟩; rw [hr, h]; exact mem_singleton_self _)
      have : r = !v := by
        revert hne; generalize (v : Bool) = vb; intro hne
        cases r <;> cases vb <;> first | rfl | exact absurd rfl hne
      rwa [← this]
    let Tw := Finset.univ.filter (fun p : Fin (gap i + 1) => (R p).card = 2)
    by_cases htw : Tw.Nonempty
    · let p := Tw.max' htw
      have hp_mem : p ∈ Tw := Tw.max'_mem htw
      simp only [Tw, mem_filter, mem_univ, true_and] at hp_mem
      have hp_pos : 0 < p.val := by
        by_contra hle
        have hp0 : p = 0 := Fin.ext (by change p.val = 0; omega)
        rw [hp0] at hp_mem; exact hR0_card hp_mem
      have hp_lt_h : p.val < gap i := by
        by_contra hge
        have hplt : p.val < gap i + 1 := p.isLt
        have hph : p = ⟨gap i, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp only; omega)
        rw [hph, hRh_single, card_singleton] at hp_mem; omega
      have hRp_univ : R p = Finset.univ := htwo _ hp_mem
      have hafter : ∀ j : Fin (gap i + 1), p.val < j.val → ∃ r : Bool, R j = {r} := by
        intro j hj
        refine hsingle _ (hne_all j) ?_
        intro hc2
        have := Tw.le_max' j (mem_filter.mpr ⟨mem_univ _, hc2⟩)
        change j.val ≤ p.val at this; omega
      let t_off : Fin (gap i - 1) := ⟨gap i - (p.val + 1), by omega⟩
      have ht_val : gap i - t_off.val = p.val + 1 := by dsimp [t_off]; omega
      let f : Fin (t_off.val + 1) → Bool := fun j =>
        Classical.choose (hafter ⟨p.val + 1 + j.val, by dsimp [t_off] at j; have := j.isLt; omega⟩ (by dsimp; omega))
      have hf_mem : ∀ j : Fin (t_off.val + 1),
          R ⟨p.val + 1 + j.val, by dsimp [t_off] at j; have := j.isLt; omega⟩ = {f j} := fun j =>
        Classical.choose_spec (hafter ⟨p.val + 1 + j.val, by dsimp [t_off] at j; have := j.isLt; omega⟩ (by dsimp; omega))
      have hf_last : f ⟨t_off.val, Nat.lt_succ_self _⟩ = !v := by
        have h1 := hf_mem ⟨t_off.val, Nat.lt_succ_self _⟩
        have heq_last : (⟨p.val + 1 + t_off.val, by dsimp [t_off]; omega⟩ : Fin (gap i + 1)) =
            ⟨gap i, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp [t_off]; omega)
        rw [heq_last, hRh_single] at h1
        exact singleton_inj.mp h1.symm
      refine ⟨CutCode.t3 t_off f, by simp [validCut], hfail_of_subset _ (by simp [validCut])
        (by intro _ h; simp [cutReqU] at h)
        (by intro v0 h; simp only [cutReqV, Option.some.injEq] at h; rw [← h, hf_last, Bool.not_not])
        ?_⟩
      intro k x y hx hy
      by_cases hkt : k.val < p.val + 1
      · by_cases hkp : k.val = p.val
        · have hke : k.castSucc = p := Fin.ext hkp
          have hmemR : cutR (CutCode.t3 t_off f) k.succ = {f 0} := by
            simp only [cutR, ht_val, Fin.val_succ]
            rw [dif_neg (by omega)]
            congr 1; exact congrArg f (Fin.ext (by dsimp; omega))
          rw [hmemR] at hy
          have hR1 := hf_mem 0
          simp only [Fin.val_zero, Nat.add_zero] at hR1
          have hks : k.succ = ⟨p.val + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
          rw [hke, hRp_univ, hks, hR1]
          exact ⟨mem_univ _, hy⟩
        · exfalso
          simp only [cutR, ht_val, Fin.val_succ] at hy
          rw [dif_pos (by omega)] at hy
          exact absurd (mem_univ y) hy
      · have hmemL : cutR (CutCode.t3 t_off f) k.castSucc = {f ⟨k.val - (p.val + 1), by omega⟩} := by
          simp only [cutR, ht_val, Fin.val_castSucc]
          rw [dif_neg (by omega)]
        rw [hmemL, mem_singleton] at hx; subst hx
        have hLk := hf_mem ⟨k.val - (p.val + 1), by omega⟩
        have hkl : k.castSucc = ⟨p.val + 1 + (k.val - (p.val + 1)), by omega⟩ :=
          Fin.ext (by simp only [Fin.val_castSucc]; omega)
        have hmemR : cutR (CutCode.t3 t_off f) k.succ = {f ⟨k.val + 1 - (p.val + 1), by omega⟩} := by
          simp only [cutR, ht_val, Fin.val_succ]
          rw [dif_neg (by omega)]
        rw [hmemR] at hy
        have hRk := hf_mem ⟨k.val + 1 - (p.val + 1), by omega⟩
        have hks : k.succ = ⟨p.val + 1 + (k.val + 1 - (p.val + 1)), by omega⟩ :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [hkl, hLk, hks, hRk]
        exact ⟨mem_singleton_self _, hy⟩
    · -- No layer has card 2 -> CutCode.t1
      have hall_single : ∀ j : Fin (gap i + 1), ∃ r : Bool, R j = {r} := fun j =>
        hsingle _ (hne_all j) fun hc2 => htw ⟨j, mem_filter.mpr ⟨mem_univ _, hc2⟩⟩
      let f : Fin (gap i + 1) → Bool := fun j => Classical.choose (hall_single j)
      have hf_mem : ∀ j : Fin (gap i + 1), R j = {f j} := fun j => Classical.choose_spec (hall_single j)
      have hf0 : f 0 = u := by have := hf_mem 0; rw [hR0] at this; exact singleton_inj.mp this.symm
      have hfl : f ⟨gap i, Nat.lt_succ_self _⟩ = !v := by
        have := hf_mem ⟨gap i, Nat.lt_succ_self _⟩
        rw [hRh_single] at this; exact singleton_inj.mp this.symm
      have hf_valid : validCut (gap i) (decide (b = 1)) (CutCode.t1 f) = true := by
        simp only [validCut]; split_ifs with hb1
        · rw [decide_eq_true_eq, hfl, hf0, hb1_uv hb1]
        · rfl
      refine ⟨CutCode.t1 f, hf_valid, hfail_of_subset _ hf_valid
        (by intro u0 h; simp only [cutReqU, Option.some.injEq] at h; rw [← h, hf0])
        (by intro v0 h; simp only [cutReqV, Option.some.injEq] at h; rw [← h, hfl, Bool.not_not])
        ?_⟩
      intro k x y hx hy
      simp only [cutR] at hx hy
      rw [mem_singleton] at hx; subst hx
      rw [hf_mem k.castSucc, hf_mem k.succ]
      exact ⟨mem_singleton_self _, hy⟩

private lemma fullFormula_enc :
    ∀ a : VType n b → Bool,
      (∃ x : Fin n → Bool, (∀ site : Fin n, a (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) = true) ∧
        ∀ i : Fin b, x (posN n hn (gapStart n b origin gap i)) = a (Sum.inl i)) ↔
      Satisfies a (↑(fullFormula n b hn hb origin gap hv) : Set (Clause (VType n b))) := by
  intro a
  constructor
  · rintro ⟨x, hx_e, hx_b⟩ C hC
    rw [Finset.mem_coe] at hC
    obtain ⟨⟨i, ⟨c, hc⟩⟩, _, rfl⟩ := mem_image.mp hC
    exact cut_sound n b hn hb origin gap hv i c hc a x hx_e hx_b
  · intro hsat
    have hreach : ∀ i : Fin b, a (Sum.inl (nextGap b hb i)) ∈
        reachLayer n b hn origin gap i a ⟨gap i, Nat.lt_succ_self _⟩ := by
      intro i
      by_contra hmiss
      obtain ⟨c, hc, hfail⟩ := reach_empty_cut n b hn hb origin gap hv i a hmiss
      exact hfail (hsat _ (Finset.mem_coe.mpr (mem_image.mpr ⟨⟨i, ⟨c, hc⟩⟩, mem_univ _, rfl⟩)))
    let pathOf : ∀ i : Fin b, Fin (gap i + 1) → Bool := fun i =>
      Classical.choose (reachLayer_spec n b hn origin gap i a ⟨gap i, Nat.lt_succ_self _⟩
        (a (Sum.inl (nextGap b hb i))) (hreach i))
    have hpath_spec : ∀ i : Fin b, pathOf i 0 = a (Sum.inl i) ∧
        pathOf i ⟨gap i, Nat.lt_succ_self _⟩ = a (Sum.inl (nextGap b hb i)) ∧
        ∀ j : Fin (gap i), a (Sum.inr (gapSite n b hn origin gap i j.val,
          pathOf i j.castSucc, pathOf i j.succ)) = true := fun i => by
      obtain ⟨h1, h2, h3⟩ := Classical.choose_spec
        (reachLayer_spec n b hn origin gap i a ⟨gap i, Nat.lt_succ_self _⟩
          (a (Sum.inl (nextGap b hb i))) (hreach i))
      exact ⟨h1, h2, fun j => h3 j⟩
    let eqv := siteEquiv n b hn origin gap hv
    let x : Fin n → Bool := fun s => pathOf (eqv.symm s).1 (eqv.symm s).2.castSucc
    have hx_at : ∀ (i : Fin b) (k : Fin (gap i)), x (gapSite n b hn origin gap i k.val) = pathOf i k.castSucc := by
      intro i k
      dsimp only [x]
      have hinv : eqv.symm (gapSite n b hn origin gap i k.val) = ⟨i, k⟩ := eqv.left_inv ⟨i, k⟩
      rw [hinv]
    have hx_start : ∀ i : Fin b, x (posN n hn (gapStart n b origin gap i)) = a (Sum.inl i) := by
      intro i
      have h0 : (⟨0, hv.1 i⟩ : Fin (gap i)).val = 0 := rfl
      have hs0 := hx_at i ⟨0, hv.1 i⟩
      simp only [gapSite, h0, add_zero] at hs0
      rw [hs0]; exact (hpath_spec i).1
    have hx_edges : ∀ site : Fin n, a (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) = true := by
      intro site
      obtain ⟨⟨i, k⟩, hik⟩ := (eqv.surjective site)
      have hs_eq : site = gapSite n b hn origin gap i k.val := hik.symm
      rw [hs_eq, hx_at i k, gapSite_next]
      by_cases hlast : k.val + 1 < gap i
      · let k' : Fin (gap i) := ⟨k.val + 1, hlast⟩
        have h1 := hx_at i k'
        have hks : k.succ = k'.castSucc := Fin.ext rfl
        rw [h1, ← hks]
        exact (hpath_spec i).2.2 k
      · have hk_last : k.val + 1 = gap i := by have := k.isLt; omega
        rw [hk_last, gapSite_end n b hn hb origin gap hv i, hx_start (nextGap b hb i)]
        have hks : k.succ = ⟨gap i, Nat.lt_succ_self _⟩ := Fin.ext hk_last
        rw [← (hpath_spec i).2.1, ← hks]
        exact (hpath_spec i).2.2 k
    exact ⟨x, hx_edges, hx_start⟩

-- Private-repair and competitor lower bound!
def hasEdgePath {h : ℕ} (E_off : Finset (Fin h × Bool × Bool)) (u v : Bool) : Prop :=
  ∃ p : Fin (h + 1) → Bool, p 0 = u ∧ p ⟨h, Nat.lt_succ_self _⟩ = v ∧
    ∀ k : Fin h, (k, p k.castSucc, p k.succ) ∉ E_off

private lemma not_hasEdgePath_of_cut {h : ℕ} (c : CutCode h) (u v : Bool)
    (hu : match cutReqU c with | some u0 => u = u0 | none => True)
    (hv_bnd : match cutReqV c with | some v0 => v = v0 | none => True) :
    ¬ hasEdgePath (cutEdges c) u v := by
  rintro ⟨p, hp0, hph, hpe⟩
  have hstart : p 0 ∈ cutR c 0 := by
    rw [hp0]; cases c with
    | t1 f => simp [cutReqU] at hu; simp [cutR, hu]
    | t2 s f => simp [cutReqU] at hu; simp [cutR, hu]
    | t3 t f => simp [cutR, show 0 < h - t.val by have := t.isLt; omega]
    | t4 a0 p0 f => simp [cutR, show 0 < a0.val + 2 - p0.val by have := p0.isLt; omega]
  have hend : ∃ m : Fin (h + 1), p m ∉ cutR c m := by
    cases c with
    | t1 f => refine ⟨⟨h, Nat.lt_succ_self _⟩, ?_⟩; simp [cutReqV] at hv_bnd; simp [cutR, hph, hv_bnd]
    | t2 s f => refine ⟨⟨s.val + 1, by have := s.isLt; omega⟩, by simp [cutR]⟩
    | t3 t f =>
      refine ⟨⟨h, Nat.lt_succ_self _⟩, ?_⟩
      simp [cutReqV] at hv_bnd; have ht := t.isLt
      simp [cutR, hph, hv_bnd, show ¬ h < h - t.val by omega, show h - (h - t.val) = t.val by omega]
    | t4 a0 p0 f =>
      refine ⟨⟨a0.val + 2, by have := a0.isLt; omega⟩, ?_⟩
      have hp := p0.isLt
      simp [cutR, show ¬ a0.val + 2 < a0.val + 2 - p0.val by omega]
  obtain ⟨m, hm⟩ := hend
  have hcross : ∃ k : Fin h, p k.castSucc ∈ cutR c k.castSucc ∧ p k.succ ∉ cutR c k.succ := by
    induction m using Fin.induction with
    | zero => exact (hm hstart).elim
    | succ m' ih =>
      by_cases hm' : p m'.castSucc ∈ cutR c m'.castSucc
      · exact ⟨m', hm', hm⟩
      · exact ih hm'
  obtain ⟨k, hk1, hk2⟩ := hcross
  exact hpe k ((mem_cutEdges c _).mpr ⟨hk1, hk2⟩)

def privUV {h : ℕ} (b1 : Bool) : CutCode h → Bool × Bool
  | .t1 f => (f 0, if b1 then f 0 else !(f ⟨h, Nat.lt_succ_self _⟩))
  | .t2 _ f => (f 0, if b1 then f 0 else false)
  | .t3 t_off f => (if b1 then !(f ⟨t_off.val, Nat.lt_succ_self _⟩) else false,
      !(f ⟨t_off.val, Nat.lt_succ_self _⟩))
  | .t4 _ _ _ => (false, false)

private lemma privUV_blocked {h : ℕ} (hh : 0 < h) (b1 : Bool) (c : CutCode h)
    (hc : validCut h b1 c = true) :
    ¬ hasEdgePath (cutEdges c) (privUV b1 c).1 (privUV b1 c).2 := by
  refine not_hasEdgePath_of_cut c _ _ ?_ ?_
  · cases c <;> simp [cutReqU, privUV]
  · cases c with
    | t1 f =>
      simp only [cutReqV, privUV]
      by_cases hb : b1 = true
      · simp only [validCut, hb, ↓reduceIte, decide_eq_true_eq] at hc
        simp [hb, hc]
      · simp [hb]
    | t2 => simp [cutReqV, privUV]
    | t3 => simp [cutReqV, privUV]
    | t4 => simp [cutReqV, privUV]

private lemma privUV_repairs_u {h : ℕ} (hh : 0 < h) (b1 : Bool) (c : CutCode h)
    (hc : validCut h b1 c = true) (u0 : Bool) (hru : cutReqU c = some u0) :
    hasEdgePath (cutEdges c) (!u0) (if b1 then !u0 else (privUV b1 c).2) := by
  cases c with
  | t1 f =>
    simp only [cutReqU, Option.some.injEq] at hru; subst hru
    let p : Fin (h + 1) → Bool := fun j =>
      if hj : j.val < h then !(f j) else if b1 then !(f 0) else !(f ⟨h, Nat.lt_succ_self _⟩)
    refine ⟨p, ?_, ?_, ?_⟩
    · simp [p, hh]
    · by_cases hb : b1 = true <;> simp [p, privUV, hb]
    · intro k hk
      rw [mem_cutEdges] at hk
      have h1 : p k.castSucc = !(f k.castSucc) := by simp [p, k.isLt]
      have hmem1 := hk.1
      rw [h1] at hmem1; simp [cutR] at hmem1
  | t2 s f =>
    simp only [cutReqU, Option.some.injEq] at hru; subst hru
    let p : Fin (h + 1) → Bool := fun j =>
      if hj : j.val ≤ s.val then !(f ⟨j.val, Nat.lt_succ_of_le hj⟩)
      else if b1 then !(f 0) else false
    refine ⟨p, ?_, ?_, ?_⟩
    · simp [p]
    · have hs := s.isLt
      by_cases hb : b1 = true <;> simp [p, show ¬ h ≤ s.val by omega, privUV, hb]
    · intro k hk
      rw [mem_cutEdges] at hk
      by_cases hks : k.val ≤ s.val
      · have h1 : p k.castSucc = !(f ⟨k.val, Nat.lt_succ_of_le hks⟩) := by
          simp only [p, Fin.val_castSucc]; rw [dif_pos hks]
        have hmem1 : p k.castSucc ∈ cutR (CutCode.t2 s f) k.castSucc := hk.1
        rw [h1] at hmem1; simp only [cutR, Fin.val_castSucc] at hmem1; rw [dif_pos hks] at hmem1
        simp only [mem_singleton] at hmem1
        cases hf : f ⟨k.val, Nat.lt_succ_of_le hks⟩ <;> rw [hf] at hmem1 <;> cases hmem1
      · have hmem2 : p k.succ ∉ cutR (CutCode.t2 s f) k.succ := hk.2
        simp only [cutR, Fin.val_succ] at hmem2
        rw [dif_neg (by omega), if_neg (by omega)] at hmem2
        exact hmem2 (mem_univ _)
  | t3 => simp [cutReqU] at hru
  | t4 => simp [cutReqU] at hru

private lemma privUV_repairs_v {h : ℕ} (hh : 0 < h) (b1 : Bool) (c : CutCode h)
    (hc : validCut h b1 c = true) (v0 : Bool) (hrv : cutReqV c = some v0) :
    hasEdgePath (cutEdges c) (if b1 then !v0 else (privUV b1 c).1) (!v0) := by
  cases c with
  | t1 f =>
    simp only [cutReqV, Option.some.injEq] at hrv; subst hrv
    by_cases hb : b1 = true
    · have hc0 := hc
      simp only [validCut, hb, ↓reduceIte, decide_eq_true_eq] at hc
      have hnv : f 0 = !(f ⟨h, Nat.lt_succ_self _⟩) := by rw [hc, Bool.not_not]
      have hfu := privUV_repairs_u hh b1 (CutCode.t1 f) hc0 (f 0) rfl
      simp only [hb, ↓reduceIte] at hfu ⊢
      simpa [hnv] using hfu
    · simp only [hb, ↓reduceIte, Bool.not_not, privUV]
      refine ⟨f, rfl, rfl, fun k hk => ?_⟩
      rw [mem_cutEdges] at hk
      have := hk.2; simp [cutR] at this
  | t2 => simp [cutReqV] at hrv
  | t3 t_off f =>
    simp only [cutReqV, Option.some.injEq] at hrv; subst hrv
    let t := h - t_off.val
    let v0_val := f ⟨t_off.val, Nat.lt_succ_self _⟩
    let p : Fin (h + 1) → Bool := fun j =>
      if hj : j.val < t then (if b1 then v0_val else false)
      else f ⟨j.val - t, by have := t_off.isLt; have := j.isLt; omega⟩
    have ht_lt : t_off.val < h - 1 := t_off.isLt
    have ht_pos : 2 ≤ t := by dsimp [t]; omega
    refine ⟨p, ?_, ?_, ?_⟩
    · by_cases hb : b1 = true <;> simp [p, show 0 < t by omega, privUV, v0_val, hb]
    · have : ¬ h < t := by omega
      simp [p, this, show h - t = t_off.val by omega, v0_val]
    · intro k hk
      rw [mem_cutEdges] at hk
      by_cases hkt : k.val + 1 < t
      · have hmem2 := hk.2
        simp only [cutR, Fin.val_succ] at hmem2
        rw [dif_pos (by dsimp [t] at hkt; exact hkt)] at hmem2
        exact hmem2 (mem_univ _)
      · have hge : t ≤ k.val + 1 := by omega
        have hmem2 : p k.succ ∈ cutR (CutCode.t3 t_off f) k.succ := by
          have hp_eq : p k.succ = f ⟨k.val + 1 - t, by have := k.isLt; omega⟩ := by
            simp only [p, Fin.val_succ]; rw [dif_neg hkt]
          rw [hp_eq]; simp only [cutR, Fin.val_succ]; dsimp only [t]
          rw [dif_neg (by dsimp [t] at hge; omega)]
          exact mem_singleton_self _
        exact hk.2 hmem2
  | t4 => simp [cutReqV] at hrv

private lemma privUV_repairs_edge {h : ℕ} (hh : 0 < h) (b1 : Bool) (c : CutCode h)
    (hc : validCut h b1 c = true) (e0 : Fin h × Bool × Bool) (he0 : e0 ∈ cutEdges c) :
    hasEdgePath ((cutEdges c).erase e0) (privUV b1 c).1 (privUV b1 c).2 := by
  rcases e0 with ⟨k0, x0, y0⟩
  rw [mem_cutEdges] at he0
  rcases he0 with ⟨hx0, hy0⟩
  cases c with
  | t1 f =>
    simp only [cutR, mem_singleton] at hx0 hy0
    have hy0_eq : y0 = !(f k0.succ) := by
      cases hy0v : y0 <;> cases hfk : f k0.succ <;> simp only [hy0v, hfk, Bool.not_true, Bool.not_false] at hy0 ⊢
      all_goals first | rfl | exact absurd rfl hy0 | contradiction
    let p : Fin (h + 1) → Bool := fun j =>
      if j.val ≤ k0.val then f j else if hj : j.val < h then !(f j) else (privUV b1 (CutCode.t1 f)).2
    refine ⟨p, ?_, ?_, fun k hk => ?_⟩
    · simp [p, privUV]
    · have hk0l : ¬ h ≤ k0.val := by have := k0.isLt; omega
      simp [p, hk0l]
    · rw [mem_erase, ne_eq] at hk
      rcases hk with ⟨hne, hmem⟩
      rw [mem_cutEdges] at hmem
      by_cases hlt : k.val < k0.val
      · have h1 : p k.succ = f k.succ := by
          dsimp only [p]; rw [if_pos (by change k.val + 1 ≤ k0.val; omega)]
        have := hmem.2; rw [h1] at this; simp [cutR] at this
      · by_cases heq : k = k0
        · subst heq
          have h1 : p k.castSucc = x0 := by simp [p, hx0]
          have h2 : p k.succ = y0 := by
            by_cases hlast : k.val + 1 < h
            · simp only [p, Fin.val_succ]
              rw [if_neg (by omega), dif_pos hlast, hy0_eq]
            · have hk_eq : k.val + 1 = h := by have := k.isLt; omega
              have hks : k.succ = ⟨h, Nat.lt_succ_self _⟩ := Fin.ext hk_eq
              simp only [p, Fin.val_succ, if_neg (by omega), dif_neg (by omega), privUV]
              by_cases hb : b1 = true
              · simp only [validCut, hb, ↓reduceIte, decide_eq_true_eq] at hc
                rw [hy0_eq, hks, hc, Bool.not_not]; simp [hb]
              · rw [hy0_eq, hks]; simp [hb]
          apply hne; exact Prod.ext rfl (Prod.ext h1 h2)
        · have hgt : k0.val < k.val := by have : k.val ≠ k0.val := fun h => heq (Fin.ext h); omega
          have h1 : p k.castSucc = !(f k.castSucc) := by
            simp only [p, Fin.val_castSucc]; rw [if_neg (by omega), dif_pos k.isLt]
          have := hmem.1; rw [h1] at this; simp [cutR] at this
  | t2 s f =>
    have hs := s.isLt
    have hk0_le : k0.val ≤ s.val := by
      by_contra hgt
      simp only [cutR, Fin.val_succ] at hy0
      rw [dif_neg (by change ¬ k0.val + 1 ≤ s.val; omega),
          if_neg (by change k0.val + 1 ≠ s.val + 1; omega)] at hy0
      exact absurd (mem_univ y0) hy0
    have hx0_eq : x0 = f ⟨k0.val, Nat.lt_succ_of_le hk0_le⟩ := by
      simp only [cutR, Fin.val_castSucc] at hx0
      rw [dif_pos hk0_le, mem_singleton] at hx0
      exact hx0
    let p : Fin (h + 1) → Bool := fun j =>
      if hj1 : j.val ≤ k0.val then f ⟨j.val, Nat.lt_succ_of_le (le_trans hj1 hk0_le)⟩
      else if j.val = k0.val + 1 then y0
      else if hj2 : j.val ≤ s.val then !(f ⟨j.val, Nat.lt_succ_of_le hj2⟩)
      else (privUV b1 (CutCode.t2 s f)).2
    refine ⟨p, ?_, ?_, fun k hk => ?_⟩
    · simp only [p, privUV, Fin.val_zero, Nat.zero_le, ↓reduceDIte]; rfl
    · have hk0l : ¬ h ≤ k0.val := by omega
      have hne1 : h ≠ k0.val + 1 := by omega
      have hns : ¬ h ≤ s.val := by omega
      dsimp only [p]; rw [dif_neg hk0l, if_neg hne1, dif_neg hns]
    · rw [mem_erase, ne_eq] at hk
      rcases hk with ⟨hne, hmem⟩
      rw [mem_cutEdges] at hmem
      by_cases hlt : k.val < k0.val
      · have hk2 : k.succ.val ≤ s.val := by change k.val + 1 ≤ s.val; omega
        have h1 : p k.succ = f ⟨k.val + 1, Nat.lt_succ_of_le hk2⟩ := by
          simp only [p, Fin.val_succ]; rw [dif_pos (by omega)]
        have := hmem.2; rw [h1] at this
        simp only [cutR, Fin.val_succ] at this
        rw [dif_pos (by omega), mem_singleton] at this
        exact this (congrArg f (Fin.ext rfl))
      · by_cases heq : k = k0
        · subst heq
          have h1 : p k.castSucc = x0 := by
            simp only [p, Fin.val_castSucc, le_refl, ↓reduceDIte]; exact hx0_eq.symm
          have h2 : p k.succ = y0 := by
            simp only [p, Fin.val_succ, ↓reduceIte]
            rw [dif_neg (by omega)]
          apply hne; exact Prod.ext rfl (Prod.ext h1 h2)
        · have hgt : k0.val < k.val := by have : k.val ≠ k0.val := fun h => heq (Fin.ext h); omega
          by_cases hks : k.val ≤ s.val
          · rcases eq_or_ne k.val (k0.val + 1) with heq1 | hne1
            · have h1 : p k.castSucc = y0 := by
                simp only [p, Fin.val_castSucc]
                rw [dif_neg (by omega), if_pos (by exact heq1)]
              have hks1 : k.castSucc = k0.succ := Fin.ext heq1
              have := hmem.1; rw [h1, hks1] at this; exact hy0 this
            · have h1 : p k.castSucc = !(f ⟨k.val, Nat.lt_succ_of_le hks⟩) := by
                simp only [p, Fin.val_castSucc]
                rw [dif_neg (by omega), if_neg hne1, dif_pos hks]
              have := hmem.1; rw [h1] at this
              simp only [cutR, Fin.val_castSucc] at this
              rw [dif_pos hks, mem_singleton] at this
              exact absurd this (Bool.not_ne_self _)
          · have := hmem.2
            simp only [cutR, Fin.val_succ] at this
            rw [dif_neg (by omega), if_neg (by omega)] at this
            exact absurd (mem_univ _) this
  | t3 t_off f =>
    let t := h - t_off.val
    have ht_lt : t_off.val < h - 1 := t_off.isLt
    have ht_pos : 2 ≤ t := by dsimp [t]; omega
    have hk0_ge : t - 1 ≤ k0.val := by
      by_contra hlt
      simp only [cutR, Fin.val_succ] at hy0
      rw [dif_pos (by dsimp [t] at hlt; omega)] at hy0
      exact absurd (mem_univ y0) hy0
    let uw := (privUV b1 (CutCode.t3 t_off f)).1
    let vw := (privUV b1 (CutCode.t3 t_off f)).2
    let p : Fin (h + 1) → Bool := fun j =>
      if j.val = k0.val then x0
      else if j.val < t then uw
      else if j.val < k0.val then f ⟨j.val - t, by have := j.isLt; omega⟩
      else if j.val = h then vw
      else !(f ⟨j.val - t, by have := j.isLt; omega⟩)
    refine ⟨p, ?_, ?_, fun k hk => ?_⟩
    · dsimp only [p]; rw [if_neg (by change 0 ≠ k0.val; omega), if_pos (by change 0 < t; omega)]
    · have hk0l : h ≠ k0.val := by have := k0.isLt; omega
      have hnt : ¬ h < t := by omega
      have hnk : ¬ h < k0.val := by have := k0.isLt; omega
      dsimp only [p]; rw [if_neg hk0l, if_neg hnt, if_neg hnk, if_pos rfl]
    · rw [mem_erase, ne_eq] at hk
      rcases hk with ⟨hne, hmem⟩
      rw [mem_cutEdges] at hmem
      by_cases hlt : k.val < k0.val
      · by_cases hkt : k.val + 1 < t
        · have := hmem.2
          simp only [cutR, Fin.val_succ] at this
          rw [dif_pos (by dsimp [t] at hkt; exact hkt)] at this
          exact absurd (mem_univ _) this
        · by_cases hk_eq : k.val + 1 = k0.val
          · have h1 : p k.succ = x0 := by
              simp only [p, Fin.val_succ]; rw [if_pos hk_eq]
            have hke : k.succ = k0.castSucc := Fin.ext hk_eq
            have := hmem.2; rw [h1, hke] at this; exact this hx0
          · have hge : t ≤ k.val + 1 := by omega
            have h1 : p k.succ = f ⟨k.val + 1 - t, by have := k.isLt; omega⟩ := by
              simp only [p, Fin.val_succ]
              rw [if_neg hk_eq, if_neg hkt, if_pos (by omega)]
            have := hmem.2; rw [h1] at this
            simp only [cutR, Fin.val_succ] at this
            rw [dif_neg (by dsimp [t] at hge; omega), mem_singleton] at this
            exact this (congrArg f (Fin.ext rfl))
      · by_cases heq : k = k0
        · subst heq
          have h1 : p k.castSucc = x0 := by simp only [p, Fin.val_castSucc, ↓reduceIte]
          have h2 : p k.succ = y0 := by
            by_cases hlast : k.val + 1 = h
            · have hks : k.succ = ⟨h, Nat.lt_succ_self _⟩ := Fin.ext hlast
              rw [hks] at hy0
              simp only [cutR] at hy0
              rw [dif_neg (by dsimp [t] at ht_pos ⊢; omega), mem_singleton] at hy0
              have hidx : f ⟨h - (h - t_off.val), by have := t_off.isLt; omega⟩ =
                  f ⟨t_off.val, Nat.lt_succ_self _⟩ :=
                congrArg f (Fin.ext (Nat.sub_sub_self (le_trans (Nat.le_of_lt ht_lt) (Nat.sub_le h 1))))
              rw [hidx] at hy0
              have hy0' : y0 = vw := by
                dsimp [vw, privUV]
                cases hy0v : y0 <;> cases hft : f ⟨t_off.val, Nat.lt_succ_self _⟩ <;>
                  simp only [hy0v, hft, Bool.not_true, Bool.not_false] at hy0 ⊢ <;>
                  first | rfl | exact absurd trivial hy0 | exact absurd rfl hy0
              rw [hy0']
              simp only [p, Fin.val_succ]
              rw [if_neg (by omega), if_neg (by dsimp [t]; omega),
                  if_neg (by omega), if_pos hlast]
            · simp only [cutR, Fin.val_succ] at hy0
              rw [dif_neg (by dsimp [t] at hk0_ge ⊢; omega), mem_singleton] at hy0
              have hidx : f ⟨k.val + 1 - (h - t_off.val), by have := t_off.isLt; have := k.isLt; omega⟩ =
                  f ⟨k.val + 1 - t, by have := k.isLt; omega⟩ := congrArg f (Fin.ext rfl)
              rw [hidx] at hy0
              have hy0' : y0 = !(f ⟨k.val + 1 - t, by have := k.isLt; omega⟩) := by
                cases hy0v : y0 <;> cases hft : f ⟨k.val + 1 - t, by have := k.isLt; omega⟩ <;>
                  simp only [hy0v, hft, Bool.not_true, Bool.not_false] at hy0 ⊢ <;>
                  first | rfl | exact absurd trivial hy0 | exact absurd rfl hy0
              simp only [p, Fin.val_succ]
              rw [if_neg (by omega), if_neg (by dsimp [t] at hk0_ge ⊢; omega),
                  if_neg (by omega), if_neg hlast, hy0']
          apply hne; exact Prod.ext rfl (Prod.ext h1 h2)
        · have hgt : k0.val < k.val := by have : k.val ≠ k0.val := fun h => heq (Fin.ext h); omega
          have h1 : p k.castSucc = !(f ⟨k.val - t, by have := k.isLt; omega⟩) := by
            simp only [p, Fin.val_castSucc]
            rw [if_neg (by omega), if_neg (by dsimp [t] at hk0_ge ⊢; omega),
                if_neg (by omega), if_neg k.isLt.ne]
          have := hmem.1; rw [h1] at this
          simp only [cutR, Fin.val_castSucc] at this
          rw [dif_neg (by dsimp [t] at hk0_ge hgt ⊢; omega), mem_singleton] at this
          have heq_f : f ⟨k.val - t, by have := k.isLt; omega⟩ =
              f ⟨k.val - (h - t_off.val), by have := t_off.isLt; have := k.isLt; omega⟩ :=
            congrArg f (Fin.ext rfl)
          rw [← heq_f] at this
          exact absurd this (Bool.not_ne_self _)
  | t4 a_off p_off f =>
    let a := a_off.val + 2
    let p_lo := a - p_off.val
    have ha_lt := a_off.isLt; have hp_le := Nat.lt_succ_iff.mp p_off.isLt
    have hk0_range : p_lo - 1 ≤ k0.val ∧ k0.val < a := by
      constructor <;> by_contra hbad
      · simp only [cutR, Fin.val_succ] at hy0
        rw [dif_pos (by dsimp [a, p_lo] at hbad; omega)] at hy0
        exact absurd (mem_univ y0) hy0
      · simp only [cutR, Fin.val_succ] at hy0
        rw [dif_neg (by dsimp [a, p_lo] at hbad ⊢; omega),
            dif_neg (by dsimp [a] at hbad; omega),
            if_neg (by dsimp [a] at hbad; omega)] at hy0
        exact absurd (mem_univ y0) hy0
    let p : Fin (h + 1) → Bool := fun j =>
      if j.val = k0.val then x0
      else if j.val = k0.val + 1 then y0
      else if hj1 : j.val < p_lo then false
      else if hj2 : j.val < k0.val then f ⟨j.val - p_lo, by omega⟩
      else if hj3 : j.val < a then !(f ⟨j.val - p_lo, by omega⟩)
      else false
    refine ⟨p, ?_, ?_, fun k hk => ?_⟩
    · have hp_pos : 2 ≤ p_lo := by dsimp [p_lo, a]; omega
      have hne0a : (0 : ℕ) ≠ k0.val := by omega
      have hne0b : (0 : ℕ) ≠ k0.val + 1 := by omega
      have hlt0p : 0 < p_lo := by omega
      simp only [p, privUV, Fin.val_zero, hne0a, hne0b, hlt0p, ↓reduceIte, ↓reduceDIte]
    · have hne1 : h ≠ k0.val := by have := k0.isLt; omega
      have hne2 : h ≠ k0.val + 1 := by omega
      have hnp : ¬ h < p_lo := by omega
      have hnk : ¬ h < k0.val := by have := k0.isLt; omega
      have hna : ¬ h < a := by omega
      dsimp only [p]
      rw [if_neg hne1, if_neg hne2, dif_neg hnp, dif_neg hnk, dif_neg hna]
      simp [privUV]
    · rw [mem_erase, ne_eq] at hk
      rcases hk with ⟨hne, hmem⟩
      rw [mem_cutEdges] at hmem
      by_cases hlt : k.val < k0.val
      · by_cases hk1 : k.val + 1 < p_lo
        · have := hmem.2
          simp only [cutR, Fin.val_succ] at this
          rw [dif_pos (by dsimp [a, p_lo] at hk1; exact hk1)] at this
          exact absurd (mem_univ _) this
        · by_cases hkeq : k.val + 1 = k0.val
          · have h1 : p k.succ = x0 := by
              simp only [p, Fin.val_succ]; rw [if_pos hkeq]
            have hks : k.succ = k0.castSucc := Fin.ext hkeq
            have := hmem.2; rw [h1, hks] at this; exact this hx0
          · have h1 : p k.succ = f ⟨k.val + 1 - p_lo, by omega⟩ := by
              simp only [p, Fin.val_succ]
              rw [if_neg hkeq, if_neg (by omega), dif_neg hk1, dif_pos (by omega)]
            have := hmem.2; rw [h1] at this
            simp only [cutR, Fin.val_succ] at this
            rw [dif_neg (by dsimp [a, p_lo] at hk1; exact hk1),
                dif_pos (by dsimp [a] at hk0_range ⊢; omega),
                mem_singleton] at this
            exact this (congrArg f (Fin.ext rfl))
      · by_cases heq : k = k0
        · subst heq
          have h1 : p k.castSucc = x0 := by simp only [p, Fin.val_castSucc, ↓reduceIte]
          have h2 : p k.succ = y0 := by
            simp only [p, Fin.val_succ, ↓reduceIte]
            rw [if_neg (by omega)]
          apply hne; exact Prod.ext rfl (Prod.ext h1 h2)
        · have hgt : k0.val < k.val := by have : k.val ≠ k0.val := fun h => heq (Fin.ext h); omega
          by_cases hka : k.val < a
          · rcases eq_or_ne k.val (k0.val + 1) with heq1 | hne1
            · have h1 : p k.castSucc = y0 := by
                simp only [p, Fin.val_castSucc]
                rw [if_neg (by omega), if_pos heq1]
              have hks : k.castSucc = k0.succ := Fin.ext heq1
              have := hmem.1; rw [h1, hks] at this; exact hy0 this
            · have h1 : p k.castSucc = !(f ⟨k.val - p_lo, by omega⟩) := by
                simp only [p, Fin.val_castSucc]
                rw [if_neg (by omega), if_neg hne1, dif_neg (by omega),
                    dif_neg (by omega), dif_pos hka]
              have := hmem.1; rw [h1] at this
              simp only [cutR, Fin.val_castSucc] at this
              rw [dif_neg (by dsimp [a, p_lo] at hk0_range hgt ⊢; omega),
                  dif_pos (by dsimp [a] at hka; exact hka),
                  mem_singleton] at this
              have heq_f : f ⟨k.val - p_lo, by omega⟩ =
                  f ⟨k.val - (a_off.val + 2 - p_off.val), by have := p_off.isLt; omega⟩ :=
                congrArg f (Fin.ext rfl)
              rw [← heq_f] at this
              exact absurd this (Bool.not_ne_self _)
          · have := hmem.2
            simp only [cutR, Fin.val_succ] at this
            rw [dif_neg (by dsimp [a, p_lo] at hka ⊢; omega),
                dif_neg (by dsimp [a] at hka; omega),
                if_neg (by dsimp [a] at hka; omega)] at this
            exact absurd (mem_univ _) this

private lemma hasPath_to_global (hv : ValidGap n b gap) (i : Fin b) (E_off : Finset (Fin (gap i) × Bool × Bool))
    (u v : Bool) (hpath : hasEdgePath E_off u v)
    (h_b1 : b = 1 → u = v) :
    let a : VType n b → Bool := fun var => match var with
      | Sum.inl j =>
          if j = i then u else if j = nextGap b hb i then v else false
      | Sum.inr (site, x1, x2) =>
          decide (¬ ∃ e ∈ E_off, gapSite n b hn origin gap i e.1.val = site ∧ e.2 = (x1, x2))
    ∃ x : Fin n → Bool, (∀ site : Fin n, a (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) = true) ∧
      ∀ j : Fin b, x (posN n hn (gapStart n b origin gap j)) = a (Sum.inl j) := by
  intro a
  obtain ⟨p, hp0, hph, hpe⟩ := hpath
  let eqv := siteEquiv n b hn origin gap hv
  let bnd : Fin n → Bool := fun s =>
    let pair := eqv.symm s
    if hpi : pair.1 = i then
      p ⟨pair.2.val, by rw [← hpi]; exact Nat.lt_succ_of_lt pair.2.isLt⟩
    else if pair.2.val = 0 then a (Sum.inl pair.1) else false
  refine ⟨bnd, ?_, ?_⟩
  · intro site
    simp only [a, decide_eq_true_eq]
    rintro ⟨e, he, hsite, he2⟩
    subst hsite
    have h1 : bnd (gapSite n b hn origin gap i e.1.val) = p e.1.castSucc := by
      have hinv : eqv.symm (gapSite n b hn origin gap i e.1.val) = ⟨i, e.1⟩ := eqv.left_inv ⟨i, e.1⟩
      dsimp only [bnd]; rw [hinv, dif_pos rfl]; rfl
    have h2 : bnd (posN n hn ((gapSite n b hn origin gap i e.1.val).val + 1)) = p e.1.succ := by
      rw [gapSite_next]
      by_cases hlast : e.1.val + 1 < gap i
      · let k' : Fin (gap i) := ⟨e.1.val + 1, hlast⟩
        have hke : e.1.succ = k'.castSucc := Fin.ext rfl
        have hinv : eqv.symm (gapSite n b hn origin gap i (e.1.val + 1)) = ⟨i, k'⟩ :=
          eqv.left_inv ⟨i, k'⟩
        dsimp only [bnd]; rw [hinv, dif_pos rfl, hke]; rfl
      · have hlast_eq : e.1.val + 1 = gap i := by have := e.1.isLt; omega
        rw [hlast_eq, gapSite_end n b hn hb origin gap hv i]
        have hks : e.1.succ = ⟨gap i, Nat.lt_succ_self _⟩ := Fin.ext hlast_eq
        rw [hks, hph]
        have hinv : eqv.symm (posN n hn (gapStart n b origin gap (nextGap b hb i))) =
            ⟨nextGap b hb i, ⟨0, hv.1 _⟩⟩ := eqv.left_inv ⟨nextGap b hb i, ⟨0, hv.1 _⟩⟩
        dsimp only [bnd]; rw [hinv]
        by_cases hsame : nextGap b hb i = i
        · have hb1 : b = 1 := by
            have hv_eq := congrArg Fin.val hsame
            simp only [nextGap] at hv_eq
            by_cases hi : i.val + 1 < b
            · rw [Nat.mod_eq_of_lt hi] at hv_eq; omega
            · have hi_eq : i.val + 1 = b := by have := i.isLt; omega
              rw [hi_eq, Nat.mod_self] at hv_eq
              have : i.val = 0 := hv_eq.symm
              omega
          rw [dif_pos hsame]
          exact (congrArg p (Fin.ext (by simp))).trans (hp0.trans (h_b1 hb1))
        · rw [dif_neg hsame, if_pos rfl]; dsimp only [a]; rw [if_neg hsame, if_pos rfl]
    rw [h1, h2] at he2
    exact hpe e.1 (by rw [← he2]; exact he)
  · intro j
    have hinv : eqv.symm (posN n hn (gapStart n b origin gap j)) = ⟨j, ⟨0, hv.1 j⟩⟩ :=
      eqv.left_inv ⟨j, ⟨0, hv.1 j⟩⟩
    dsimp only [bnd]
    rw [hinv]
    by_cases hj : j = i
    · subst hj
      simp only [dif_pos rfl, a, if_pos rfl]
      exact (congrArg p (Fin.ext (by simp))).trans hp0
    · rw [dif_neg hj, if_pos rfl]

private lemma competitor_lower (G : Finset (Clause (VType n b)))
    (hG : ∀ a : VType n b → Bool,
      (∃ x : Fin n → Bool, (∀ site : Fin n, a (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) = true) ∧
        ∀ i : Fin b, x (posN n hn (gapStart n b origin gap i)) = a (Sum.inl i)) ↔
      Satisfies a (↑G : Set (Clause (VType n b)))) :
    (fullFormula n b hn hb origin gap hv).card ≤ G.card ∧
    (∑ C ∈ fullFormula n b hn hb origin gap hv, C.card) ≤ ∑ B ∈ G, B.card := by
  have hex : ∀ C ∈ fullFormula n b hn hb origin gap hv,
      ∃ B ∈ G, C ⊆ B ∧ B.filter (fun l => decide (l.1.isRight ∧ l.2)) =
        C.filter (fun l => decide (l.1.isRight ∧ l.2)) := by
    intro C hC
    obtain ⟨⟨i, ⟨c, hc⟩⟩, _, rfl⟩ := mem_image.mp hC
    let uv := privUV (decide (b = 1)) c
    let a : VType n b → Bool := fun var => match var with
      | Sum.inl j =>
          if j = i then uv.1 else if j = nextGap b hb i then uv.2 else false
      | Sum.inr (site, x1, x2) =>
          decide (¬ ∃ e ∈ cutEdges c, gapSite n b hn origin gap i e.1.val = site ∧ e.2 = (x1, x2))
    have ha_fail : ¬ Satisfies a (↑G : Set (Clause (VType n b))) := by
      rw [← hG a]
      rintro ⟨x, hx_e, hx_b⟩
      have hpath : hasEdgePath (cutEdges c) uv.1 uv.2 := by
        refine ⟨fun k => x (gapSite n b hn origin gap i k.val), ?_, ?_, ?_⟩
        · dsimp only [gapSite]; simp only [Fin.val_zero, Nat.add_zero]; rw [hx_b i]; simp [a]
        · dsimp only
          rw [gapSite_end n b hn hb origin gap hv i, hx_b (nextGap b hb i)]
          by_cases hsame : nextGap b hb i = i
          · have hb1 : b = 1 := by
              have hv_eq := congrArg Fin.val hsame
              simp only [nextGap] at hv_eq
              by_cases hi : i.val + 1 < b
              · rw [Nat.mod_eq_of_lt hi] at hv_eq; omega
              · have hi_eq : i.val + 1 = b := by have := i.isLt; omega
                rw [hi_eq, Nat.mod_self] at hv_eq; have : i.val = 0 := hv_eq.symm; omega
            have hsame_uv : uv.1 = uv.2 := by
              cases c with
              | t1 f => simp [uv, privUV, hb1]
              | t2 s f => simp [uv, privUV, hb1]
              | t3 t f => simp [uv, privUV, hb1]
              | t4 a0 p0 f => simp [uv, privUV]
            simp [a, hsame, hsame_uv]
          · simp [a, hsame]
        · intro k hk
          have he := hx_e (gapSite n b hn origin gap i k.val)
          rw [gapSite_next] at he
          simp only [a, decide_eq_true_eq] at he
          exact he ⟨(k, _, _), hk, rfl, rfl⟩
      exact privUV_blocked (hv.1 i) (decide (b = 1)) c hc hpath
    simp only [Satisfies, Finset.mem_coe, not_forall] at ha_fail
    obtain ⟨B, hBG, hBfail⟩ := ha_fail
    have hBval : ∀ l ∈ B, a l.1 = !(l.2) := by
      intro l hl
      by_contra hne
      have : a l.1 = l.2 := by cases ha : a l.1 <;> cases hl2 : l.2 <;> simp_all
      exact hBfail ⟨l, hl, this⟩
    have hsub : toClause n b hn hb origin gap i c ⊆ B := by
      intro l hl
      by_contra hlB
      -- Flip l.1 in a!
      let a' : VType n b → Bool := Function.update a l.1 (!(a l.1))
      have hB_still_false : ¬ ClauseSat a' B := by
        rintro ⟨l', hl'B, hl'sat⟩
        have hne_v : l'.1 ≠ l.1 := by
          intro hveq
          have hv1 := hBval l' hl'B
          have hv2 : a' l'.1 = !(a l'.1) := by simp [a', hveq]
          rw [hl'sat] at hv2
          have : l'.2 = l.2 := by
            have hl_false : a l.1 = !(l.2) := by
              simp only [toClause, cutBndLits, cutEdgeLits, mem_union, mem_image] at hl
              rcases hl with (hlU | hlV) | ⟨e, he, rfl⟩
              · cases hru : cutReqU c with
                | none => simp [hru] at hlU
                | some u0 =>
                  simp only [hru, mem_singleton] at hlU; rw [hlU]
                  have hu0 : u0 = uv.1 := by
                    cases c <;> simp [cutReqU] at hru <;> simp [uv, privUV, hru]
                  simp [a, hu0]
              · cases hrv : cutReqV c with
                | none => simp [hrv] at hlV
                | some v0 =>
                  simp only [hrv, mem_singleton] at hlV; rw [hlV]
                  have hv0 : v0 = uv.2 := by
                    cases c with
                    | t1 f =>
                      simp only [cutReqV, Option.some.injEq] at hrv
                      by_cases hb1 : b = 1
                      · simp only [validCut, hb1, decide_true, ↓reduceIte, decide_eq_true_eq] at hc
                        simp [uv, privUV, hb1, ← hrv, hc]
                      · simp [uv, privUV, hb1, ← hrv]
                    | t2 => simp [cutReqV] at hrv
                    | t3 t0 f =>
                      simp only [cutReqV, Option.some.injEq] at hrv
                      simp only [uv, privUV, hrv]
                    | t4 => simp [cutReqV] at hrv
                  by_cases hsame : nextGap b hb i = i
                  · have hb1 : b = 1 := by
                      have hv_eq := congrArg Fin.val hsame
                      simp only [nextGap] at hv_eq
                      by_cases hi : i.val + 1 < b
                      · rw [Nat.mod_eq_of_lt hi] at hv_eq; omega
                      · have hi_eq : i.val + 1 = b := by have := i.isLt; omega
                        rw [hi_eq, Nat.mod_self] at hv_eq; have : i.val = 0 := hv_eq.symm; omega
                    have huv_eq : uv.1 = uv.2 := by
                      cases c <;> simp [uv, privUV, hb1]
                    simp [a, hsame, hv0, huv_eq]
                  · simp [a, hsame, hv0]
              · simp only [a, decide_eq_true_eq]
                have hex : ∃ e' ∈ cutEdges c, gapSite n b hn origin gap i e'.1.val = gapSite n b hn origin gap i e.1.val ∧ e'.2 = e.2 :=
                  ⟨e, he, rfl, rfl⟩
                simp [hex]
            rw [← hveq] at hl_false
            cases ha : a l'.1 <;> cases hb2 : l.2 <;> cases hc2 : l'.2 <;> simp_all
          have : l' = l := Prod.ext hveq this
          rw [this] at hl'B; exact hlB hl'B
        have hv' : a' l'.1 = a l'.1 := by simp [a', hne_v]
        rw [hv'] at hl'sat
        have := hBval l' hl'B
        rw [hl'sat] at this; cases l'.2 <;> simp at this
      have ha'_valid : ∃ x : Fin n → Bool,
          (∀ site : Fin n, a' (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) = true) ∧
          ∀ j : Fin b, x (posN n hn (gapStart n b origin gap j)) = a' (Sum.inl j) := by
        simp only [toClause, cutBndLits, cutEdgeLits, mem_union, mem_image] at hl
        rcases hl with (hlU | hlV) | ⟨e, he, rfl⟩
        · cases hru : cutReqU c with
          | none => simp [hru] at hlU
          | some u0 =>
            simp only [hru, mem_singleton] at hlU
            have hpat := privUV_repairs_u (hv.1 i) (decide (b = 1)) c hc u0 hru
            have hu0 : u0 = uv.1 := by
              cases c <;> simp [cutReqU] at hru <;> simp [uv, privUV, hru]
            have hgl := hasPath_to_global n b hn hb origin gap hv i (cutEdges c) (!u0)
              (if decide (b = 1) then !u0 else uv.2) hpat (fun hb1 => by simp [hb1])
            obtain ⟨x, hxg1, hxg2⟩ := hgl
            refine ⟨x, fun site => ?_, fun j => ?_⟩
            · have := hxg1 site
              have ha_eq : a' (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) =
                  a (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) := by
                dsimp only [a']; rw [Function.update_of_ne (by rw [hlU]; simp)]
              rw [ha_eq]; exact this
            · have := hxg2 j
              have ha_eq : a' (Sum.inl j) =
                  (if j = i then !u0 else if j = nextGap b hb i then (if decide (b = 1) then !u0 else uv.2) else false) := by
                dsimp only [a', a]
                by_cases hji : j = i
                · subst hji; rw [hlU]; simp only [Function.update_self, hu0, ↓reduceIte]
                · rw [Function.update_of_ne (by rw [hlU]; intro h; exact hji (Sum.inl.inj h))]
                  by_cases hb1 : b = 1
                  · subst hb1; exact absurd (Subsingleton.elim j i) hji
                  · have hni : nextGap b hb i ≠ i := by
                      intro heq; have hv' := congrArg Fin.val heq; simp only [nextGap] at hv'
                      by_cases hi : i.val + 1 < b
                      · rw [Nat.mod_eq_of_lt hi] at hv'; omega
                      · have hi_eq : i.val + 1 = b := by have := i.isLt; omega
                        rw [hi_eq, Nat.mod_self] at hv'; omega
                    simp [hji, hb1]
              exact this.trans ha_eq.symm
        · cases hrv : cutReqV c with
          | none => simp [hrv] at hlV
          | some v0 =>
            simp only [hrv, mem_singleton] at hlV
            have hpat := privUV_repairs_v (hv.1 i) (decide (b = 1)) c hc v0 hrv
            have hv0 : v0 = uv.2 := by
              cases c with
              | t1 f =>
                simp only [cutReqV, Option.some.injEq] at hrv
                by_cases hb1 : b = 1
                · simp only [validCut, hb1, decide_true, ↓reduceIte, decide_eq_true_eq] at hc
                  simp [uv, privUV, hb1, ← hrv, hc]
                · simp [uv, privUV, hb1, ← hrv]
              | t2 => simp [cutReqV] at hrv
              | t3 t0 f =>
                simp only [cutReqV, Option.some.injEq] at hrv
                simp only [uv, privUV, hrv]
              | t4 => simp [cutReqV] at hrv
            have hgl := hasPath_to_global n b hn hb origin gap hv i (cutEdges c)
              (if decide (b = 1) then !v0 else uv.1) (!v0) hpat (fun hb1 => by simp [hb1])
            obtain ⟨x, hxg1, hxg2⟩ := hgl
            refine ⟨x, fun site => ?_, fun j => ?_⟩
            · have := hxg1 site
              have ha_eq : a' (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) =
                  a (Sum.inr (site, x site, x (posN n hn (site.val + 1)))) := by
                dsimp only [a']; rw [Function.update_of_ne (by rw [hlV]; simp)]
              rw [ha_eq]; exact this
            · have := hxg2 j
              have ha_eq : a' (Sum.inl j) =
                  (if j = i then (if decide (b = 1) then !v0 else uv.1)
                   else if j = nextGap b hb i then !v0 else false) := by
                dsimp only [a', a]
                by_cases hjni : j = nextGap b hb i
                · subst hjni; rw [hlV]; simp only [Function.update_self]
                  by_cases hsame : nextGap b hb i = i
                  · have hb1 : b = 1 := by
                      have hv' := congrArg Fin.val hsame; simp only [nextGap] at hv'
                      by_cases hi : i.val + 1 < b
                      · rw [Nat.mod_eq_of_lt hi] at hv'; omega
                      · have hi_eq : i.val + 1 = b := by have := i.isLt; omega
                        rw [hi_eq, Nat.mod_self] at hv'; omega
                    have huv : uv.1 = uv.2 := by cases c <;> simp [uv, privUV, hb1]
                    simp [hsame, hb1, hv0, huv]
                  · simp [hsame, hv0]
                · rw [Function.update_of_ne (by rw [hlV]; intro h; exact hjni (Sum.inl.inj h))]
                  by_cases hb1 : b = 1
                  · subst hb1; exact absurd (Subsingleton.elim j (nextGap 1 hb i)) hjni
                  · simp [hjni, hb1]
              exact this.trans ha_eq.symm
        · have hpat := privUV_repairs_edge (hv.1 i) (decide (b = 1)) c hc e he
          have hgl := hasPath_to_global n b hn hb origin gap hv i ((cutEdges c).erase e)
            uv.1 uv.2 hpat (fun hb1 => by cases c <;> simp [uv, privUV, hb1])
          obtain ⟨x, hxg1, hxg2⟩ := hgl
          refine ⟨x, fun site => ?_, fun j => ?_⟩
          · have := hxg1 site
            dsimp only [a']
            by_cases heq : (Sum.inr (site, x site, x (posN n hn (site.val + 1))) : VType n b) =
                Sum.inr (gapSite n b hn origin gap i e.1.val, e.2)
            · rw [heq, Function.update_self]
              have ha_f : a (Sum.inr (gapSite n b hn origin gap i e.1.val, e.2)) = false := by
                simp only [a, decide_eq_false_iff_not, not_not]; exact ⟨e, he, rfl, rfl⟩
              rw [ha_f]; rfl
            · rw [Function.update_of_ne heq]
              have hx_eq : ¬ ∃ e' ∈ cutEdges c, gapSite n b hn origin gap i e'.1.val = site ∧ e'.2 = (x site, x (posN n hn (site.val + 1))) := by
                rintro ⟨e', he', hs1, hs2⟩
                simp only [a', Function.update_of_ne heq, a, decide_eq_true_eq, not_exists, not_and] at this
                exact this e' (mem_erase.mpr ⟨fun hne => heq (congrArg Sum.inr
                  (Prod.ext (hs1.symm.trans (by rw [hne])) (hs2.symm.trans (by rw [hne])))), he'⟩) hs1 hs2
              simp only [a, decide_eq_true_eq]
              exact hx_eq
          · have hne_lj : (Sum.inl j : VType n b) ≠ Sum.inr (gapSite n b hn origin gap i e.1.val, e.2) := by
              intro h; cases h
            dsimp only [a']
            rw [Function.update_of_ne hne_lj]
            exact hxg2 j
      rw [hG a'] at ha'_valid
      exact hB_still_false (ha'_valid B (Finset.mem_coe.mpr hBG))
    have hfilt_eq : B.filter (fun l => decide (l.1.isRight ∧ l.2)) =
        (toClause n b hn hb origin gap i c).filter (fun l => decide (l.1.isRight ∧ l.2)) := by
      ext l; constructor <;> intro hl
      · rw [mem_filter] at hl
        have hfalse := hBval l hl.1
        simp only [decide_eq_true_eq] at hl
        rcases l with ⟨v, pol⟩
        cases v with
        | inl j => simp at hl
        | inr se =>
          have hpol : pol = true := hl.2.2
          subst hpol
          simp only [a, Bool.not_true, decide_eq_false_iff_not, not_not] at hfalse
          obtain ⟨e, he, hs1, hs2⟩ := hfalse
          rw [mem_filter]
          refine ⟨mem_union_right _ (mem_image.mpr ⟨e, he, ?_⟩), by simp⟩
          rw [hs1, hs2]
      · rw [mem_filter] at hl
        exact mem_filter.mpr ⟨hsub hl.1, hl.2⟩
    exact ⟨B, hBG, hsub, hfilt_eq⟩
  -- Injectivity from positive edge part
  let proj : Clause (VType n b) → Clause (VType n b) := fun B => B.filter (fun l => decide (l.1.isRight ∧ l.2))
  have hproj_on_F : ∀ C ∈ fullFormula n b hn hb origin gap hv, proj C = C.filter (fun l => decide l.1.isRight) := by
    intro C hC; ext l; simp only [proj, toClause] at *; simp only [mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨h, h1, _⟩; exact ⟨h, h1⟩
    · rintro ⟨h, h1⟩; refine ⟨h, h1, ?_⟩
      obtain ⟨⟨i, ⟨c, hc⟩⟩, _, rfl⟩ := mem_image.mp hC
      simp only [toClause, cutBndLits, cutEdgeLits, mem_union, mem_image] at h
      rcases h with (hU | hV) | ⟨e, _, heq⟩
      · split at hU <;> simp only [mem_singleton, notMem_empty] at hU
        subst hU; simp at h1
      · split at hV <;> simp only [mem_singleton, notMem_empty] at hV
        subst hV; simp at h1
      · exact congrArg Prod.snd heq.symm
  have hmap : ∀ C (hC : C ∈ fullFormula n b hn hb origin gap hv),
      let B := Classical.choose (hex C hC)
      B ∈ G ∧ C ⊆ B ∧ proj B = proj C := fun C hC =>
    Classical.choose_spec (hex C hC)
  let pick : Clause (VType n b) → Clause (VType n b) := fun C =>
    if hC : C ∈ fullFormula n b hn hb origin gap hv then Classical.choose (hex C hC) else ∅
  have hpick_mem : ∀ C ∈ fullFormula n b hn hb origin gap hv, pick C ∈ G := fun C hC => by
    simp only [pick, dif_pos hC]; exact (Classical.choose_spec (hex C hC)).1
  have hpick_sub : ∀ C ∈ fullFormula n b hn hb origin gap hv, C ⊆ pick C := fun C hC => by
    simp only [pick, dif_pos hC]; exact (Classical.choose_spec (hex C hC)).2.1
  have hpick_inj : ∀ C1 ∈ fullFormula n b hn hb origin gap hv,
      ∀ C2 ∈ fullFormula n b hn hb origin gap hv, pick C1 = pick C2 → C1 = C2 := by
    intro C1 hC1 C2 hC2 heq
    have hp1 : proj (pick C1) = proj C1 := by simp only [pick, dif_pos hC1]; exact (Classical.choose_spec (hex C1 hC1)).2.2
    have hp2 : proj (pick C2) = proj C2 := by simp only [pick, dif_pos hC2]; exact (Classical.choose_spec (hex C2 hC2)).2.2
    have hpeq : proj C1 = proj C2 := hp1.symm.trans ((congrArg proj heq).trans hp2)
    rw [hproj_on_F C1 hC1, hproj_on_F C2 hC2] at hpeq
    obtain ⟨p1, _, rfl⟩ := mem_image.mp hC1
    obtain ⟨p2, _, rfl⟩ := mem_image.mp hC2
    have hfin : toClause n b hn hb origin gap p1.1 p1.2.val = toClause n b hn hb origin gap p2.1 p2.2.val := by
      -- Since positive right-part uniquely identifies p!
      have hsub_eq := hpeq
      have hf : ∀ i c, (toClause n b hn hb origin gap i c).filter (fun l => decide l.1.isRight) =
          cutEdgeLits n b hn origin gap i c := by
        intro i c; ext l; simp only [toClause, mem_filter, mem_union, cutBndLits, cutEdgeLits, mem_image]
        constructor
        · rintro ⟨h | ⟨e, he', rfl⟩, hr⟩
          · rcases h with hu | hv'
            · split at hu <;> simp only [mem_singleton, notMem_empty] at hu
              subst hu; simp at hr
            · split at hv' <;> simp only [mem_singleton, notMem_empty] at hv'
              subst hv'; simp at hr
          · exact ⟨e, he', rfl⟩
        · rintro ⟨e, he', rfl⟩; exact ⟨Or.inr ⟨e, he', rfl⟩, rfl⟩
      rw [hf, hf] at hsub_eq
      -- Reuse logic from toClause_inj directly via a quick intermediate lemma:
      have hne1 : (cutEdges p1.2.val).Nonempty := by
        have hcard : 0 < (cutEdges p1.2.val).card := by
          cases p1.2.val with
          | t1 => rw [cutEdges_card_t1]; exact hv.1 p1.1
          | t2 => rw [cutEdges_card_t2]; omega
          | t3 => rw [cutEdges_card_t3]; omega
          | t4 => rw [cutEdges_card_t4]; split_ifs <;> omega
        exact card_pos.mp hcard
      obtain ⟨e1, he1⟩ := hne1
      have hl1 : (Sum.inr (gapSite n b hn origin gap p1.1 e1.1.val, e1.2), true) ∈
          cutEdgeLits n b hn origin gap p1.1 p1.2.val := mem_image_of_mem _ he1
      rw [hsub_eq] at hl1
      obtain ⟨e2, _, he2⟩ := mem_image.mp hl1
      have hsite := (Prod.ext_iff.mp (Sum.inr.inj (congrArg Prod.fst he2))).1
      rcases p1 with ⟨i1, ⟨c1, hc1⟩⟩; rcases p2 with ⟨i2, ⟨c2, hc2⟩⟩
      dsimp only at hsite hsub_eq
      have hi_eq : i2 = i1 := gapSite_fst_eq n b hn origin gap hv hsite
      subst hi_eq
      have hce : cutEdges c1 = cutEdges c2 := by
        ext e; constructor <;> intro he
        · have hl : (Sum.inr (gapSite n b hn origin gap i2 e.1.val, e.2), true) ∈
              cutEdgeLits n b hn origin gap i2 c1 := mem_image_of_mem _ he
          rw [hsub_eq] at hl; obtain ⟨e', he', heq'⟩ := mem_image.mp hl
          have hs := Prod.ext_iff.mp (Sum.inr.inj (congrArg Prod.fst heq'))
          have he1 := gapSite_same_inj n b hn origin gap hv hs.1
          have : e' = e := Prod.ext he1 hs.2
          subst this; exact he'
        · have hl : (Sum.inr (gapSite n b hn origin gap i2 e.1.val, e.2), true) ∈
              cutEdgeLits n b hn origin gap i2 c2 := mem_image_of_mem _ he
          rw [← hsub_eq] at hl; obtain ⟨e', he', heq'⟩ := mem_image.mp hl
          have hs := Prod.ext_iff.mp (Sum.inr.inj (congrArg Prod.fst heq'))
          have he1 := gapSite_same_inj n b hn origin gap hv hs.1
          have : e' = e := Prod.ext he1 hs.2
          subst this; exact he'
      dsimp only at *; have hce_eq : c1 = c2 := cutEdges_inj (hv.1 i2) (decide (b = 1)) hc1 hc2 hce
      rw [hce_eq]
    exact hfin
  refine ⟨card_le_card_of_injOn pick hpick_mem hpick_inj, ?_⟩
  calc ∑ C ∈ fullFormula n b hn hb origin gap hv, C.card
      ≤ ∑ C ∈ fullFormula n b hn hb origin gap hv, (pick C).card :=
          sum_le_sum fun C hC => card_le_card (hpick_sub C hC)
    _ = ∑ B ∈ (fullFormula n b hn hb origin gap hv).image pick, B.card :=
          (sum_image hpick_inj).symm
    _ ≤ ∑ B ∈ G, B.card :=
          sum_le_sum_of_subset (image_subset_iff.mpr hpick_mem)

end CycleCNF

end PEqualNP.Outside.L_pcx_239_aux

open PEqualNP.Outside.L_pcx_239_aux in
theorem PEqualNP.Outside.L_pcx_239 :
    ∀ (n b : ℕ) (hn : 0 < n) (hb : 0 < b), b ≤ n → ∀ origin : Fin n,
      let E := Fin n × (Bool × Bool)
      let V := Sum (Fin b) E
      let pos := fun idx : ℕ => (⟨idx % n, Nat.mod_lt _ hn⟩ : Fin n)
      let valid := fun lengths : Fin b → ℕ => (∀ i, 0 < lengths i) ∧ (∑ i, lengths i) = n
      let balanced := fun distances : Fin b → ℕ => ∀ i j, distances i ≤ distances j + 1
      let enc := fun (layout : Fin b → ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause V)) =>
        ∀ a : V → Bool,
          (∃ x : Fin n → Bool, (∀ site : Fin n, a (Sum.inr
              (site, x site, x (pos (site.val + 1)))) = true) ∧
            ∀ i : Fin b, x (pos (origin.val + ∑ j ∈ Finset.univ.filter
              (fun z : Fin b => z.val < i.val), layout j)) = a (Sum.inl i)) ↔
          PEqualNP.ProofComplexity.Satisfies a (↑F : Set _)
      let clauses := fun h : ℕ => (if b = 1 then 7 else 9) * 2 ^ (h - 1) - h - 4
      let literals := fun size : ℕ => if size = 1 then (if b = 1 then 4 else 12)
        else (if b = 1 then 7 * size else 9 * size + 6) * 2 ^ (size - 1) - 4
      let best := fun f : ℕ → ℕ => (b - n % b) * f (n / b) + n % b * f (n / b + 1)
      (∃ gap : Fin b → ℕ, valid gap ∧ balanced gap) ∧
        ∀ gap : Fin b → ℕ, valid gap →
          let C := ∑ i, clauses (gap i)
          let L := ∑ i, literals (gap i)
          (∃ F : Finset (PEqualNP.ProofComplexity.Clause V),
            enc gap F ∧ F.card = C ∧ (∑ item ∈ F, item.card) = L) ∧
          (∀ G : Finset (PEqualNP.ProofComplexity.Clause V), enc gap G →
            C ≤ G.card ∧ L ≤ ∑ item ∈ G, item.card) ∧
          best clauses ≤ C ∧ best literals ≤ L ∧
          (C = best clauses ↔ balanced gap) ∧ (L = best literals ↔ balanced gap) := by
  intro n b hn hb hbn origin E V pos valid balanced enc clauses literals best
  refine ⟨exists_balanced_gap n b hb hbn, fun gap hv => ?_⟩
  intro C L
  let F := fullFormula n b hn hb origin gap hv
  have hcnt := fullFormula_counts n b hn hb origin gap hv
  have henc := fullFormula_enc n b hn hb origin gap hv
  have hcomp := competitor_lower n b hn hb origin gap hv
  have hbal_cl : best clauses ≤ C ∧ (C = best clauses ↔ balanced gap) := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb) with hb1 | hb2
    · have hb1' : b = 1 := hb1.symm; subst hb1'
      exact b1_balance_opt n hn clauses gap hv
    · exact convex_balance_opt n b hb clauses (clCost_strict_convex b hb2) gap hv
  have hbal_lit : best literals ≤ L ∧ (L = best literals ↔ balanced gap) := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb) with hb1 | hb2
    · have hb1' : b = 1 := hb1.symm; subst hb1'
      exact b1_balance_opt n hn literals gap hv
    · exact convex_balance_opt n b hb literals (litCost_strict_convex b hb2) gap hv
  refine ⟨⟨F, henc, hcnt.1, hcnt.2⟩, fun G hG => ?_, hbal_cl.1, hbal_lit.1, hbal_cl.2, hbal_lit.2⟩
  have h1 := hcomp G hG
  exact ⟨le_trans (le_of_eq hcnt.1.symm) h1.1, le_trans (le_of_eq hcnt.2.symm) h1.2⟩
