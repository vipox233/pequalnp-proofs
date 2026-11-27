import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_521_aux

lemma avg (Dq q K : ℕ) (f : ℕ → ℕ) (hD : 0 < Dq)
    (h : q * ∑ s ∈ Finset.range Dq, f s ≤ K * Dq) : ∃ s < Dq, q * f s ≤ K := by
  by_contra hc
  push_neg at hc
  have h1 : ∑ s ∈ Finset.range Dq, K < ∑ s ∈ Finset.range Dq, q * f s :=
    Finset.sum_lt_sum_of_nonempty (by simpa using hD.ne')
      (fun s hs => hc s (Finset.mem_range.mp hs))
  rw [← Finset.mul_sum] at h1
  simp at h1
  nlinarith

lemma exC (u : ℕ) (T : Finset (Fin u)) (q Dq : ℕ) (h : ℕ → Fin u → ℕ) (hD : 0 < Dq)
    (huniv : ∀ x z : Fin u, x ≠ z →
      q * ((Finset.range Dq).filter (fun s => h s x = h s z)).card ≤ Dq) :
    ∃ s < Dq, q * (T.offDiag.filter (fun p => h s p.1 = h s p.2)).card
      ≤ T.card * T.card - T.card := by
  apply avg Dq q _ _ hD
  have e : ∑ s ∈ Finset.range Dq, (T.offDiag.filter (fun p => h s p.1 = h s p.2)).card
      = ∑ p ∈ T.offDiag, ((Finset.range Dq).filter (fun s => h s p.1 = h s p.2)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [e, Finset.mul_sum, ← Finset.offDiag_card]
  calc _ ≤ ∑ p ∈ T.offDiag, Dq :=
        Finset.sum_le_sum (fun p hp => huniv p.1 p.2 (Finset.mem_offDiag.mp hp).2.2)
    _ = _ := by simp

lemma sq_sum (u m : ℕ) (S : Finset (Fin u)) (h : Fin u → ℕ) (hlt : ∀ x, h x < m) :
    ∑ j : Fin m, (S.filter (fun x => h x = j.val)).card ^ 2
      = ((S ×ˢ S).filter (fun p => h p.1 = h p.2)).card := by
  have e : ∀ j : Fin m, (S.filter (fun x => h x = j.val))
      = S.filter (fun x => (⟨h x, hlt x⟩ : Fin m) = j) := by
    intro j
    ext x
    simp [Fin.ext_iff]
  simp only [e]
  rw [Finset.card_filter, Finset.sum_product,
    ← Finset.sum_fiberwise_of_maps_to (g := fun x => (⟨h x, hlt x⟩ : Fin m))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sq, Finset.card_eq_sum_ones (S.filter _), Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hj := (Finset.mem_filter.mp hx).2
  rw [one_mul, ← Finset.card_eq_sum_ones, Finset.card_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [← hj, Fin.ext_iff, eq_comm]

lemma sq_le (u m : ℕ) (S : Finset (Fin u)) (h : Fin u → ℕ) (hlt : ∀ x, h x < m) :
    ∑ j : Fin m, (S.filter (fun x => h x = j.val)).card ^ 2
      ≤ S.card + (S.offDiag.filter (fun p => h p.1 = h p.2)).card := by
  rw [sq_sum u m S h hlt, ← Finset.diag_union_offDiag, Finset.filter_union]
  refine (Finset.card_union_le _ _).trans ?_
  have := Finset.card_filter_le S.diag (fun p => h p.1 = h p.2)
  rw [Finset.diag_card] at this
  omega

lemma second (u : ℕ) (T : Finset (Fin u)) (q Dq : ℕ) (h : ℕ → Fin u → ℕ) (hD : 0 < Dq)
    (hq : q = max 1 (T.card ^ 2))
    (huniv : ∀ x z : Fin u, x ≠ z →
      q * ((Finset.range Dq).filter (fun s => h s x = h s z)).card ≤ Dq) :
    ∃ s < Dq, Set.InjOn (h s) (↑T : Set (Fin u)) := by
  obtain ⟨s, hs, hle⟩ := exC u T q Dq h hD huniv
  refine ⟨s, hs, ?_⟩
  have hlt : T.card * T.card - T.card < q := by
    have h1 : T.card ^ 2 ≤ q := hq ▸ le_max_right _ _
    have h2 : 1 ≤ q := hq ▸ le_max_left _ _
    rw [sq] at h1
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · rw [h0]; omega
    · have : 0 < T.card * T.card := Nat.mul_pos h0 h0
      omega
  have hz : (T.offDiag.filter (fun p => h s p.1 = h s p.2)).card = 0 := by
    by_contra hne
    have : q * 1 ≤ q * (T.offDiag.filter (fun p => h s p.1 = h s p.2)).card :=
      Nat.mul_le_mul_left q (Nat.one_le_iff_ne_zero.mpr hne)
    omega
  intro x hx z hz' hxz
  by_contra hne
  have hmem : (x, z) ∈ T.offDiag.filter (fun p => h s p.1 = h s p.2) := by
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    exact ⟨⟨Finset.mem_coe.mp hx, Finset.mem_coe.mp hz', hne⟩, hxz⟩
  rw [Finset.card_eq_zero] at hz
  rw [hz] at hmem
  simp at hmem

end PEqualNP.Outside.L_lib_521_aux

theorem PEqualNP.Outside.L_lib_521 : ∀ (u : Nat) (S : Finset (Fin u)) (D : Nat → Nat) (H : Nat → Nat → Fin u → Nat),
  S.Nonempty →
  (∀ q : Nat, 0 < q → 0 < D q ∧ (∀ s < D q, ∀ x, H q s x < q) ∧
    ∀ x z : Fin u, x ≠ z → q * ((Finset.range (D q)).filter (fun s => H q s x = H q s z)).card ≤ D q) →
  let m := S.card
  ∃ first < D m,
    let bin := fun (j : Fin m) => S.filter (fun x => H m first x = j.val)
    let cap := fun (j : Fin m) => max 1 ((bin j).card^2)
    (∑ j : Fin m, cap j) ≤ 3*m ∧
    ∀ j : Fin m, ∃ second < D (cap j), Set.InjOn (H (cap j) second) (↑(bin j) : Set (Fin u)) := by
  intro u S D H hne hyp
  intro m
  have hm : 0 < m := Finset.card_pos.mpr hne
  obtain ⟨hD, hlt, huniv⟩ := hyp m hm
  obtain ⟨first, hf, hle⟩ := PEqualNP.Outside.L_lib_521_aux.exC u S m (D m) (H m) hD huniv
  refine ⟨first, hf, ?_⟩
  intro bin cap
  constructor
  · have h1 := PEqualNP.Outside.L_lib_521_aux.sq_le u m S (H m first) (hlt first hf)
    have h2 : (S.offDiag.filter (fun p => H m first p.1 = H m first p.2)).card ≤ m - 1 := by
      apply Nat.le_of_mul_le_mul_left _ hm
      rw [Nat.mul_sub, mul_one]
      exact hle
    have h3 : ∑ j : Fin m, cap j ≤ ∑ j : Fin m, (1 + (bin j).card ^ 2) := by
      refine Finset.sum_le_sum fun j _ => ?_
      show max 1 ((bin j).card ^ 2) ≤ _
      have := Nat.zero_le ((bin j).card ^ 2)
      omega
    rw [Finset.sum_add_distrib] at h3
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h3
    have h4 : ∑ j : Fin m, (bin j).card ^ 2 ≤ S.card + (m - 1) := h1.trans (by omega)
    have h5 : S.card = m := rfl
    omega
  · intro j
    have hq : 0 < cap j := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)
    obtain ⟨hD2, -, huniv2⟩ := hyp (cap j) hq
    exact PEqualNP.Outside.L_lib_521_aux.second u (bin j) (cap j) (D (cap j)) (H (cap j)) hD2 rfl huniv2
