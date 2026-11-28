import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_937

variable {n : ℕ}

def chg (cost : Fin n → ℕ) (C : Finset (Fin n)) : ℕ := ∑ i ∈ C, cost i

def clipF (budget : ℕ) (cost : Fin n → ℕ) (groups : Finset (Finset (Fin n))) (t : ℚ) : ℚ :=
  (∑ C ∈ groups, min 1 (t * (chg cost C : ℚ))) - t * (budget : ℚ)

def fitsF (cost : Fin n → ℕ) (price : ℚ) (w : Fin n → ℚ) (z : Fin n → Fin n → ℚ) : Prop :=
  0 ≤ price ∧ price ≤ 1 ∧ (∀ i, 0 ≤ w i ∧ w i ≤ price * (cost i : ℚ)) ∧
    (∀ i j, 0 ≤ z i j ∧ z i j ≤ w j) ∧
    ∀ i, w i + (∑ j : Fin n, if i < j then w j - z i j else 0) ≤ 1

def scoreF (budget : ℕ) (groups : Finset (Finset (Fin n))) (price : ℚ) (w : Fin n → ℚ)
    (z : Fin n → Fin n → ℚ) : ℚ :=
  (∑ C ∈ groups, ∑ i ∈ C, (w i - (∑ j ∈ C, if i < j then z i j else 0))) -
    price * (budget : ℚ)

def remainF (groups : Finset (Finset (Fin n))) (R : Finset (Fin n)) : ℕ :=
  (groups.filter (fun C => ¬ C ⊆ R)).card

theorem chg_cast (cost : Fin n → ℕ) (C : Finset (Fin n)) :
    (chg cost C : ℚ) = ∑ i ∈ C, (cost i : ℚ) := by
  simp [chg]

theorem class_le_t {cost : Fin n → ℕ} {t : ℚ} {v : Fin n → ℚ} {d : Fin n → Fin n → ℚ}
    (h : fitsF cost t v d) (C : Finset (Fin n)) :
    ∑ i ∈ C, (v i - (∑ j ∈ C, if i < j then d i j else 0)) ≤ t * (chg cost C : ℚ) := by
  calc ∑ i ∈ C, (v i - (∑ j ∈ C, if i < j then d i j else 0))
      ≤ ∑ i ∈ C, v i := by
        apply Finset.sum_le_sum
        intro i _
        apply sub_le_self
        apply Finset.sum_nonneg
        intro j _
        split_ifs
        · exact (h.2.2.2.1 i j).1
        · exact le_refl _
    _ ≤ ∑ i ∈ C, t * (cost i : ℚ) := Finset.sum_le_sum fun i _ => (h.2.2.1 i).2
    _ = t * (chg cost C : ℚ) := by rw [← Finset.mul_sum, chg_cast]

theorem class_le_one {cost : Fin n → ℕ} {t : ℚ} {v : Fin n → ℚ} {d : Fin n → Fin n → ℚ}
    (h : fitsF cost t v d) (C : Finset (Fin n)) (hC : C.Nonempty) :
    ∑ i ∈ C, (v i - (∑ j ∈ C, if i < j then d i j else 0)) ≤ 1 := by
  set i0 := C.min' hC with hi0def
  have hi0 : i0 ∈ C := C.min'_mem hC
  have hinner : ∀ i, 0 ≤ ∑ j ∈ C, (if i < j then d i j else 0) := by
    intro i
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact (h.2.2.2.1 i j).1
    · exact le_refl _
  have hfilter : C.filter (fun j => i0 < j) = C.erase i0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hj, hlt⟩; exact ⟨ne_of_gt hlt, hj⟩
    · rintro ⟨hne, hj⟩
      exact ⟨hj, lt_of_le_of_ne (C.min'_le j hj) (Ne.symm hne)⟩
  have hsplit : ∑ i ∈ C, v i = v i0 + ∑ j ∈ C, (if i0 < j then v j else 0) := by
    rw [← Finset.sum_filter, hfilter, Finset.add_sum_erase C v hi0]
  calc ∑ i ∈ C, (v i - (∑ j ∈ C, if i < j then d i j else 0))
      = ∑ i ∈ C, v i - ∑ i ∈ C, ∑ j ∈ C, (if i < j then d i j else 0) :=
        Finset.sum_sub_distrib _ _
    _ ≤ ∑ i ∈ C, v i - ∑ j ∈ C, (if i0 < j then d i0 j else 0) := by
        apply sub_le_sub_left
        exact Finset.single_le_sum (f := fun i => ∑ j ∈ C, (if i < j then d i j else 0))
          (fun i _ => hinner i) hi0
    _ = v i0 + ∑ j ∈ C, (if i0 < j then v j - d i0 j else 0) := by
        rw [hsplit, add_sub_assoc, ← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
    _ ≤ v i0 + ∑ j : Fin n, (if i0 < j then v j - d i0 j else 0) := by
        apply add_le_add_right
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        intro j _ _
        split_ifs
        · exact sub_nonneg.mpr (h.2.2.2.1 i0 j).2
        · exact le_refl _
    _ ≤ 1 := h.2.2.2.2 i0

theorem weak {budget : ℕ} {cost : Fin n → ℕ} {groups : Finset (Finset (Fin n))}
    (hne : ∀ C ∈ groups, C.Nonempty) {t : ℚ} {v : Fin n → ℚ} {d : Fin n → Fin n → ℚ}
    (h : fitsF cost t v d) : scoreF budget groups t v d ≤ clipF budget cost groups t := by
  unfold scoreF clipF
  apply sub_le_sub_right
  apply Finset.sum_le_sum
  intro C hC
  exact le_min (class_le_one h C (hne C hC)) (class_le_t h C)

theorem dual {budget : ℕ} {cost : Fin n → ℕ} {groups : Finset (Finset (Fin n))}
    (hdisj : ∀ C ∈ groups, ∀ E ∈ groups, C ≠ E → Disjoint C E) {p : ℚ} (hp0 : 0 ≤ p)
    (S : Finset (Fin n)) (hS : chg cost S ≤ budget) :
    clipF budget cost groups p ≤ (remainF groups S : ℚ) := by
  unfold clipF remainF
  have h1 : ∑ C ∈ groups, min 1 (p * (chg cost C : ℚ)) ≤
      ∑ C ∈ groups, (if C ⊆ S then p * (chg cost C : ℚ) else 1) := by
    apply Finset.sum_le_sum
    intro C _
    split_ifs
    · exact min_le_right _ _
    · exact min_le_left _ _
  rw [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum] at h1
  have h2 : ∑ C ∈ groups.filter (fun C => C ⊆ S), chg cost C ≤ chg cost S := by
    have hb : ∑ C ∈ groups.filter (fun C => C ⊆ S), chg cost C =
        chg cost ((groups.filter (fun C => C ⊆ S)).biUnion id) := by
      unfold chg
      rw [Finset.sum_biUnion]
      · rfl
      · intro C hC E hE hCE
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hC hE
        exact hdisj C hC.1 E hE.1 hCE
    rw [hb]
    apply Finset.sum_le_sum_of_subset
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_filter, id] at hx
    obtain ⟨C, ⟨_, hCS⟩, hxC⟩ := hx
    exact hCS hxC
  have h3 : (∑ C ∈ groups.filter (fun C => C ⊆ S), (chg cost C : ℚ)) ≤ (budget : ℚ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast h2.trans hS
  have h4 := mul_le_mul_of_nonneg_left h3 hp0
  linarith

section Attain

variable {budget : ℕ} {cost : Fin n → ℕ} {groups : Finset (Finset (Fin n))}

noncomputable def lam (cost : Fin n → ℕ) (p : ℚ) (C : Finset (Fin n)) : ℚ :=
  if p * (chg cost C : ℚ) ≤ 1 then 1 else 1 / (p * (chg cost C : ℚ))

noncomputable def wA (cost : Fin n → ℕ) (groups : Finset (Finset (Fin n))) (p : ℚ) (i : Fin n) : ℚ :=
  ∑ C ∈ groups, if i ∈ C then p * (cost i : ℚ) * lam cost p C else 0

noncomputable def zA (cost : Fin n → ℕ) (groups : Finset (Finset (Fin n))) (p : ℚ)
    (i j : Fin n) : ℚ :=
  if ∃ C ∈ groups, i ∈ C ∧ j ∈ C then 0 else wA cost groups p j

theorem lam_nonneg (p : ℚ) (C : Finset (Fin n)) : 0 ≤ lam cost p C := by
  unfold lam
  split_ifs with h
  · exact zero_le_one
  · push_neg at h
    exact le_of_lt (one_div_pos.mpr (lt_trans zero_lt_one h))

theorem lam_le_one (p : ℚ) (C : Finset (Fin n)) : lam cost p C ≤ 1 := by
  unfold lam
  split_ifs with h
  · exact le_refl _
  · push_neg at h
    exact (div_le_one (lt_trans zero_lt_one h)).mpr h.le

theorem mul_lam (p : ℚ) (C : Finset (Fin n)) :
    p * (chg cost C : ℚ) * lam cost p C = min 1 (p * (chg cost C : ℚ)) := by
  unfold lam
  split_ifs with h
  · rw [mul_one, min_eq_right h]
  · push_neg at h
    rw [min_eq_left h.le, mul_one_div_cancel (ne_of_gt (lt_trans zero_lt_one h))]

variable (hdisj : ∀ C ∈ groups, ∀ E ∈ groups, C ≠ E → Disjoint C E)
include hdisj

theorem wA_of_mem {p : ℚ} {C : Finset (Fin n)} (hC : C ∈ groups) {i : Fin n} (hi : i ∈ C) :
    wA cost groups p i = p * (cost i : ℚ) * lam cost p C := by
  unfold wA
  rw [Finset.sum_eq_single C]
  · rw [if_pos hi]
  · intro E hE hEC
    rw [if_neg]
    intro hiE
    exact Finset.disjoint_left.mp (hdisj E hE C hC hEC) hiE hi
  · intro h; exact absurd hC h

omit hdisj in
theorem wA_of_none {p : ℚ} {i : Fin n} (h : ¬ ∃ C ∈ groups, i ∈ C) : wA cost groups p i = 0 := by
  unfold wA
  apply Finset.sum_eq_zero
  intro C hC
  rw [if_neg]
  intro hi
  exact h ⟨C, hC, hi⟩

theorem wA_bounds {p : ℚ} (hp0 : 0 ≤ p) (i : Fin n) :
    0 ≤ wA cost groups p i ∧ wA cost groups p i ≤ p * (cost i : ℚ) := by
  have hpc : 0 ≤ p * (cost i : ℚ) := mul_nonneg hp0 (Nat.cast_nonneg _)
  by_cases h : ∃ C ∈ groups, i ∈ C
  · obtain ⟨C, hC, hi⟩ := h
    rw [wA_of_mem hdisj hC hi]
    exact ⟨mul_nonneg hpc (lam_nonneg p C), mul_le_of_le_one_right hpc (lam_le_one p C)⟩
  · rw [wA_of_none h]
    exact ⟨le_refl _, hpc⟩

theorem wA_class_sum {p : ℚ} {C : Finset (Fin n)} (hC : C ∈ groups) :
    ∑ i ∈ C, wA cost groups p i = min 1 (p * (chg cost C : ℚ)) := by
  rw [Finset.sum_congr rfl (fun i hi => wA_of_mem hdisj hC hi), ← Finset.sum_mul,
    ← Finset.mul_sum, ← chg_cast, mul_lam]

theorem same_class_iff {C : Finset (Fin n)} (hC : C ∈ groups) {i : Fin n} (hi : i ∈ C)
    (j : Fin n) : (∃ E ∈ groups, i ∈ E ∧ j ∈ E) ↔ j ∈ C := by
  constructor
  · rintro ⟨E, hE, hiE, hjE⟩
    by_contra hjC
    have hEC : E ≠ C := fun h => hjC (h ▸ hjE)
    exact Finset.disjoint_left.mp (hdisj E hE C hC hEC) hiE hi
  · intro hj; exact ⟨C, hC, hi, hj⟩

theorem attain {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fitsF cost p (wA cost groups p) (zA cost groups p) ∧
      scoreF budget groups p (wA cost groups p) (zA cost groups p) =
        clipF budget cost groups p := by
  have hw := wA_bounds (cost := cost) hdisj hp0
  refine ⟨⟨hp0, hp1, hw, ?_, ?_⟩, ?_⟩
  · intro i j
    unfold zA
    split_ifs
    · exact ⟨le_refl _, (hw j).1⟩
    · exact ⟨(hw j).1, le_refl _⟩
  · intro i
    by_cases h : ∃ C ∈ groups, i ∈ C
    · obtain ⟨C, hC, hi⟩ := h
      have hz : ∀ j, wA cost groups p j - zA cost groups p i j =
          if j ∈ C then wA cost groups p j else 0 := by
        intro j
        unfold zA
        by_cases hj : j ∈ C
        · rw [if_pos ((same_class_iff hdisj hC hi j).mpr hj), if_pos hj, sub_zero]
        · rw [if_neg (fun h' => hj ((same_class_iff hdisj hC hi j).mp h')), if_neg hj, sub_self]
      have h1 : (∑ j : Fin n, if i < j then wA cost groups p j - zA cost groups p i j else 0) =
          ∑ j ∈ C, if i < j then wA cost groups p j else 0 := by
        simp only [hz]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ C)]
        rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun j => ¬ j ∈ C))]
        · rw [add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_pos hj]
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [if_neg hj]; split_ifs <;> rfl
      rw [h1]
      have h2 : (∑ j ∈ C, if i < j then wA cost groups p j else 0) ≤
          ∑ j ∈ C.erase i, wA cost groups p j := by
        rw [← Finset.sum_erase C (a := i) (f := fun j => if i < j then wA cost groups p j else 0)
          (by simp)]
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · exact le_refl _
        · exact (hw j).1
      calc wA cost groups p i + (∑ j ∈ C, if i < j then wA cost groups p j else 0)
          ≤ wA cost groups p i + ∑ j ∈ C.erase i, wA cost groups p j := add_le_add_right h2 _
        _ = ∑ j ∈ C, wA cost groups p j := Finset.add_sum_erase C _ hi
        _ = min 1 (p * (chg cost C : ℚ)) := wA_class_sum hdisj hC
        _ ≤ 1 := min_le_left _ _
    · rw [wA_of_none h]
      have : ∀ j, (if i < j then wA cost groups p j - zA cost groups p i j else 0) = 0 := by
        intro j
        unfold zA
        rw [if_neg (show ¬ ∃ E ∈ groups, i ∈ E ∧ j ∈ E from
          fun ⟨C, hC, hi, _⟩ => h ⟨C, hC, hi⟩)]
        split_ifs <;> simp
      simp [this]
  · unfold scoreF clipF
    congr 1
    apply Finset.sum_congr rfl
    intro C hC
    rw [← wA_class_sum hdisj hC]
    apply Finset.sum_congr rfl
    intro i hi
    have : ∀ j ∈ C, (if i < j then zA cost groups p i j else 0) = 0 := by
      intro j hj
      unfold zA
      rw [if_pos (show ∃ E ∈ groups, i ∈ E ∧ j ∈ E from ⟨C, hC, hi, hj⟩)]
      split_ifs <;> rfl
    rw [Finset.sum_eq_zero this, sub_zero]

end Attain

section Choose

variable {budget : ℕ} {cost : Fin n → ℕ} {groups : Finset (Finset (Fin n))}


theorem sum_ite_sub {Q : Finset (Finset (Fin n))} (hQ : Q ⊆ groups) (a : Finset (Fin n) → ℚ) :
    (∑ C ∈ groups, if C ∈ Q then a C else 0) = ∑ C ∈ Q, a C := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hQ]

theorem choose (hne : ∀ C ∈ groups, C.Nonempty)
    (hdisj : ∀ C ∈ groups, ∀ E ∈ groups, C ≠ E → Disjoint C E) :
    ∃ (p : ℚ) (R : Finset (Fin n)), 0 ≤ p ∧ p ≤ 1 ∧
      (p = 0 ∨ ∃ C ∈ groups, 0 < chg cost C ∧ p * (chg cost C : ℚ) = 1) ∧
      (∀ t : ℚ, 0 ≤ t → t ≤ 1 → clipF budget cost groups t ≤ clipF budget cost groups p) ∧
      chg cost R ≤ budget ∧ (remainF groups R : ℚ) < clipF budget cost groups p + 1 := by
  set Fam := groups.powerset.filter (fun P => ∑ C ∈ P, chg cost C ≤ budget ∧
    ∀ C ∈ P, ∀ E ∈ groups, chg cost E < chg cost C → E ∈ P) with hFam
  have h0 : (∅ : Finset (Finset (Fin n))) ∈ Fam := by simp [Fam]
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image Fam Finset.card ⟨∅, h0⟩
  simp only [Fam, Finset.mem_filter, Finset.mem_powerset] at hP
  obtain ⟨hPsub, hPsum, hPpre⟩ := hP
  set R := P.biUnion id with hRdef
  have hRchg : chg cost R = ∑ C ∈ P, chg cost C := by
    unfold chg
    rw [hRdef, Finset.sum_biUnion]
    · rfl
    · intro C hC E hE hCE
      exact hdisj C (hPsub hC) E (hPsub hE) hCE
  have hrem : remainF groups R = (groups \ P).card := by
    unfold remainF
    congr 1
    ext C
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hC, hnot⟩
      exact ⟨hC, fun hCP => hnot (Finset.subset_biUnion_of_mem id hCP)⟩
    · rintro ⟨hC, hCP⟩
      refine ⟨hC, fun hsub => ?_⟩
      obtain ⟨x, hx⟩ := hne C hC
      have hxR := hsub hx
      simp only [hRdef, Finset.mem_biUnion, id] at hxR
      obtain ⟨E, hE, hxE⟩ := hxR
      have hEC : C ≠ E := fun h => hCP (h ▸ hE)
      exact Finset.disjoint_left.mp (hdisj C hC E (hPsub hE) hEC) hx hxE
  have hsumQ : (∑ C ∈ P, (chg cost C : ℚ)) ≤ budget := by
    rw [← Nat.cast_sum]; exact_mod_cast hPsum
  by_cases hall : groups \ P = ∅
  · have hgP : groups = P :=
      Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hall) hPsub
    refine ⟨0, R, le_refl _, zero_le_one, Or.inl rfl, ?_, ?_, ?_⟩
    · intro t ht0 _
      have hc0 : clipF budget cost groups 0 = 0 := by unfold clipF; simp
      rw [hc0]
      unfold clipF
      have hb : (∑ C ∈ groups, (chg cost C : ℚ)) ≤ budget := by rw [hgP]; exact hsumQ
      calc (∑ C ∈ groups, min 1 (t * (chg cost C : ℚ))) - t * (budget : ℚ)
          ≤ (∑ C ∈ groups, t * (chg cost C : ℚ)) - t * (budget : ℚ) :=
            sub_le_sub_right (Finset.sum_le_sum fun C _ => min_le_right _ _) _
        _ = t * ((∑ C ∈ groups, (chg cost C : ℚ)) - budget) := by rw [← Finset.mul_sum]; ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith)
    · rw [hRchg]; exact hPsum
    · rw [hrem, hall]
      unfold clipF
      simp
  · obtain ⟨Cs, hCs, hmin⟩ := Finset.exists_min_image (groups \ P) (chg cost)
      (Finset.nonempty_iff_ne_empty.mpr hall)
    have hCs' := Finset.mem_sdiff.mp hCs
    have hover : budget < ∑ C ∈ P, chg cost C + chg cost Cs := by
      by_contra hle
      push_neg at hle
      have hmem : insert Cs P ∈ Fam := by
        simp only [Fam, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.insert_subset hCs'.1 hPsub, ?_, ?_⟩
        · rw [Finset.sum_insert hCs'.2]; omega
        · intro C hC E hE hlt
          rw [Finset.mem_insert] at hC ⊢
          rcases hC with rfl | hC
          · right
            by_contra hEP
            exact absurd (hmin E (Finset.mem_sdiff.mpr ⟨hE, hEP⟩)) (not_le.mpr hlt)
          · right; exact hPpre C hC E hE hlt
      have hc := hmax _ hmem
      rw [Finset.card_insert_of_notMem hCs'.2] at hc
      omega
    have hPle : ∀ C ∈ P, chg cost C ≤ chg cost Cs := by
      intro C hC
      by_contra h
      push_neg at h
      exact hCs'.2 (hPpre C hC Cs hCs'.1 h)
    have hcpos : 0 < chg cost Cs := by omega
    set c : ℚ := (chg cost Cs : ℚ) with hcdef
    have hc1 : (1 : ℚ) ≤ c := by rw [hcdef]; exact_mod_cast hcpos
    have hc0 : (0 : ℚ) < c := by linarith
    set p : ℚ := 1 / c with hpdef
    have hp0 : 0 ≤ p := le_of_lt (one_div_pos.mpr hc0)
    have hp1 : p ≤ 1 := (div_le_one hc0).mpr hc1
    have hpc : p * c = 1 := one_div_mul_cancel (ne_of_gt hc0)
    have hminP : ∀ C ∈ P, min 1 (p * (chg cost C : ℚ)) = p * (chg cost C : ℚ) := by
      intro C hC
      apply min_eq_right
      have : (chg cost C : ℚ) ≤ c := by rw [hcdef]; exact_mod_cast hPle C hC
      calc p * (chg cost C : ℚ) ≤ p * c := mul_le_mul_of_nonneg_left this hp0
        _ = 1 := hpc
    have hminN : ∀ C ∈ groups \ P, min 1 (p * (chg cost C : ℚ)) = 1 := by
      intro C hC
      apply min_eq_left
      have : c ≤ (chg cost C : ℚ) := by rw [hcdef]; exact_mod_cast hmin C hC
      calc (1 : ℚ) = p * c := hpc.symm
        _ ≤ p * (chg cost C : ℚ) := mul_le_mul_of_nonneg_left this hp0
    have hclip : clipF budget cost groups p =
        p * (∑ C ∈ P, (chg cost C : ℚ)) + ((groups \ P).card : ℚ) - p * budget := by
      unfold clipF
      rw [← Finset.sum_sdiff hPsub, Finset.sum_congr rfl hminN, Finset.sum_congr rfl hminP,
        Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
      ring
    have hoverQ : (budget : ℚ) < (∑ C ∈ P, (chg cost C : ℚ)) + c := by
      rw [← Nat.cast_sum, hcdef]; exact_mod_cast hover
    refine ⟨p, R, hp0, hp1, Or.inr ⟨Cs, hCs'.1, hcpos, hpc⟩, ?_, ?_, ?_⟩
    · intro t ht0 _
      have key : (∑ C ∈ groups, (min 1 (t * (chg cost C : ℚ)) - min 1 (p * (chg cost C : ℚ))))
          ≤ (t - p) * budget := by
        rcases le_or_gt p t with hpt | htp
        · calc (∑ C ∈ groups, (min 1 (t * (chg cost C : ℚ)) - min 1 (p * (chg cost C : ℚ))))
              ≤ ∑ C ∈ groups, (if C ∈ P then (t - p) * (chg cost C : ℚ) else 0) := by
                apply Finset.sum_le_sum
                intro C hC
                split_ifs with hCP
                · rw [hminP C hCP]
                  have := min_le_right 1 (t * (chg cost C : ℚ))
                  linarith
                · rw [hminN C (Finset.mem_sdiff.mpr ⟨hC, hCP⟩)]
                  have := min_le_left 1 (t * (chg cost C : ℚ))
                  linarith
            _ = (t - p) * ∑ C ∈ P, (chg cost C : ℚ) := by
                rw [sum_ite_sub hPsub, Finset.mul_sum]
            _ ≤ (t - p) * budget := mul_le_mul_of_nonneg_left hsumQ (sub_nonneg.mpr hpt)
        · have hQ : insert Cs P ⊆ groups := Finset.insert_subset hCs'.1 hPsub
          calc (∑ C ∈ groups, (min 1 (t * (chg cost C : ℚ)) - min 1 (p * (chg cost C : ℚ))))
              ≤ ∑ C ∈ groups, (if C ∈ insert Cs P then (t - p) * (chg cost C : ℚ) else 0) := by
                apply Finset.sum_le_sum
                intro C hC
                split_ifs with hCQ
                · have hle : (chg cost C : ℚ) ≤ c := by
                    rw [Finset.mem_insert] at hCQ
                    rcases hCQ with rfl | hCP
                    · exact le_refl _
                    · rw [hcdef]; exact_mod_cast hPle C hCP
                  have hpm : min 1 (p * (chg cost C : ℚ)) = p * (chg cost C : ℚ) := by
                    apply min_eq_right
                    calc p * (chg cost C : ℚ) ≤ p * c := mul_le_mul_of_nonneg_left hle hp0
                      _ = 1 := hpc
                  rw [hpm]
                  have := min_le_right 1 (t * (chg cost C : ℚ))
                  linarith
                · have : min 1 (t * (chg cost C : ℚ)) ≤ min 1 (p * (chg cost C : ℚ)) :=
                    min_le_min_left 1 (mul_le_mul_of_nonneg_right htp.le (Nat.cast_nonneg _))
                  linarith
            _ = (t - p) * (c + ∑ C ∈ P, (chg cost C : ℚ)) := by
                rw [sum_ite_sub hQ, Finset.sum_insert hCs'.2, mul_add, Finset.mul_sum]
            _ ≤ (t - p) * budget := by
                apply mul_le_mul_of_nonpos_left _ (by linarith)
                linarith
      unfold clipF
      rw [Finset.sum_sub_distrib] at key
      linarith
    · rw [hRchg]; exact hPsum
    · rw [hrem, hclip]
      have h1 : p * ((budget : ℚ) - ∑ C ∈ P, (chg cost C : ℚ)) < p * c := by
        apply mul_lt_mul_of_pos_left _ (one_div_pos.mpr hc0)
        linarith
      rw [hpc, mul_sub] at h1
      linarith

end Choose

end PEqualNP.Outside.L_lib_937

theorem PEqualNP.Outside.L_lib_937 : (∀ (n budget : ℕ) (cost : Fin n → ℕ) (groups : Finset (Finset (Fin n))),
  (∀ C ∈ groups, C.Nonempty) →
  (∀ C ∈ groups, ∀ E ∈ groups, C ≠ E → Disjoint C E) →
  let W := Fin n → ℚ
  let D := Fin n → Fin n → ℚ
  let fits := fun (price : ℚ) (w : W) (z : D) =>
    0 ≤ price ∧ price ≤ 1 ∧ (∀ i, 0 ≤ w i ∧ w i ≤ price * (cost i : ℚ)) ∧
    (∀ i j, 0 ≤ z i j ∧ z i j ≤ w j) ∧
    ∀ i, w i + (∑ j : Fin n, if i < j then w j - z i j else 0) ≤ 1
  let charge := fun R : Finset (Fin n) => ∑ i ∈ R, cost i
  let remain := fun R : Finset (Fin n) => (groups.filter (fun C => ¬ C ⊆ R)).card
  let clip := fun price : ℚ =>
    (∑ C ∈ groups, min 1 (price * (charge C : ℚ))) - price * (budget : ℚ)
  let pairScore := fun (price : ℚ) (w : W) (z : D) =>
    (∑ C ∈ groups, ∑ i ∈ C, (w i - (∑ j ∈ C, if i < j then z i j else 0))) -
      price * (budget : ℚ)
  ∃ (price : ℚ) (w : W) (z : D) (R : Finset (Fin n)),
    fits price w z ∧ (price = 0 ∨ ∃ C ∈ groups, 0 < charge C ∧ price * (charge C : ℚ) = 1) ∧
    pairScore price w z = clip price ∧
    (∀ t : ℚ, 0 ≤ t → t ≤ 1 → clip t ≤ clip price) ∧
    (∀ (t : ℚ) (v : W) (discount : D), fits t v discount → pairScore t v discount ≤ clip price) ∧
    charge R ≤ budget ∧ (remain R : ℚ) < clip price + 1 ∧
    ∀ S : Finset (Fin n), charge S ≤ budget → clip price ≤ (remain S : ℚ)) := by

  intro n budget cost groups hne hdisj W D fits charge remain clip pairScore
  obtain ⟨p, R, hp0, hp1, hform, hmax, hR, hrem⟩ :=
    PEqualNP.Outside.L_lib_937.choose (budget := budget) (cost := cost) hne hdisj
  obtain ⟨hfits, hscore⟩ :=
    PEqualNP.Outside.L_lib_937.attain (budget := budget) (cost := cost) hdisj hp0 hp1
  refine ⟨p, PEqualNP.Outside.L_lib_937.wA cost groups p,
    PEqualNP.Outside.L_lib_937.zA cost groups p, R, hfits, hform, hscore, hmax, ?_, hR, hrem, ?_⟩
  · intro t v d h
    exact (PEqualNP.Outside.L_lib_937.weak (budget := budget) hne h).trans (hmax t h.1 h.2.1)
  · intro S hS
    exact PEqualNP.Outside.L_lib_937.dual hdisj hp0 S hS
