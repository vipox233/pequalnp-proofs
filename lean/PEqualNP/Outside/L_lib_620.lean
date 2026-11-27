import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_620_aux

lemma majority_halve {n : ℕ} (G : Fin n → Fin n → Bool) (S C : Finset (Fin n)) :
    ∃ (C' : Finset (Fin n)) (b : Fin n → Bool),
      C' ⊆ C ∧ C.card ≤ 2 ^ S.card * C'.card ∧ ∀ x ∈ S, ∀ y ∈ C', G x y = b x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨C, fun _ => false, Finset.Subset.refl C, by simp, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | @insert a s has ih =>
    obtain ⟨C1, b1, hC1sub, hC1card, hC1eq⟩ := ih
    let CT := C1.filter (fun y => G a y = true)
    let CF := C1.filter (fun y => G a y = false)
    have hsplit : CT.card + CF.card = C1.card := by
      rw [← Finset.card_union_of_disjoint]
      · have hun : CT ∪ CF = C1 := by
          ext y
          simp only [CT, CF, Finset.mem_union, Finset.mem_filter]
          cases G a y <;> simp
        rw [hun]
      · rw [Finset.disjoint_left]
        intro y h1 h2
        simp only [CT, CF, Finset.mem_filter] at h1 h2
        rw [h1.2] at h2
        exact Bool.noConfusion h2.2
    rw [Finset.card_insert_of_notMem has, pow_succ]
    by_cases hle : CF.card ≤ CT.card
    · refine ⟨CT, fun x => if x = a then true else b1 x,
        Finset.Subset.trans (Finset.filter_subset _ _) hC1sub, ?_, ?_⟩
      · have h2 : C1.card ≤ 2 * CT.card := by omega
        calc C.card ≤ 2 ^ s.card * C1.card := hC1card
          _ ≤ 2 ^ s.card * (2 * CT.card) := Nat.mul_le_mul_left _ h2
          _ = 2 ^ s.card * 2 * CT.card := by ring
      · intro x hx y hy
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hxs
        · simp only [↓reduceIte]
          exact (Finset.mem_filter.mp hy).2
        · have hxa : x ≠ a := fun h => has (h ▸ hxs)
          simp only [hxa, ↓reduceIte]
          exact hC1eq x hxs y (Finset.filter_subset _ _ hy)
    · refine ⟨CF, fun x => if x = a then false else b1 x,
        Finset.Subset.trans (Finset.filter_subset _ _) hC1sub, ?_, ?_⟩
      · have h2 : C1.card ≤ 2 * CF.card := by omega
        calc C.card ≤ 2 ^ s.card * C1.card := hC1card
          _ ≤ 2 ^ s.card * (2 * CF.card) := Nat.mul_le_mul_left _ h2
          _ = 2 ^ s.card * 2 * CF.card := by ring
      · intro x hx y hy
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hxs
        · simp only [↓reduceIte]
          exact (Finset.mem_filter.mp hy).2
        · have hxa : x ≠ a := fun h => has (h ▸ hxs)
          simp only [hxa, ↓reduceIte]
          exact hC1eq x hxs y (Finset.filter_subset _ _ hy)

lemma exists_mono_rect {n m : ℕ} (G : Fin n → Fin n → Bool)
    (R C : Finset (Fin n)) (hR : 2 * m ≤ R.card) (hC : m * 4 ^ m ≤ C.card) :
    ∃ (R0 C0 : Finset (Fin n)) (val : Bool),
      R0 ⊆ R ∧ C0 ⊆ C ∧ R0.card = m ∧ C0.card = m ∧
      ∀ x ∈ R0, ∀ y ∈ C0, G x y = val := by
  classical
  obtain ⟨R1, hR1sub, hR1card⟩ := Finset.exists_subset_card_eq hR
  obtain ⟨C', b, hC'sub, hC'card, hC'eq⟩ := majority_halve G R1 C
  have hpow : 2 ^ R1.card = 4 ^ m := by
    rw [hR1card, pow_mul]
    norm_num
  rw [hpow] at hC'card
  have hC'ge : m ≤ C'.card := by
    have h4 : 0 < 4 ^ m := by positivity
    have hmul : 4 ^ m * m ≤ 4 ^ m * C'.card := by
      calc 4 ^ m * m = m * 4 ^ m := mul_comm _ _
        _ ≤ C.card := hC
        _ ≤ 4 ^ m * C'.card := hC'card
    exact Nat.le_of_mul_le_mul_left hmul h4
  obtain ⟨C0, hC0sub, hC0card⟩ := Finset.exists_subset_card_eq hC'ge
  let RT := R1.filter (fun x => b x = true)
  let RF := R1.filter (fun x => b x = false)
  have hsplit : RT.card + RF.card = 2 * m := by
    rw [← hR1card, ← Finset.card_union_of_disjoint]
    · have hun : RT ∪ RF = R1 := by
        ext x
        simp only [RT, RF, Finset.mem_union, Finset.mem_filter]
        cases b x <;> simp
      rw [hun]
    · rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [RT, RF, Finset.mem_filter] at h1 h2
      rw [h1.2] at h2
      exact Bool.noConfusion h2.2
  by_cases hle : RF.card ≤ RT.card
  · have hmT : m ≤ RT.card := by omega
    obtain ⟨R0, hR0sub, hR0card⟩ := Finset.exists_subset_card_eq hmT
    refine ⟨R0, C0, true,
      Finset.Subset.trans hR0sub (Finset.Subset.trans (Finset.filter_subset _ _) hR1sub),
      Finset.Subset.trans hC0sub hC'sub, hR0card, hC0card, ?_⟩
    intro x hx y hy
    have hxT := Finset.mem_filter.mp (hR0sub hx)
    rw [hC'eq x hxT.1 y (hC0sub hy), hxT.2]
  · have hmF : m ≤ RF.card := by omega
    obtain ⟨R0, hR0sub, hR0card⟩ := Finset.exists_subset_card_eq hmF
    refine ⟨R0, C0, false,
      Finset.Subset.trans hR0sub (Finset.Subset.trans (Finset.filter_subset _ _) hR1sub),
      Finset.Subset.trans hC0sub hC'sub, hR0card, hC0card, ?_⟩
    intro x hx y hy
    have hxF := Finset.mem_filter.mp (hR0sub hx)
    rw [hC'eq x hxF.1 y (hC0sub hy), hxF.2]

lemma decomp_direct {n m : ℕ} (hm : 0 < m) (G : Fin n → Fin n → Bool) :
    ∀ (k : ℕ) (R C : Finset (Fin n)), R.card = k → C.card = k →
      ∃ (L : ℕ) (f : Fin n → Fin n) (grp : Fin n → ℕ),
        L ≤ k / m + m * 4 ^ m ∧
        (∀ x ∈ R, f x ∈ C) ∧
        (∀ x ∈ R, ∀ y ∈ R, f x = f y → x = y) ∧
        (∀ x ∈ R, grp x < L) ∧
        (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, ∀ w ∈ R,
          grp x = grp y → grp x = grp z → grp x = grp w → G x (f y) = G z (f w)) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro R C hR hC
    by_cases hlt : k < m * 4 ^ m
    · have hcardEq : Fintype.card { x : Fin n // x ∈ R } = Fintype.card { y : Fin n // y ∈ C } := by
        simp [hR, hC]
      let eRC : { x : Fin n // x ∈ R } ≃ { y : Fin n // y ∈ C } := Fintype.equivOfCardEq hcardEq
      have hcardFin : Fintype.card { x : Fin n // x ∈ R } = Fintype.card (Fin k) := by
        simp [hR]
      let eFin : { x : Fin n // x ∈ R } ≃ Fin k := Fintype.equivOfCardEq hcardFin
      let f : Fin n → Fin n := fun x => if hx : x ∈ R then (eRC ⟨x, hx⟩).1 else x
      let grp : Fin n → ℕ := fun x => if hx : x ∈ R then (eFin ⟨x, hx⟩).val else 0
      refine ⟨k, f, grp, le_trans (le_of_lt hlt) (Nat.le_add_left _ _), ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [f, hx, ↓reduceDIte]
        exact (eRC ⟨x, hx⟩).2
      · intro x hx y hy hxy
        simp only [f, hx, hy, ↓reduceDIte] at hxy
        have hsub : eRC ⟨x, hx⟩ = eRC ⟨y, hy⟩ := Subtype.ext hxy
        exact congrArg Subtype.val (eRC.injective hsub)
      · intro x hx
        simp only [grp, hx, ↓reduceDIte]
        exact (eFin ⟨x, hx⟩).isLt
      · intro x hx y hy z hz w hw hxy hxz hxw
        have hinj_g : ∀ u ∈ R, ∀ v ∈ R, grp u = grp v → u = v := by
          intro u hu v hv huv
          simp only [grp, hu, hv, ↓reduceDIte] at huv
          exact congrArg Subtype.val (eFin.injective (Fin.ext huv))
        have ey := hinj_g x hx y hy hxy
        have ez := hinj_g x hx z hz hxz
        have ew := hinj_g x hx w hw hxw
        subst ey; subst ez; subst ew
        rfl
    · have hge : m * 4 ^ m ≤ k := by omega
      have h4m : 2 ≤ 4 ^ m := by
        have h1 : 4 ^ 1 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        omega
      have h2m : 2 * m ≤ k := by nlinarith
      obtain ⟨R0, C0, val, hR0sub, hC0sub, hR0card, hC0card, hmono⟩ :=
        exists_mono_rect (m := m) G R C (by omega) (by omega)
      let R' := R \ R0
      let C' := C \ C0
      have hR'card : R'.card = k - m := by
        rw [Finset.card_sdiff_of_subset hR0sub, hR, hR0card]
      have hC'card : C'.card = k - m := by
        rw [Finset.card_sdiff_of_subset hC0sub, hC, hC0card]
      have hkm_lt : k - m < k := by omega
      obtain ⟨L', f', grp', hL'le, hf'mem, hf'inj, hgrp'lt, hgrp'mono⟩ :=
        ih (k - m) hkm_lt R' C' hR'card hC'card
      have hcard0 : Fintype.card { x : Fin n // x ∈ R0 } = Fintype.card { y : Fin n // y ∈ C0 } := by
        simp [hR0card, hC0card]
      let e0 : { x : Fin n // x ∈ R0 } ≃ { y : Fin n // y ∈ C0 } := Fintype.equivOfCardEq hcard0
      let f : Fin n → Fin n := fun x => if hx : x ∈ R0 then (e0 ⟨x, hx⟩).1 else f' x
      let grp : Fin n → ℕ := fun x => if x ∈ R0 then L' else grp' x
      have hdiv_step : (k - m) / m + 1 = k / m := by
        have hadd : k - m + m = k := by omega
        conv_rhs => rw [← hadd]
        exact (Nat.add_div_right (k - m) hm).symm
      refine ⟨L' + 1, f, grp, by omega, ?_, ?_, ?_, ?_⟩
      · intro x hx
        by_cases hx0 : x ∈ R0
        · simp only [f, hx0, ↓reduceDIte]
          exact hC0sub (e0 ⟨x, hx0⟩).2
        · simp only [f, hx0, ↓reduceDIte]
          have hx' : x ∈ R' := Finset.mem_sdiff.mpr ⟨hx, hx0⟩
          exact Finset.sdiff_subset (hf'mem x hx')
      · intro x hx y hy hxy
        by_cases hx0 : x ∈ R0 <;> by_cases hy0 : y ∈ R0
        · simp only [f, hx0, hy0, ↓reduceDIte] at hxy
          exact congrArg Subtype.val (e0.injective (Subtype.ext hxy))
        · simp only [f, hx0, hy0, ↓reduceDIte] at hxy
          have h1 : (e0 ⟨x, hx0⟩).1 ∈ C0 := (e0 ⟨x, hx0⟩).2
          have hy' : y ∈ R' := Finset.mem_sdiff.mpr ⟨hy, hy0⟩
          have h2 : f' y ∈ C' := hf'mem y hy'
          rw [← hxy] at h2
          exact absurd h1 (Finset.mem_sdiff.mp h2).2
        · simp only [f, hx0, hy0, ↓reduceDIte] at hxy
          have h1 : (e0 ⟨y, hy0⟩).1 ∈ C0 := (e0 ⟨y, hy0⟩).2
          have hx' : x ∈ R' := Finset.mem_sdiff.mpr ⟨hx, hx0⟩
          have h2 : f' x ∈ C' := hf'mem x hx'
          rw [hxy] at h2
          exact absurd h1 (Finset.mem_sdiff.mp h2).2
        · simp only [f, hx0, hy0, ↓reduceDIte] at hxy
          exact hf'inj x (Finset.mem_sdiff.mpr ⟨hx, hx0⟩) y (Finset.mem_sdiff.mpr ⟨hy, hy0⟩) hxy
      · intro x hx
        by_cases hx0 : x ∈ R0
        · simp only [grp, hx0, ↓reduceIte]
          omega
        · simp only [grp, hx0, ↓reduceIte]
          have := hgrp'lt x (Finset.mem_sdiff.mpr ⟨hx, hx0⟩)
          omega
      · intro x hx y hy z hz w hw hxy hxz hxw
        by_cases hx0 : x ∈ R0
        · have hgx : grp x = L' := by simp only [grp, hx0, ↓reduceIte]
          have hmem0 : ∀ u ∈ R, grp u = L' → u ∈ R0 := by
            intro u hu hgu
            by_contra hu0
            simp only [grp, hu0, ↓reduceIte] at hgu
            have := hgrp'lt u (Finset.mem_sdiff.mpr ⟨hu, hu0⟩)
            omega
          have hy0 : y ∈ R0 := hmem0 y hy (hxy.symm.trans hgx)
          have hz0 : z ∈ R0 := hmem0 z hz (hxz.symm.trans hgx)
          have hw0 : w ∈ R0 := hmem0 w hw (hxw.symm.trans hgx)
          simp only [f, hy0, hw0, ↓reduceDIte]
          rw [hmono x hx0 _ (e0 ⟨y, hy0⟩).2, hmono z hz0 _ (e0 ⟨w, hw0⟩).2]
        · have hx' : x ∈ R' := Finset.mem_sdiff.mpr ⟨hx, hx0⟩
          have hgx : grp x = grp' x := by simp only [grp, hx0, ↓reduceIte]
          have hgx_lt : grp x < L' := by rw [hgx]; exact hgrp'lt x hx'
          have hnot0 : ∀ u ∈ R, grp x = grp u → u ∉ R0 := by
            intro u _ hgu hu0
            simp only [grp, hx0, hu0, ↓reduceIte] at hgu
            have := hgrp'lt x hx'
            omega
          have hy0 : y ∉ R0 := hnot0 y hy hxy
          have hz0 : z ∉ R0 := hnot0 z hz hxz
          have hw0 : w ∉ R0 := hnot0 w hw hxw
          have hy' : y ∈ R' := Finset.mem_sdiff.mpr ⟨hy, hy0⟩
          have hz' : z ∈ R' := Finset.mem_sdiff.mpr ⟨hz, hz0⟩
          have hw' : w ∈ R' := Finset.mem_sdiff.mpr ⟨hw, hw0⟩
          simp only [grp, hx0, hy0, hz0, hw0, ↓reduceIte] at hxy hxz hxw
          simp only [f, hy0, hw0, ↓reduceDIte]
          exact hgrp'mono x hx' y hy' z hz' w hw' hxy hxz hxw

end PEqualNP.Outside.L_lib_620_aux

theorem PEqualNP.Outside.L_lib_620 : (∀ (n m : ℕ), 0 < m → m^2*4^m ≤ n →
  ∀ G : Fin n → Fin n → Bool,
    ∃ (π : Equiv.Perm (Fin n)) (group : Fin n → Fin (2*(n/m))),
      ∀ (x y z w : Fin n), group x = group y → group x = group z → group x = group w →
        G x (π y) = G z (π w)) := by
  intro n m hm hn G
  obtain ⟨L, f, grp, hLle, _, hfinj, hgrplt, hmono⟩ :=
    PEqualNP.Outside.L_lib_620_aux.decomp_direct hm G n Finset.univ Finset.univ
      (by simp) (by simp)
  have hfinj' : Function.Injective f := fun x y hxy =>
    hfinj x (Finset.mem_univ x) y (Finset.mem_univ y) hxy
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj')
  have hm4m_le : m * 4 ^ m ≤ n / m := by
    rw [Nat.le_div_iff_mul_le hm]
    calc m * 4 ^ m * m = m ^ 2 * 4 ^ m := by ring
      _ ≤ n := hn
  have hL_bound : L ≤ 2 * (n / m) := by omega
  let group : Fin n → Fin (2 * (n / m)) := fun x =>
    ⟨grp x, lt_of_lt_of_le (hgrplt x (Finset.mem_univ x)) hL_bound⟩
  refine ⟨π, group, fun x y z w hxy hxz hxw => ?_⟩
  exact hmono x (Finset.mem_univ x) y (Finset.mem_univ y) z (Finset.mem_univ z)
    w (Finset.mem_univ w) (congrArg Fin.val hxy) (congrArg Fin.val hxz) (congrArg Fin.val hxw)
