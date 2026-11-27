import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_478 : (∀ (n : ℕ) (R : Set (Fin n → Bool)), 0 < n →
  (∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R,
    (fun i => (a i && b i) || (b i && c i) || (c i && a i)) ∈ R) →
  ∀ x : Fin n → Bool, x ∈ R ↔
    ∀ i j : Fin n, ∃ y ∈ R, y i = x i ∧ y j = x j) := by
  intro n R hn hmaj x
  constructor
  · intro hx i j
    exact ⟨x, hx, rfl, rfl⟩
  · intro hpair
    have hind : ∀ m : ℕ, ∀ S : Finset (Fin n), S.card = m → ∃ y ∈ R, ∀ i ∈ S, y i = x i := by
      intro m
      induction m with
      | zero =>
        intro S hs
        obtain ⟨y, hyR, _, _⟩ := hpair ⟨0, hn⟩ ⟨0, hn⟩
        refine ⟨y, hyR, fun i hi => ?_⟩
        rw [Finset.card_eq_zero.mp hs] at hi
        simp at hi
      | succ m ih =>
        cases m with
        | zero =>
          intro S hs
          obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
          obtain ⟨y, hyR, hya, _⟩ := hpair a a
          refine ⟨y, hyR, fun i hi => ?_⟩
          rw [Finset.mem_singleton.mp hi]
          exact hya
        | succ m =>
          cases m with
          | zero =>
            intro S hs
            obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hs
            obtain ⟨y, hyR, hya, hyb⟩ := hpair a b
            refine ⟨y, hyR, fun i hi => ?_⟩
            rcases Finset.mem_insert.mp hi with rfl | hib
            · exact hya
            · rw [Finset.mem_singleton.mp hib]
              exact hyb
          | succ k =>
            intro S hs
            have hpos0 : 0 < S.card := by omega
            obtain ⟨i1, hi1⟩ := Finset.card_pos.mp hpos0
            have hc1 : (S.erase i1).card = k + 2 := by
              rw [Finset.card_erase_of_mem hi1]
              omega
            have hpos1 : 0 < (S.erase i1).card := by omega
            obtain ⟨i2, hi2_e1⟩ := Finset.card_pos.mp hpos1
            obtain ⟨hi2_ne1, hi2⟩ := Finset.mem_erase.mp hi2_e1
            have hc2_sub : ((S.erase i1).erase i2).card = k + 1 := by
              rw [Finset.card_erase_of_mem hi2_e1]
              omega
            have hpos2 : 0 < ((S.erase i1).erase i2).card := by omega
            obtain ⟨i3, hi3_e2⟩ := Finset.card_pos.mp hpos2
            obtain ⟨hi3_ne2, hi3_e1⟩ := Finset.mem_erase.mp hi3_e2
            obtain ⟨hi3_ne1, hi3⟩ := Finset.mem_erase.mp hi3_e1
            have hc2 : (S.erase i2).card = k + 2 := by
              rw [Finset.card_erase_of_mem hi2]
              omega
            have hc3 : (S.erase i3).card = k + 2 := by
              rw [Finset.card_erase_of_mem hi3]
              omega
            obtain ⟨y1, hy1R, hy1⟩ := ih (S.erase i1) hc1
            obtain ⟨y2, hy2R, hy2⟩ := ih (S.erase i2) hc2
            obtain ⟨y3, hy3R, hy3⟩ := ih (S.erase i3) hc3
            refine ⟨fun j => (y1 j && y2 j) || (y2 j && y3 j) || (y3 j && y1 j),
              hmaj y1 hy1R y2 hy2R y3 hy3R, fun j hj => ?_⟩
            dsimp only
            by_cases hj1 : j = i1
            · have hj_ne2 : j ≠ i2 := by
                rw [hj1]
                exact hi2_ne1.symm
              have hj_ne3 : j ≠ i3 := by
                rw [hj1]
                exact hi3_ne1.symm
              have heq2 : y2 j = x j := hy2 j (Finset.mem_erase.mpr ⟨hj_ne2, hj⟩)
              have heq3 : y3 j = x j := hy3 j (Finset.mem_erase.mpr ⟨hj_ne3, hj⟩)
              rw [heq2, heq3]
              cases y1 j <;> cases x j <;> rfl
            · by_cases hj2 : j = i2
              · have hj_ne3 : j ≠ i3 := by
                  rw [hj2]
                  exact hi3_ne2.symm
                have heq1 : y1 j = x j := hy1 j (Finset.mem_erase.mpr ⟨hj1, hj⟩)
                have heq3 : y3 j = x j := hy3 j (Finset.mem_erase.mpr ⟨hj_ne3, hj⟩)
                rw [heq1, heq3]
                cases y2 j <;> cases x j <;> rfl
              · have heq1 : y1 j = x j := hy1 j (Finset.mem_erase.mpr ⟨hj1, hj⟩)
                have heq2 : y2 j = x j := hy2 j (Finset.mem_erase.mpr ⟨hj2, hj⟩)
                rw [heq1, heq2]
                cases y3 j <;> cases x j <;> rfl
    obtain ⟨y, hyR, hy⟩ := hind (Finset.univ : Finset (Fin n)).card Finset.univ rfl
    have hyx : y = x := funext (fun i => hy i (Finset.mem_univ i))
    rwa [← hyx]
