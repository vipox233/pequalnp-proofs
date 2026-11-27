import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18802_3
    (hNoDirtyOr :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle x2 →
        x2.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO x2 x4 →
        PEqualNP.TopForm.TopForm x2 x4 →
        (PEqualNP.TopForm.Ustar x2 x4).Nonempty →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card →
        PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4 = ∅ →
        ∃ (x11 : Finset (Fin x1)),
          (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → s(x12, x13) ∈ PEqualNP.TopForm.Ustar x2 x4 → x12 ∈ x11 ∨ x13 ∈ x11) ∧
          x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤
            (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card)
    (hHasDirtyOr :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle x2 →
        x2.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO x2 x4 →
        PEqualNP.TopForm.TopForm x2 x4 →
        (PEqualNP.TopForm.Ustar x2 x4).Nonempty →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card →
        (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).Nonempty →
        ∃ (x11 : Finset (Fin x1)),
          (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → s(x12, x13) ∈ PEqualNP.TopForm.Ustar x2 x4 → x12 ∈ x11 ∨ x13 ∈ x11) ∧
          x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤
            (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card +
            (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.Ustar x2 x4).Nonempty → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ∃ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → s(x12, x13) ∈ PEqualNP.TopForm.Ustar x2 x4 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  intro x1 x2 x3 x4 hC4 hNE hLeast hTF hU hJ
  by_cases hO : PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4 = ∅
  · obtain ⟨S, hCov, hBnd⟩ := @hNoDirtyOr x1 x2 x3 x4 hC4 hNE hLeast hTF hU hJ hO
    refine ⟨S, hCov, ?_⟩
    rw [hO, Finset.card_empty]
    omega
  · exact @hHasDirtyOr x1 x2 x3 x4 hC4 hNE hLeast hTF hU hJ (Finset.nonempty_iff_ne_empty.mpr hO)
