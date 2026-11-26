import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18886_1
    (hNoCentreless : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → PEqualNP.TopForm.centreless x2 x4 = ∅ → ∃ (x10 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x10 ∧ x10.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card)
    (hHasCentreless : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (PEqualNP.TopForm.centreless x2 x4).Nonempty → ∃ (x10 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x10 ∧ x10.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ∃ (x10 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x10 ∧ x10.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card) := by
  intro x1 x2 x3 x4 h4 hne hLeast hTF hJunk
  by_cases hc : PEqualNP.TopForm.centreless x2 x4 = ∅
  · rcases @hNoCentreless x1 x2 x3 x4 h4 hne hLeast hTF hJunk hc with ⟨x10, hcov, hcard⟩
    refine ⟨x10, hcov, ?_⟩
    have hZero : (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card = (PEqualNP.TopForm.tops x2 x4).card := by
      rw [hc, Finset.sdiff_empty, Finset.card_empty]
      omega
    rw [hZero]
    exact hcard
  · exact @hHasCentreless x1 x2 x3 x4 h4 hne hLeast hTF hJunk (Finset.nonempty_iff_ne_empty.mpr hc)
