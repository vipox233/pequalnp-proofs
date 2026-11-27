import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8307_3
    (hToTopForm :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle x2 →
        PEqualNP.MetaComplexity.Monotone2 x4 →
        PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        (PEqualNP.TopForm.junk x2 x4).Nonempty →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 x1 D ∧
          PEqualNP.TopForm.TopForm x2 D ∧
          PEqualNP.MetaComplexity.circuitFun x1 D = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
          D.size ≤ x4.size ∧
          (PEqualNP.TopForm.junk x2 D).card ≤ (PEqualNP.TopForm.junk x2 x4).card)
    (hElimDirtyTopForm :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle x2 →
        PEqualNP.TopForm.IsAO2 x1 D →
        PEqualNP.TopForm.TopForm x2 D →
        PEqualNP.MetaComplexity.circuitFun x1 D = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        (PEqualNP.TopForm.junk x2 D).Nonempty →
        ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 E ∧
          PEqualNP.MetaComplexity.circuitFun x1 E = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
          E.size ≤ D.size ∧
          (PEqualNP.TopForm.junk x2 E).card < (PEqualNP.TopForm.junk x2 D).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (PEqualNP.TopForm.junk x2 x4).Nonempty → (∀ x9 ∈ PEqualNP.TopForm.junk x2 x4, ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ PEqualNP.EdgeOwnership.pairInput x11 x12 ≠ PEqualNP.EdgeOwnership.pairInput x13 x14 ∧ PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x4.gates x9 Bool.false, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit } (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.false ∧ PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x4.gates x9 Bool.false, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit } (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.false) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x4.size ∧ (PEqualNP.TopForm.junk x2 x10).card < (PEqualNP.TopForm.junk x2 x4).card := by
  intro x1 x2 x3 x4 hC4 hM hFun hJNE _hTwoEdge
  obtain ⟨D, hDAO, hDTF, hDFun, hDle, hDjle⟩ := @hToTopForm x1 x2 x3 x4 hC4 hM hFun hJNE
  by_cases hlt : (PEqualNP.TopForm.junk x2 D).card < (PEqualNP.TopForm.junk x2 x4).card
  · have hDM : PEqualNP.MetaComplexity.Monotone2 D := by
      intro g hg
      refine ⟨?_, ?_⟩
      · exact hDAO.1 g hg
      · rw [hDAO.2.2 g hg]
    exact ⟨D, hDM, hDFun, hDle, hlt⟩
  · have hDNE : (PEqualNP.TopForm.junk x2 D).Nonempty := by
      have hpos : 0 < (PEqualNP.TopForm.junk x2 x4).card := Finset.card_pos.mpr hJNE
      exact Finset.card_pos.mp (by omega)
    obtain ⟨E, hEM, hEFun, hEle, hEjlt⟩ := @hElimDirtyTopForm x1 x2 x3 D hC4 hDAO hDTF hDFun hDNE
    exact ⟨E, hEM, hEFun, Nat.le_trans hEle hDle, Nat.lt_of_lt_of_le hEjlt hDjle⟩
