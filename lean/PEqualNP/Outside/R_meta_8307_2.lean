import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8307_2
    (hNormalize :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle x2 →
        x2.edgeFinset.Nonempty →
        PEqualNP.MetaComplexity.Monotone2 x4 →
        PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsAO2 x1 D ∧
          PEqualNP.MetaComplexity.circuitFun x1 D = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
          D.size ≤ x4.size ∧
          (PEqualNP.TopForm.junk x2 D).card ≤ (PEqualNP.TopForm.junk x2 x4).card)
    (hReduceAO2 :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle x2 →
        x2.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 x1 D →
        PEqualNP.MetaComplexity.circuitFun x1 D = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        (PEqualNP.TopForm.junk x2 D).Nonempty →
        ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 x10 ∧
          PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
          x10.size ≤ D.size ∧
          (PEqualNP.TopForm.junk x2 x10).card < (PEqualNP.TopForm.junk x2 D).card) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (PEqualNP.TopForm.junk x2 x4).Nonempty → (∀ x9 ∈ PEqualNP.TopForm.junk x2 x4, ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ PEqualNP.EdgeOwnership.pairInput x11 x12 ≠ PEqualNP.EdgeOwnership.pairInput x13 x14 ∧ PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x4.gates x9 Bool.false, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit } (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.false ∧ PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x4.gates x9 Bool.false, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit } (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.false) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x4.size ∧ (PEqualNP.TopForm.junk x2 x10).card < (PEqualNP.TopForm.junk x2 x4).card) := by
  intro x1 x2 _ x4 hC4 hM hFun hNE hTwo
  have hEdgeNE : x2.edgeFinset.Nonempty :=
    Exists.elim hNE fun j hj =>
      Exists.elim (hTwo j hj) fun u hu =>
        Exists.elim hu fun v hv =>
          Exists.elim hv fun _ hw =>
            Exists.elim hw fun _ hz =>
              ⟨s(u, v), x2.mem_edgeFinset.mpr hz.1⟩
  exact Exists.elim (hNormalize x1 x2 x4 hC4 hEdgeNE hM hFun) fun D hD =>
    Or.elim (Nat.lt_or_ge (PEqualNP.TopForm.junk x2 D).card (PEqualNP.TopForm.junk x2 x4).card)
      (fun hlt =>
        ⟨D,
          fun g hg => ⟨hD.1.1 g hg, Nat.le_of_eq (hD.1.2.2 g hg)⟩,
          hD.2.1, hD.2.2.1, hlt⟩)
      (fun hge =>
        have hDne : (PEqualNP.TopForm.junk x2 D).Nonempty :=
          Finset.card_pos.mp (Nat.lt_of_lt_of_le (Finset.card_pos.mpr hNE) hge)
        Exists.elim (hReduceAO2 x1 x2 D hC4 hEdgeNE hD.1 hD.2.1 hDne) fun x10 hx10 =>
          ⟨x10, hx10.1, hx10.2.1, le_trans hx10.2.2.1 hD.2.2.1,
            lt_of_lt_of_le hx10.2.2.2 hD.2.2.2⟩)
