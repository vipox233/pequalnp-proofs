import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8935_2
    (hStarCover :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        ∃ V : Finset (Fin n),
          (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ V, v ∈ e) ∧
          V.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (hUstarCoverBudget :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 →
        PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 →
        (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 x12 x13 x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ s(x11, x12) ≠ s(x13, x14) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x11, ↑x12] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13, ↑x14] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) →
        ∃ W : Finset (Fin x1),
          (∀ e ∈ PEqualNP.TopForm.Ustar x2 x4, ∃ v ∈ W, v ∈ e) ∧
          x2.edgeFinset.card + (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + W.card ≤ x4.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ s(x11, x12) ≠ s(x13, x14) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x11, ↑x12] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13, ↑x14] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → ∃ (x11 : Finset (Fin x1)), x2.IsVertexCover ↑x11 ∧ x2.edgeFinset.card + x11.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro x1 x2 x3 x4 hBip hNA hC4 hLeast hTF hDirty
  obtain ⟨V1, hV1cov, hV1card⟩ := @hStarCover x1 x2 x3 x4 hC4 hLeast hTF
  obtain ⟨V2, hV2cov, hV2card⟩ := @hUstarCoverBudget x1 x2 x3 x4 hBip hNA hC4 hLeast hTF hDirty
  have hCov : x2.IsVertexCover ↑(V1 ∪ V2) := by
    intro u v huv
    have he : s(u, v) ∈ x2.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    by_cases hs : s(u, v) ∈ PEqualNP.TopForm.starEdges x2 x4
    · obtain ⟨w, hwV, hwe⟩ := hV1cov s(u, v) hs
      rcases Sym2.mem_iff.mp hwe with rfl | rfl
      · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left V2 hwV))
      · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_union_left V2 hwV))
    · obtain ⟨w, hwW, hwe⟩ := hV2cov s(u, v) (Finset.mem_sdiff.mpr ⟨he, hs⟩)
      rcases Sym2.mem_iff.mp hwe with rfl | rfl
      · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right V1 hwW))
      · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_union_right V1 hwW))
  have hUni : (V1 ∪ V2).card ≤ V1.card + V2.card := Finset.card_union_le V1 V2
  exact ⟨V1 ∪ V2, hCov, by omega⟩
