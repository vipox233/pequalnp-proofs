import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8307_4
    (hNormalizeTop :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        (2 : ℕ) ≤ G.edgeFinset.card →
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧
          PEqualNP.TopForm.TopForm G D ∧
          D.size ≤ C.size ∧
          (PEqualNP.TopForm.junk G D).card ≤ (PEqualNP.TopForm.junk G C).card)
    (hReduceTop :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        (2 : ℕ) ≤ G.edgeFinset.card →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        (PEqualNP.TopForm.junk G D).Nonempty →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C' ∧
          PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
          C'.size ≤ D.size ∧
          (PEqualNP.TopForm.junk G C').card < (PEqualNP.TopForm.junk G D).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (PEqualNP.TopForm.junk x2 x4).Nonempty → (∀ x9 ∈ PEqualNP.TopForm.junk x2 x4, ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ PEqualNP.EdgeOwnership.pairInput x11 x12 ≠ PEqualNP.EdgeOwnership.pairInput x13 x14 ∧ PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x4.gates x9 Bool.false, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit } (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.false ∧ PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x4.gates x9 Bool.false, output := x4.output : PEqualNP.CircuitLowerBounds.Circuit } (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.false) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x4.size ∧ (PEqualNP.TopForm.junk x2 x10).card < (PEqualNP.TopForm.junk x2 x4).card := by
  classical
  intro n G _ C hC4 hM hFun hNE hTwo
  obtain ⟨j0, hj0⟩ := hNE
  obtain ⟨u, v, w, z, huv, hwz, hnePair, _, _⟩ := hTwo j0 hj0
  have hneEdge : s(u, v) ≠ s(w, z) := by
    intro hsym
    apply hnePair
    funext i
    change decide (i = u ∨ i = v) = decide (i = w ∨ i = z)
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Iff.rfl
    · exact or_comm
  have h2edges : 2 ≤ G.edgeFinset.card := by
    have hsub : ({s(u, v), s(w, z)} : Finset (Sym2 (Fin n))) ⊆ G.edgeFinset := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact SimpleGraph.mem_edgeFinset.mpr huv
      · exact SimpleGraph.mem_edgeFinset.mpr hwz
    have hpairCard : ({s(u, v), s(w, z)} : Finset (Sym2 (Fin n))).card = 2 :=
      Finset.card_pair hneEdge
    rw [← hpairCard]
    exact Finset.card_le_card hsub
  obtain ⟨D, hLeast, hTF, hDle, hDjunk⟩ := hNormalizeTop n G C hC4 h2edges hM hFun
  rcases Nat.lt_or_ge (PEqualNP.TopForm.junk G D).card (PEqualNP.TopForm.junk G C).card with hlt | hge
  · have hDM : PEqualNP.MetaComplexity.Monotone2 D :=
      fun g hg => ⟨hLeast.1.1 g hg, Nat.le_of_eq (hLeast.1.2.2 g hg)⟩
    exact ⟨D, hDM, hLeast.2.1, hDle, hlt⟩
  · have hDne : (PEqualNP.TopForm.junk G D).Nonempty :=
      Finset.card_pos.mp (Nat.lt_of_lt_of_le (Finset.card_pos.mpr ⟨j0, hj0⟩) hge)
    obtain ⟨C', hC'M, hC'f, hC'sz, hC'j⟩ := hReduceTop n G D hC4 h2edges hLeast hTF hDne
    exact ⟨C', hC'M, hC'f, Nat.le_trans hC'sz hDle, Nat.lt_of_lt_of_le hC'j hDjunk⟩
