import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18605_2
    (hExistsMinCover :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))),
        ∃ (x2 : Finset (Fin (26 : ℕ))),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover x1 x2)
    (hWithMinCover :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        PEqualNP.TopForm.TopForm x1 x3 →
        x3.size ≤ (64 : ℕ) →
        have x8 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;
        have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;
        have x10 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
        have x11 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;
        x10.card ≤ (12 : ℕ) → PEqualNP.TopForm.centreless x1 x3 = ∅ → (2 : ℕ) ≤ x9.card → (1 : ℕ) ≤ (PEqualNP.TopForm.mixing x1 x3).card → (3 : ℕ) ≤ x10.card → x8.card + x9.card + x11.card ≤ (13 : ℕ) + x10.card → (52 : ℕ) ≤ (4 : ℕ) * x8.card + x10.card →
        ∀ (x19 : Finset (Fin (26 : ℕ))),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x19 →
          x19.card ≤ x8.card →
          False) :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size ≤ (64 : ℕ) →           have x8 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;           have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;           have x10 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x11 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;           x10.card ≤ (12 : ℕ) → PEqualNP.TopForm.centreless x1 x3 = ∅ → (2 : ℕ) ≤ x9.card → (1 : ℕ) ≤ (PEqualNP.TopForm.mixing x1 x3).card → (3 : ℕ) ≤ x10.card → x8.card + x9.card + x11.card ≤ (13 : ℕ) + x10.card → (52 : ℕ) ≤ (4 : ℕ) * x8.card + x10.card → (∀ (x19 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x19 → x19.card ≤ x8.card) → False) := by
  intro x1 x2 x3 hEqG hL hTF hSz x8 x9 x10 x11 hULe hC hJ hM hUGe hSum hDeg hAll
  exact (hExistsMinCover (x1.deleteEdges ↑x10)).elim fun x19 hMin =>
    @hWithMinCover x1 x2 x3 hEqG hL hTF hSz hULe hC hJ hM hUGe hSum hDeg x19 hMin (hAll x19 hMin)
