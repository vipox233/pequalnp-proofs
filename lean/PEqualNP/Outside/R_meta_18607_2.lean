import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18607_2
    (hMinCoverAndCount :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) (u : Finset (Sym2 (Fin (26 : ℕ)))),
        (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) =>
          ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
        (13 : ℕ) ≤ u.card → u.card ≤ (52 : ℕ) →
        ∃ (c : Finset (Fin (26 : ℕ))),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑u) c ∧
          (52 : ℕ) ≤ (4 : ℕ) * c.card + u.card)
    (hRefuteWithCover :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [DecidableRel x1.Adj]
        (x3 : PEqualNP.CircuitLowerBounds.Circuit) (c : Finset (Fin (26 : ℕ))),
        have x8 : Finset ℕ := PEqualNP.TopForm.tops x1 x3
        have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3
        have x10 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3
        have x11 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3
        ((x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) =>
            ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ∧
          PEqualNP.TopForm.IsLeastAO x1 x3 ∧ PEqualNP.TopForm.TopForm x1 x3 ∧
          x3.size ≤ (64 : ℕ) ∧ (13 : ℕ) ≤ x10.card ∧ x10.card ≤ (52 : ℕ) ∧
          PEqualNP.TopForm.centreless x1 x3 = ∅ ∧ (2 : ℕ) ≤ x9.card ∧
          (1 : ℕ) ≤ (PEqualNP.TopForm.mixing x1 x3).card ∧
          x8.card + x9.card + x11.card ≤ (13 : ℕ) + x10.card ∧
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) c ∧
          c.card ≤ x8.card ∧ (52 : ℕ) ≤ (4 : ℕ) * c.card + x10.card) →
        False) :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size ≤ (64 : ℕ) →           have x8 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;           have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;           have x10 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x11 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;           (13 : ℕ) ≤ x10.card → x10.card ≤ (52 : ℕ) → PEqualNP.TopForm.centreless x1 x3 = ∅ → (2 : ℕ) ≤ x9.card → (1 : ℕ) ≤ (PEqualNP.TopForm.mixing x1 x3).card → (3 : ℕ) ≤ x10.card → x8.card + x9.card + x11.card ≤ (13 : ℕ) + x10.card → (52 : ℕ) ≤ (4 : ℕ) * x8.card + x10.card → (∀ (x20 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x20 → x20.card ≤ x8.card) → False) :=
  fun x1 _ x3 hEqG hL hTF hSz hGe13 hLe52 hCent hJ hMix _ hSum _ hMin =>
    (hMinCoverAndCount x1 (PEqualNP.TopForm.Ustar x1 x3) hEqG hGe13 hLe52).elim fun c hc =>
      hRefuteWithCover x1 x3 c ⟨hEqG, hL, hTF, hSz, hGe13, hLe52, hCent, hJ, hMix, hSum, hc.1, hMin c hc.1, hc.2⟩
