import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17751_2
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x4 : ℕ := (PEqualNP.TopForm.Ustar x1 x2).card;
        have x5 : ℕ := (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        have x6 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card;
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (PEqualNP.TopForm.centreless x1 x2).card = (0 : ℕ) ∧
          (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) ∧
          x2.size ≤ (21 : ℕ) ∧
          (2 : ℕ) ≤ x5 ∧
          (2 : ℕ) + x5 < (2 : ℕ) * x4 ∧
          (3 : ℕ) ≤ x4 ∧
          (18 : ℕ) + x6 + x5 ≤ x2.size + x4 + (1 : ℕ) ∧
          (∀ (x11 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x2)) x11 → x11.card ≤ x6) ∧
          (∀ (x12 : Fin (11 : ℕ)), ↑x12 < (4 : ℕ) → (∀ x14 < x2.size, ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x14 x15 x16 : ℕ), x14 < x15 → x15 < x16 → x16 < x2.size → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs → ↑x12 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs)) →
        False)
    (hPosCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x3 : ℕ := (PEqualNP.TopForm.centreless x1 x2).card;
        have x4 : ℕ := (PEqualNP.TopForm.Ustar x1 x2).card;
        have x5 : ℕ := (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        have x6 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card;
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (1 : ℕ) ≤ x3 ∧
          (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) ∧
          x2.size ≤ (21 : ℕ) ∧
          (2 : ℕ) * x3 + (2 : ℕ) + x5 < (2 : ℕ) * x4 ∧
          (3 : ℕ) ≤ x4 ∧
          (18 : ℕ) + x6 + (2 : ℕ) * x3 + x5 ≤ x2.size + x4 + (1 : ℕ) ∧
          (∀ (x11 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x2)) x11 → x11.card ≤ x6) ∧
          (∀ (x12 : Fin (11 : ℕ)), ↑x12 < (4 : ℕ) → (∀ x14 < x2.size, ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x14 x15 x16 : ℕ), x14 < x15 → x15 < x16 → x16 < x2.size → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs → ↑x12 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs)) →
        False) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) → x2.size ≤ (21 : ℕ) → (2 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (16 : ℕ) + (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card ≤ x2.size + (PEqualNP.TopForm.Ustar x1 x2).card + (1 : ℕ) → (∀ (x11 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x2)) x11 → x11.card ≤ (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card) → (∀ (x12 : Fin (11 : ℕ)), ↑x12 < (4 : ℕ) → (∀ x14 < x2.size, ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x14 x15 x16 : ℕ), x14 < x15 → x15 < x16 → x16 < x2.size → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs → ↑x12 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs) → False) := by
  intro x1 x2 hL hTF hJ hSz hLB hLt hU3 hSum hMC hR2
  exact Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless x1 x2).card)
    (fun hC0 => hNoCentreless x2 ⟨hL, hTF, hC0, hJ, hSz,
      by dsimp only [x1] at hC0 hLB; omega,
      by dsimp only [x1] at hC0 hJ hLt; omega,
      hU3,
      by dsimp only [x1] at hC0 hJ hSum; omega,
      hMC, hR2⟩)
    (fun hCPos => hPosCentreless x2 ⟨hL, hTF, hCPos, hJ, hSz,
      by dsimp only [x1] at hJ hLt; omega,
      hU3,
      by dsimp only [x1] at hJ hSum; omega,
      hMC, hR2⟩)
