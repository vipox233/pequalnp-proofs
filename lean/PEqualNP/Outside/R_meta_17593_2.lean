import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17593_2
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (x2.size ≤ (21 : ℕ) ∧
          PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (PEqualNP.TopForm.centreless x1 x2).card = (0 : ℕ) ∧
          (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
          (4 : ℕ) ≤ x8 ∧ x7.card ≤ x8 ∧ x8 < (2 : ℕ) * x7.card ∧ x8 - x7.card ≤ (4 : ℕ)) →
        ∃ (x13 : Finset (Fin (11 : ℕ))) (x14 : Finset (Fin (11 : ℕ))),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x13 ∧
          x1.IsVertexCover ↑x14 ∧ (x14 \ x13).card ≤ x8 - x7.card)
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (x2.size ≤ (21 : ℕ) ∧
          PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (0 : ℕ) < (PEqualNP.TopForm.centreless x1 x2).card ∧
          (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
          (4 : ℕ) ≤ x8 ∧ x7.card ≤ x8 ∧ x8 < (2 : ℕ) * x7.card ∧ x8 - x7.card ≤ (4 : ℕ)) →
        ∃ (x13 : Finset (Fin (11 : ℕ))) (x14 : Finset (Fin (11 : ℕ))),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x13 ∧
          x1.IsVertexCover ↑x14 ∧ (x14 \ x13).card ≤ x8 - x7.card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (4 : ℕ) ≤ x8 → x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → x8 - x7.card ≤ (4 : ℕ) → ∃ (x13 : Finset (Fin (11 : ℕ))) (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x13 ∧ x1.IsVertexCover ↑x14 ∧ (x14 \ x13).card ≤ x8 - x7.card) :=
  fun x2 hSz hLeast hTF hJ2 h4 hLe hLt hDiff =>
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]
    Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless x1 x2).card)
      (fun hC0 =>
        let hEq : (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card =
            (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card :=
          Eq.trans (congrArg (fun k => (2 : ℕ) * k + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) hC0)
            (congrArg (fun k => k + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) (Nat.zero_add _))
        Eq.subst (motive := fun m => ∃ (x13 : Finset (Fin (11 : ℕ))) (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x2)) x13 ∧ x1.IsVertexCover ↑x14 ∧ (x14 \ x13).card ≤ m - (PEqualNP.TopForm.Ustar x1 x2).card) hEq.symm
          (hNoCentreless x2 ⟨hSz, hLeast, hTF, hC0, hJ2,
            Eq.subst (motive := fun m => (4 : ℕ) ≤ m) hEq h4,
            Eq.subst (motive := fun m => (PEqualNP.TopForm.Ustar x1 x2).card ≤ m) hEq hLe,
            Eq.subst (motive := fun m => m < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card) hEq hLt,
            Eq.subst (motive := fun m => m - (PEqualNP.TopForm.Ustar x1 x2).card ≤ (4 : ℕ)) hEq hDiff⟩))
      (fun hCPos =>
        hHasCentreless x2 ⟨hSz, hLeast, hTF, hCPos, hJ2, h4, hLe, hLt, hDiff⟩)
