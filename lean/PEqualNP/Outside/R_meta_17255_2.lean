import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17255_2
    (hNoCentreless :
      ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        PEqualNP.TopForm.TopForm x1 x3 →
        x3.size < (22 : ℕ) →
        ∀ (j1 j2 : ℕ),
          PEqualNP.TopForm.junk x1 x3 = {j1, j2} →
          PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 j1 j2 →
          PEqualNP.TopForm.centreless x1 x3 = ∅ →
          have u : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3
          (4 : ℕ) ≤ u.card →
          ∀ (x11 : Finset (Fin (11 : ℕ))),
            (∀ (x12 x13 : Fin (11 : ℕ)), (x1.deleteEdges ↑u).Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) →
            x11.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card < (5 : ℕ) + u.card →
            ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit),
              PEqualNP.TopForm.IsAO2 (11 : ℕ) x14 ∧
              PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x14 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ ∧
              x14.size < x3.size)
    (hHasCentreless :
      ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        PEqualNP.TopForm.TopForm x1 x3 →
        x3.size < (22 : ℕ) →
        ∀ (j1 j2 : ℕ),
          PEqualNP.TopForm.junk x1 x3 = {j1, j2} →
          PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 j1 j2 →
          (0 : ℕ) < (PEqualNP.TopForm.centreless x1 x3).card →
          have u : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3
          (4 : ℕ) ≤ u.card →
          ∀ (x11 : Finset (Fin (11 : ℕ))),
            (∀ (x12 x13 : Fin (11 : ℕ)), (x1.deleteEdges ↑u).Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) →
            x11.card + ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) < (5 : ℕ) + u.card →
            ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit),
              PEqualNP.TopForm.IsAO2 (11 : ℕ) x14 ∧
              PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x14 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ ∧
              x14.size < x3.size) :
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             (4 : ℕ) ≤ x9.card → ∀ (x11 : Finset (Fin (11 : ℕ))), (∀ (x12 x13 : Fin (11 : ℕ)), (x1.deleteEdges ↑x9).Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x11.card + ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) < (5 : ℕ) + x9.card → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (11 : ℕ) x14 ∧ PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x14 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ ∧ x14.size < x3.size) := by
  intro x1 _ x3 hEq hLeast hTop hSize hJunk _ hU x11 hCov hCard
  exact Exists.elim hJunk fun j1 hJ1 =>
    Exists.elim hJ1 fun j2 hJ =>
      Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless x1 x3).card)
        (fun hC0 =>
          hNoCentreless x1 x3 hEq hLeast hTop hSize j1 j2 hJ.1 hJ.2
            (Finset.card_eq_zero.mp hC0) hU x11 hCov
            (Eq.mp
              (congrArg
                (fun k => x11.card + k < (5 : ℕ) + (PEqualNP.TopForm.Ustar x1 x3).card)
                (Eq.trans
                  (congrArg (fun k => k + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card)
                    (Eq.trans (congrArg (fun k => (2 : ℕ) * k) hC0) (Nat.mul_zero (2 : ℕ))))
                  (Nat.zero_add (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card)))
              hCard))
        (fun hCPos =>
          hHasCentreless x1 x3 hEq hLeast hTop hSize j1 j2 hJ.1 hJ.2 hCPos hU x11 hCov hCard)
