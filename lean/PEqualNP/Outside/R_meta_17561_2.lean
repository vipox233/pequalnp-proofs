import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17561_2
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        ∀ (j1 j2 : ℕ),
          j1 ∈ PEqualNP.TopForm.junk x1 x2 →
          j2 ∈ PEqualNP.TopForm.junk x1 x2 →
          j1 ≠ j2 →
          PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 j1 j2 →
          (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) →
          (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card →
          (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
          PEqualNP.TopForm.centreless x1 x2 = ∅ →
          (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
          (PEqualNP.TopForm.Ustar x1 x2).card ≤ (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        ∀ (j1 j2 : ℕ),
          j1 ∈ PEqualNP.TopForm.junk x1 x2 →
          j2 ∈ PEqualNP.TopForm.junk x1 x2 →
          j1 ≠ j2 →
          PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 j1 j2 →
          (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) →
          (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card →
          (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
          (0 : ℕ) < (PEqualNP.TopForm.centreless x1 x2).card →
          (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
          (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ (PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∨ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7)) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) := by
  intro x1 x2 hSize hLeast hTop _ hPair hCov hU3 hLt hJ3
  exact Exists.elim hPair fun a hPa =>
    Exists.elim hPa fun b hP =>
      Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless x1 x2).card)
        (fun hC0 =>
          have hZ : (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card = (PEqualNP.TopForm.junk x1 x2).card :=
            Eq.trans
              (congrArg (fun k => k + (PEqualNP.TopForm.junk x1 x2).card)
                (Eq.trans (congrArg (fun k => (2 : ℕ) * k) hC0) (Nat.mul_zero (2 : ℕ))))
              (Nat.zero_add (PEqualNP.TopForm.junk x1 x2).card)
          have hLt0 : (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card :=
            Eq.mp
              (congrArg (fun k => k + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card) hZ)
              hLt
          Eq.mpr
            (congrArg (fun k => (PEqualNP.TopForm.Ustar x1 x2).card ≤ k + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) hZ)
            (Or.elim hP.2.2.2
              (fun hCone => hNoCentreless x2 hSize hLeast hTop a b hP.1 hP.2.1 hP.2.2.1 hCone hCov hU3 hJ3 (Finset.card_eq_zero.mp hC0) hLt0)
              (fun hCone => hNoCentreless x2 hSize hLeast hTop b a hP.2.1 hP.1 (Ne.symm hP.2.2.1) hCone hCov hU3 hJ3 (Finset.card_eq_zero.mp hC0) hLt0)))
        (fun hCPos =>
          Or.elim hP.2.2.2
            (fun hCone => hHasCentreless x2 hSize hLeast hTop a b hP.1 hP.2.1 hP.2.2.1 hCone hCov hU3 hJ3 hCPos hLt)
            (fun hCone => hHasCentreless x2 hSize hLeast hTop b a hP.2.1 hP.1 (Ne.symm hP.2.2.1) hCone hCov hU3 hJ3 hCPos hLt))
