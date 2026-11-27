import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17559_2
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) →
        (PEqualNP.TopForm.centreless x1 x2).Nonempty →
        x7 ∈ PEqualNP.TopForm.junk x1 x2 →
        x8 ∈ PEqualNP.TopForm.junk x1 x2 →
        x7 ≠ x8 →
        PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 →
        (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) →
        (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) →
        PEqualNP.TopForm.centreless x1 x2 = ∅ →
        x7 ∈ PEqualNP.TopForm.junk x1 x2 →
        x8 ∈ PEqualNP.TopForm.junk x1 x2 →
        x7 ≠ x8 →
        PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 →
        (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) →
        (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card →
        (2 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (∃ (x7 : ℕ) (x8 : ℕ), x7 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x8 ∈ PEqualNP.TopForm.junk x1 x2 ∧ x7 ≠ x8 ∧ (PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x7 x8 ∨ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x8 x7)) → (∀ (x8 x9 : Fin (11 : ℕ)), s(x8, x9) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x11 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x11 (PEqualNP.EdgeOwnership.pairInput x8 x9) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) := by
  intro x1 x2 hSz hL hTF _ hEx hCov hU3 hIneq hJ2
  exact hEx.elim fun a ha =>
    ha.elim fun b hb =>
      (Classical.em (PEqualNP.TopForm.centreless x1 x2 = ∅)).elim
        (fun hEmpty =>
          have hEqSum :
              (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card +
                (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card =
              (2 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card :=
            congrArg (· + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
              (Eq.trans
                (congrArg (fun k => (2 : ℕ) * k + (PEqualNP.TopForm.junk x1 x2).card)
                  (Eq.trans (congrArg Finset.card hEmpty) Finset.card_empty))
                (Eq.trans (Nat.zero_add _) hJ2))
          Eq.mpr (congrArg ((PEqualNP.TopForm.Ustar x1 x2).card ≤ ·) hEqSum)
            (hb.2.2.2.elim
              (fun hAB => hNoCentreless x2 a b hSz hL hTF hJ2 hEmpty hb.1 hb.2.1 hb.2.2.1 hAB hCov hU3
                (Eq.mp (congrArg (· < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card) hEqSum) hIneq))
              (fun hBA => hNoCentreless x2 b a hSz hL hTF hJ2 hEmpty hb.2.1 hb.1 (Ne.symm hb.2.2.1) hBA hCov hU3
                (Eq.mp (congrArg (· < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card) hEqSum) hIneq))))
        (fun hNe =>
          have hEqJ :
              (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card +
                (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card =
              (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) +
                (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card :=
            congrArg (fun k => (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + k +
              (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) hJ2
          have hNeFin := Finset.nonempty_iff_ne_empty.mpr hNe
          Eq.mpr (congrArg ((PEqualNP.TopForm.Ustar x1 x2).card ≤ ·) hEqJ)
            (hb.2.2.2.elim
              (fun hAB => hHasCentreless x2 a b hSz hL hTF hJ2 hNeFin hb.1 hb.2.1 hb.2.2.1 hAB hCov hU3
                (Eq.mp (congrArg (· < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card) hEqJ) hIneq))
              (fun hBA => hHasCentreless x2 b a hSz hL hTF hJ2 hNeFin hb.2.1 hb.1 (Ne.symm hb.2.2.1) hBA hCov hU3
                (Eq.mp (congrArg (· < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card) hEqJ) hIneq))))
