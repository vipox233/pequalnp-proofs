import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17810_1
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (PEqualNP.TopForm.centreless x1 x2).card = (0 : ℕ) →
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        (2 : ℕ) ≤ x6.card →
        (∃ (x9 : ℕ) (x10 : ℕ), x9 ∈ x6 ∧ x10 ∈ x6 ∧ x9 ≠ x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x9) →
        (3 : ℕ) ≤ x7.card →
        ∀ x11 ⊆ x7, x11.Nonempty → (x7 \ x11).card ≤ {x14 ∈ x6 | Disjoint x11 (PEqualNP.TopForm.gammaE x1 x2 x14)}.card → (∀ x15 ∈ x6, (x11 ∩ PEqualNP.TopForm.gammaE x1 x2 x15).card ≠ (1 : ℕ)) → (∀ x16 ∈ x7, ∃ x18 ∈ x6, x16 ∈ PEqualNP.TopForm.gammaE x1 x2 x18) → x11.card ≤ (x6.card - (x7 \ x11).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (1 : ℕ) ≤ (PEqualNP.TopForm.centreless x1 x2).card →
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        (2 : ℕ) ≤ x6.card →
        (∃ (x9 : ℕ) (x10 : ℕ), x9 ∈ x6 ∧ x10 ∈ x6 ∧ x9 ≠ x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x9) →
        (3 : ℕ) ≤ x7.card →
        ∀ x11 ⊆ x7, x11.Nonempty → (x7 \ x11).card ≤ {x14 ∈ x6 | Disjoint x11 (PEqualNP.TopForm.gammaE x1 x2 x14)}.card → (∀ x15 ∈ x6, (x11 ∩ PEqualNP.TopForm.gammaE x1 x2 x15).card ≠ (1 : ℕ)) → (∀ x16 ∈ x7, ∃ x18 ∈ x6, x16 ∈ PEqualNP.TopForm.gammaE x1 x2 x18) → x11.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x11).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         (2 : ℕ) ≤ x6.card → (∃ (x9 : ℕ) (x10 : ℕ), x9 ∈ x6 ∧ x10 ∈ x6 ∧ x9 ≠ x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x9) → (3 : ℕ) ≤ x7.card → ∀ x11 ⊆ x7, x11.Nonempty → (x7 \ x11).card ≤ {x14 ∈ x6 | Disjoint x11 (PEqualNP.TopForm.gammaE x1 x2 x14)}.card → (∀ x15 ∈ x6, (x11 ∩ PEqualNP.TopForm.gammaE x1 x2 x15).card ≠ (1 : ℕ)) → (∀ x16 ∈ x7, ∃ x18 ∈ x6, x16 ∈ PEqualNP.TopForm.gammaE x1 x2 x18) → x11.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x11).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :=
  fun x2 hSz hLeast hTF h2 hIncomp h3 x11 hSub hNon hDiff hNe1 hCov =>
    Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless (PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]) x2).card)
      (fun h0 =>
        Eq.subst (motive := fun n => x11.card ≤ (2 : ℕ) * n + ((PEqualNP.TopForm.junk _ x2).card - (PEqualNP.TopForm.Ustar _ x2 \ x11).card) + (PEqualNP.TopForm.orN _ x2 \ PEqualNP.TopForm.lam _ x2).card) h0.symm
          (Eq.subst (motive := fun m => x11.card ≤ m + (PEqualNP.TopForm.orN _ x2 \ PEqualNP.TopForm.lam _ x2).card) (Nat.zero_add ((PEqualNP.TopForm.junk _ x2).card - (PEqualNP.TopForm.Ustar _ x2 \ x11).card)).symm
            (hNoCentreless x2 hSz hLeast hTF h0 h2 hIncomp h3 x11 hSub hNon hDiff hNe1 hCov)))
      (fun hPos => hHasCentreless x2 hSz hLeast hTF hPos h2 hIncomp h3 x11 hSub hNon hDiff hNe1 hCov)
