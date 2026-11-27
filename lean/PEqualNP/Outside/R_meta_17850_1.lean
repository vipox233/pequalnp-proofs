import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17850_1
    (hCentrelessZero :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        (PEqualNP.TopForm.centreless x1 x2).card = (0 : ℕ) →
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x8 : ℕ := (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        ∀ x9 ∈ x7,
          ∀ x11 ∈ x7,
            x9 ≠ x11 →
            PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 →
            have x15 : Finset ℕ := (x7.erase x9).erase x11;
            have x16 : Finset ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x16 : Finset ℕ) => x6 ∩ x16.biUnion (PEqualNP.TopForm.gammaE x1 x2);
            have x17 : Finset (Sym2 (Fin (11 : ℕ))) := x6 \ x16 x15;
            (x16 x15).card ≤ x15.card →
            x8 + (3 : ℕ) ≤ x17.card →
            x17 ⊆ PEqualNP.TopForm.gammaE x1 x2 x9 ∪ PEqualNP.TopForm.gammaE x1 x2 x11 →
            x17.card ≤ x8 + (x7.card - (x16 x15).card))
    (hCentrelessPos :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        (0 : ℕ) < (PEqualNP.TopForm.centreless x1 x2).card →
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        ∀ x9 ∈ x7,
          ∀ x11 ∈ x7,
            x9 ≠ x11 →
            PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 →
            have x15 : Finset ℕ := (x7.erase x9).erase x11;
            have x16 : Finset ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x16 : Finset ℕ) => x6 ∩ x16.biUnion (PEqualNP.TopForm.gammaE x1 x2);
            have x17 : Finset (Sym2 (Fin (11 : ℕ))) := x6 \ x16 x15;
            (x16 x15).card ≤ x15.card →
            x8 + (3 : ℕ) ≤ x17.card →
            x17 ⊆ PEqualNP.TopForm.gammaE x1 x2 x9 ∪ PEqualNP.TopForm.gammaE x1 x2 x11 →
            x17.card ≤ x8 + (x7.card - (x16 x15).card)) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;         ∀ x9 ∈ x7,           ∀ x11 ∈ x7,             x9 ≠ x11 →               PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 →                 have x15 : Finset ℕ := (x7.erase x9).erase x11;                 have x16 : Finset ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x16 : Finset ℕ) => x6 ∩ x16.biUnion (PEqualNP.TopForm.gammaE x1 x2);                 have x17 : Finset (Sym2 (Fin (11 : ℕ))) := x6 \ x16 x15;                 (x16 x15).card ≤ x15.card → x8 + (3 : ℕ) ≤ x17.card → x17 ⊆ PEqualNP.TopForm.gammaE x1 x2 x9 ∪ PEqualNP.TopForm.gammaE x1 x2 x11 → x17.card ≤ x8 + (x7.card - (x16 x15).card)) :=
  fun x2 hSz hLeast hTF x9 hx9 x11 hx11 hne hCone hle h3 hSub =>
    Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless _ x2).card)
      (fun h0 =>
        Nat.le_trans
          (hCentrelessZero x2 h0 hSz hLeast hTF x9 hx9 x11 hx11 hne hCone hle
            (Nat.le_trans (Nat.add_le_add_right (Nat.le_add_left _ _) _) h3) hSub)
          (Nat.add_le_add_right (Nat.le_add_left _ _) _))
      (fun hPos =>
        hCentrelessPos x2 hPos hSz hLeast hTF x9 hx9 x11 hx11 hne hCone hle h3 hSub)
