import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18394_3
    (hZeroCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x5 : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;
        have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x9 : ℕ := (2 : ℕ) * x5.card + x6.card + x7.card;
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          x5.card = (0 : ℕ) ∧
          (2 : ℕ) ≤ x6.card ∧
          (4 : ℕ) ≤ x9 ∧
          x8.card ≤ x9 ∧
          x9 < (2 : ℕ) * x8.card ∧
          (2 : ℕ) ≤ x7.card) →
        (22 : ℕ) ≤ x2.size)
    (hPosCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x5 : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;
        have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x9 : ℕ := (2 : ℕ) * x5.card + x6.card + x7.card;
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (0 : ℕ) < x5.card ∧
          (2 : ℕ) ≤ x6.card ∧
          (4 : ℕ) ≤ x9 ∧
          x8.card ≤ x9 ∧
          x9 < (2 : ℕ) * x8.card ∧
          (0 : ℕ) < x7.card) →
        (22 : ℕ) ≤ x2.size) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;       have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;       have x7 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;       have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x9 : ℕ := (2 : ℕ) * x5.card + x6.card + x7.card;       (2 : ℕ) ≤ x6.card → (4 : ℕ) ≤ x9 → x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → (0 : ℕ) < x7.card → (0 : ℕ) < x5.card ∨ (2 : ℕ) ≤ x7.card → (22 : ℕ) ≤ x2.size) :=
  fun x2 hLeast hTF h2 h4 hle hlt hpos hor =>
    Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless _ x2).card)
      (fun h0 =>
        hZeroCentreless x2
          ⟨hLeast, hTF, h0, h2, h4, hle, hlt,
            Or.elim hor (fun hcp => False.elim ((Nat.ne_of_gt hcp) h0)) id⟩)
      (fun hcp =>
        hPosCentreless x2 ⟨hLeast, hTF, hcp, h2, h4, hle, hlt, hpos⟩)
