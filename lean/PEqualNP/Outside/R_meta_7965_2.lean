import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7965_2
    (hZeroCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        ((PEqualNP.TopForm.centreless x1 x2).card = (0 : ℕ) ∧
          x2.size ≤ (21 : ℕ) ∧
          PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
          x7.card ≤ x8 ∧ x8 < (2 : ℕ) * x7.card ∧
          s((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))) ∈ x7 ∧
          s((4 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))) ∈ x7 ∧
          s((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))) ∈ x7 ∧
          s((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))) ∈ x7 ∧
          s((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))) ∈ x7) →
        ∃ (x16 : Finset (Fin (11 : ℕ))), (∀ (x17 x18 : Fin (11 : ℕ)), s(x17, x18) ∈ x7 → x17 ∈ x16 ∨ x18 ∈ x16) ∧ x7.card + x16.card ≤ x8 + (1 : ℕ))
    (hPosCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        ((1 : ℕ) ≤ (PEqualNP.TopForm.centreless x1 x2).card ∧
          x2.size ≤ (21 : ℕ) ∧
          PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
          x7.card ≤ x8 ∧ x8 < (2 : ℕ) * x7.card ∧
          s((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))) ∈ x7 ∧
          s((4 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))) ∈ x7 ∧
          s((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))) ∈ x7 ∧
          s((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))) ∈ x7 ∧
          s((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))) ∈ x7) →
        ∃ (x16 : Finset (Fin (11 : ℕ))), (∀ (x17 x18 : Fin (11 : ℕ)), s(x17, x18) ∈ x7 → x17 ∈ x16 ∨ x18 ∈ x16) ∧ x7.card + x16.card ≤ x8 + (1 : ℕ)) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → s((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))) ∈ x7 → s((4 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))) ∈ x7 → s((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))) ∈ x7 → s((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))) ∈ x7 → s((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))) ∈ x7 → ∃ (x16 : Finset (Fin (11 : ℕ))), (∀ (x17 x18 : Fin (11 : ℕ)), s(x17, x18) ∈ x7 → x17 ∈ x16 ∨ x18 ∈ x16) ∧ x7.card + x16.card ≤ x8 + (1 : ℕ)) :=
  fun x2 hSz hLeast hTF hJunk hLe hLt he1 he2 he3 he4 he5 =>
    Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless _ x2).card)
      (fun h0 => hZeroCentreless x2 ⟨h0, hSz, hLeast, hTF, hJunk, hLe, hLt, he1, he2, he3, he4, he5⟩)
      (fun hPos => hPosCentreless x2 ⟨hPos, hSz, hLeast, hTF, hJunk, hLe, hLt, he1, he2, he3, he4, he5⟩)
