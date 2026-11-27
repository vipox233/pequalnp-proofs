import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17595_2
    (hDiff5 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        have x9 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x7;
        (x2.size ≤ (21 : ℕ) ∧
          PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
          (4 : ℕ) ≤ x8 ∧ x7.card ≤ x8 ∧ x8 < (2 : ℕ) * x7.card ∧
          x8 - x7.card = (5 : ℕ)) →
        ∀ (v : Fin (11 : ℕ)), ∃ (a b : Fin (11 : ℕ)), x9.Adj a b ∧ v ≠ a ∧ v ≠ b)
    (hDiff6 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        have x9 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x7;
        (x2.size ≤ (21 : ℕ) ∧
          PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
          (4 : ℕ) ≤ x8 ∧ x7.card ≤ x8 ∧ x8 < (2 : ℕ) * x7.card ∧
          x8 - x7.card = (6 : ℕ)) →
        ∃ (a b : Fin (11 : ℕ)), x9.Adj a b) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           have x9 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x7;           (4 : ℕ) ≤ x8 → x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → (5 : ℕ) ≤ x8 - x7.card → x8 - x7.card ≤ (6 : ℕ) → (∃ (x15 : Fin (11 : ℕ)) (x16 : Fin (11 : ℕ)), x9.Adj x15 x16) ∧ (x8 - x7.card = (5 : ℕ) → ∀ (x16 : Fin (11 : ℕ)), ∃ (x17 : Fin (11 : ℕ)) (x18 : Fin (11 : ℕ)), x9.Adj x17 x18 ∧ x16 ≠ x17 ∧ x16 ≠ x18)) :=
  fun x2 hSz hLeast hTF hJ2 h4 hLe hLt hGe5 hLe6 =>
    Or.elim (Nat.eq_or_lt_of_le hGe5)
      (fun h5 =>
        let hAll := hDiff5 x2 ⟨hSz, hLeast, hTF, hJ2, h4, hLe, hLt, h5.symm⟩
        ⟨Exists.elim (hAll (0 : Fin (11 : ℕ))) fun a ha => Exists.elim ha fun b hb => ⟨a, b, hb.1⟩,
         fun _ => hAll⟩)
      (fun hGt5 =>
        let h6 := Nat.le_antisymm hLe6 hGt5
        ⟨hDiff6 x2 ⟨hSz, hLeast, hTF, hJ2, h4, hLe, hLt, h6⟩,
         fun h5 => False.elim ((show (5 : ℕ) ≠ (6 : ℕ) by decide) (Eq.trans h5.symm h6))⟩)
