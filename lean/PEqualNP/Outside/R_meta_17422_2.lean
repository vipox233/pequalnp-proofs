import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17422_2
    (hExact5 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x14 x16 : Finset (Fin (11 : ℕ))),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        x7.card = (5 : ℕ) →
        x8 = (8 : ℕ) →
        x14.card = (8 : ℕ) →
        x16 ⊆ x14 →
        x16.card = (4 : ℕ) →
        (∀ a ∈ x16, ∀ b ∈ x16, ¬x1.Adj a b) →
        ∃ u ∈ x14, ∃ v ∈ x14, x1.Adj u v ∧ s(u, v) ∉ x7)
    (hGe6 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x14 x16 : Finset (Fin (11 : ℕ))),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        (6 : ℕ) ≤ x7.card →
        x8 = x7.card + (3 : ℕ) →
        x14.card = (8 : ℕ) →
        x16 ⊆ x14 →
        x16.card = (4 : ℕ) →
        (∀ a ∈ x16, ∀ b ∈ x16, ¬x1.Adj a b) →
        ∃ u ∈ x14, ∃ v ∈ x14, x1.Adj u v ∧ s(u, v) ∉ x7) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           ∀ (x9 : ℕ), x9 = (3 : ℕ) → x8 = x7.card + x9 → x8 < (2 : ℕ) * x7.card → [(1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (8 : ℕ), (12 : ℕ), (16 : ℕ)].getD x9 (0 : ℕ) ≤ x7.card → ∀ (x14 : Finset (Fin (11 : ℕ))), x14.card = x9 + (5 : ℕ) → (∃ x16 ⊆ x14, x16.card = (4 : ℕ) ∧ ∀ x17 ∈ x16, ∀ x19 ∈ x16, ¬x1.Adj x17 x19) → ∃ x17 ∈ x14, ∃ x18 ∈ x14, x1.Adj x17 x18 ∧ s(x17, x18) ∉ x7) := by
  intro x1 x2 hSz hLeast hTF hJunk x7 x8 x9 hx9 hEq8 _ hLB x14 hCard14 hEx
  subst hx9
  have h5 : (5 : ℕ) ≤ x7.card := hLB
  exact Exists.elim hEx fun x16 h16 =>
    Or.elim (Nat.eq_or_lt_of_le h5)
      (fun hEq5 =>
        hExact5 x2 x14 x16 hSz hLeast hTF hJunk hEq5.symm
          (Eq.trans hEq8 (congrArg (· + (3 : ℕ)) hEq5.symm))
          hCard14 h16.1 h16.2.1 h16.2.2)
      (fun hGt5 =>
        hGe6 x2 x14 x16 hSz hLeast hTF hJunk hGt5 hEq8
          hCard14 h16.1 h16.2.1 h16.2.2)
