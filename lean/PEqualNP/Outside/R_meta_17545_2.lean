import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17545_2
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x10 x11 : ℕ) (x14 : Finset ℕ),
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (g : ℕ) => x7 ∩ PEqualNP.TopForm.gammaE x1 x2 g;
        have x9 : ℕ := (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        PEqualNP.TopForm.centreless x1 x2 = ∅ →
        x10 ∈ x6 → x11 ∈ x6 → x10 ≠ x11 →
        ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x11 →
        ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x11 x10 →
        x7 ⊆ x6.biUnion x8 →
        (3 : ℕ) ≤ x7.card →
        (∀ g ∈ x6, (x8 g).card ≤ (2 : ℕ)) →
        x14 ⊆ x6 →
        x9 < x14.card →
        (∀ g ∈ x14, (x8 g).card = (2 : ℕ)) →
        (∀ a ∈ x14, ∀ b ∈ x14, a ≠ b → Disjoint (x8 a) (x8 b)) →
        x7.card ≤ x6.card + x9)
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x10 x11 : ℕ) (x14 : Finset ℕ),
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (g : ℕ) => x7 ∩ PEqualNP.TopForm.gammaE x1 x2 g;
        have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (PEqualNP.TopForm.centreless x1 x2).Nonempty →
        x10 ∈ x6 → x11 ∈ x6 → x10 ≠ x11 →
        ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x11 →
        ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x11 x10 →
        x7 ⊆ x6.biUnion x8 →
        (3 : ℕ) ≤ x7.card →
        (∀ g ∈ x6, (x8 g).card ≤ (2 : ℕ)) →
        x14 ⊆ x6 →
        x9 < x14.card →
        (∀ g ∈ x14, (x8 g).card = (2 : ℕ)) →
        (∀ a ∈ x14, ∀ b ∈ x14, a ≠ b → Disjoint (x8 a) (x8 b)) →
        x7.card ≤ x6.card + x9) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         have x8 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x8 : ℕ) => x7 ∩ PEqualNP.TopForm.gammaE x1 x2 x8;         have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;         (∃ (x10 : ℕ) (x11 : ℕ), x10 ∈ x6 ∧ x11 ∈ x6 ∧ x10 ≠ x11 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x11 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x11 x10) → x7 ⊆ x6.biUnion x8 → (3 : ℕ) ≤ x7.card → (∀ x13 ∈ x6, (x8 x13).card ≤ (2 : ℕ)) → (∃ x14 ⊆ x6, x9 < x14.card ∧ (∀ x15 ∈ x14, (x8 x15).card = (2 : ℕ)) ∧ ∀ x15 ∈ x14, ∀ x17 ∈ x14, x15 ≠ x17 → Disjoint (x8 x15) (x8 x17)) → x7.card ≤ x6.card + x9) := by
  intro x1 x2 hSz hLeast hTF x6 x7 x8 x9 hInc hCov h3 hLe2 hFam
  exact Exists.elim hInc fun x10 h1 =>
    Exists.elim h1 fun x11 h2 =>
      Exists.elim hFam fun x14 h14 =>
        Or.elim (Finset.eq_empty_or_nonempty (PEqualNP.TopForm.centreless x1 x2))
          (fun hEmpty => by
            have hEq : x9 = (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
              dsimp only [x9]; rw [hEmpty, Finset.card_empty]; omega
            have hLt := h14.2.1
            rw [hEq] at hLt ⊢
            exact hNoCentreless x2 x10 x11 x14 hSz hLeast hTF hEmpty h2.1 h2.2.1 h2.2.2.1 h2.2.2.2.1 h2.2.2.2.2 hCov h3 hLe2 h14.1 hLt h14.2.2.1 h14.2.2.2)
          (fun hNE =>
            hHasCentreless x2 x10 x11 x14 hSz hLeast hTF hNE h2.1 h2.2.1 h2.2.2.1 h2.2.2.2.1 h2.2.2.2.2 hCov h3 hLe2 h14.1 h14.2.1 h14.2.2.1 h14.2.2.2)
