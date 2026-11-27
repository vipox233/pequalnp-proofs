import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17397_2
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).Nonempty →
        (PEqualNP.TopForm.centreless x1 x2).Nonempty →
        (5 : ℕ) ≤ x8 →
        x7.card ≤ x8 →
        x8 < (2 : ℕ) * x7.card →
        x8 - x7.card < (7 : ℕ) →
        (∀ (x15 : Finset (Fin (11 : ℕ))), (∀ (u v : Fin (11 : ℕ)), s(u, v) ∈ x7 → u ∈ x15 ∨ v ∈ x15) → x8 - x7.card < x15.card) →
        ∃ (x16 x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x16 ∧ x1.IsVertexCover ↑(x16 ∪ x17) ∧ x17.card ≤ x8 - x7.card)
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ := (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        PEqualNP.TopForm.centreless x1 x2 = ∅ →
        (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card →
        (5 : ℕ) ≤ x8 →
        x7.card ≤ x8 →
        x8 < (2 : ℕ) * x7.card →
        x8 - x7.card < (7 : ℕ) →
        (∀ (x15 : Finset (Fin (11 : ℕ))), (∀ (u v : Fin (11 : ℕ)), s(u, v) ∈ x7 → u ∈ x15 ∨ v ∈ x15) → x8 - x7.card < x15.card) →
        ∃ (x16 x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x16 ∧ x1.IsVertexCover ↑(x16 ∪ x17) ∧ x17.card ≤ x8 - x7.card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).Nonempty → (PEqualNP.TopForm.centreless x1 x2).Nonempty ∨ (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card → (5 : ℕ) ≤ x8 → x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → x8 - x7.card < (7 : ℕ) → (∀ (x15 : Finset (Fin (11 : ℕ))), (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x7 → x16 ∈ x15 ∨ x17 ∈ x15) → x8 - x7.card < x15.card) → ∃ (x16 : Finset (Fin (11 : ℕ))) (x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x16 ∧ x1.IsVertexCover ↑(x16 ∪ x17) ∧ x17.card ≤ x8 - x7.card) := by
  intro x1 x2 hSz hLeast hTF hJunk x7 x8 hOrNE hDisj h5 hLe hLt2 hSub7 hCov
  exact Or.elim (Finset.eq_empty_or_nonempty (PEqualNP.TopForm.centreless x1 x2))
    (fun hEmpty => by
      have hGe2 : (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card :=
        Or.elim hDisj (fun hNE => False.elim (Finset.not_nonempty_empty (hEmpty ▸ hNE))) id
      have hEq : x8 = (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
        dsimp only [x8]; rw [hEmpty, Finset.card_empty]; omega
      rw [hEq] at h5 hLe hLt2 hSub7 hCov ⊢
      exact hNoCentreless x2 hSz hLeast hTF hJunk hEmpty hGe2 h5 hLe hLt2 hSub7 hCov)
    (fun hNE =>
      hHasCentreless x2 hSz hLeast hTF hJunk hOrNE hNE h5 hLe hLt2 hSub7 hCov)
