import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17395_2
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) :=
        PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
          [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
           ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
           ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
           ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        let x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        let x8 : ℕ :=
          (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card +
          (PEqualNP.TopForm.junk x1 x2).card +
          (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (x2.size ≤ (21 : ℕ) ∧
         PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) ∧
         (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).Nonempty ∧
         (PEqualNP.TopForm.centreless x1 x2).Nonempty ∧
         (4 : ℕ) ≤ x8 ∧
         x7.card ≤ x8 ∧
         x8 < (2 : ℕ) * x7.card ∧
         x8 - x7.card < (7 : ℕ) ∧
         (∀ (s : Finset (Fin (11 : ℕ))),
           (∀ (u v : Fin (11 : ℕ)), s(u, v) ∈ x7 → u ∈ s ∨ v ∈ s) →
           x8 - x7.card < s.card)) →
        ∃ (c1 c2 : Finset (Fin (11 : ℕ))),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) c1 ∧
          x1.IsVertexCover ↑(c1 ∪ c2) ∧ c2.card ≤ x8 - x7.card)
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) :=
        PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
          [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
           ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
           ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
           ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        let x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        let x8 : ℕ := (2 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        (x2.size ≤ (21 : ℕ) ∧
         PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) ∧
         PEqualNP.TopForm.centreless x1 x2 = ∅ ∧
         (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card ∧
         x7.card ≤ x8 ∧
         x8 < (2 : ℕ) * x7.card ∧
         x8 - x7.card < (7 : ℕ) ∧
         (∀ (s : Finset (Fin (11 : ℕ))),
           (∀ (u v : Fin (11 : ℕ)), s(u, v) ∈ x7 → u ∈ s ∨ v ∈ s) →
           x8 - x7.card < s.card)) →
        ∃ (c1 c2 : Finset (Fin (11 : ℕ))),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) c1 ∧
          x1.IsVertexCover ↑(c1 ∪ c2) ∧ c2.card ≤ x8 - x7.card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).Nonempty → (PEqualNP.TopForm.centreless x1 x2).Nonempty ∨ (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card → (4 : ℕ) ≤ x8 → x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → x8 - x7.card < (7 : ℕ) → (∀ (x15 : Finset (Fin (11 : ℕ))), (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x7 → x16 ∈ x15 ∨ x17 ∈ x15) → x8 - x7.card < x15.card) → ∃ (x16 : Finset (Fin (11 : ℕ))) (x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x16 ∧ x1.IsVertexCover ↑(x16 ∪ x17) ∧ x17.card ≤ x8 - x7.card) :=
  fun x2 hSz hL hTF hJ2 hOrNE hDisj h4 hLe hLt2 hSub7 hCov =>
    let x1 : SimpleGraph (Fin (11 : ℕ)) :=
      PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
        [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
         ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
         ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
         ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]
    Or.elim (Finset.eq_empty_or_nonempty (PEqualNP.TopForm.centreless x1 x2))
      (fun hEmp =>
        let h2Or : (2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card :=
          Or.elim hDisj (fun hC => False.elim (Finset.not_nonempty_empty (hEmp ▸ hC))) id
        let hEqX8 :
            (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card +
              (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card =
            (2 : ℕ) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card :=
          Eq.trans
            (congrArg (fun a => (2 : ℕ) * a + (PEqualNP.TopForm.junk x1 x2).card +
              (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
              (Eq.trans (congrArg Finset.card hEmp) Finset.card_empty))
            (Eq.trans
              (congrArg (fun b => (0 : ℕ) + b + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) hJ2)
              (congrArg (fun c => c + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) (Nat.zero_add 2)))
        hEqX8.symm ▸
          hNoCentreless x2
            ⟨hSz, hL, hTF, hJ2, hEmp, h2Or,
             hEqX8 ▸ hLe, hEqX8 ▸ hLt2, hEqX8 ▸ hSub7,
             fun s hs => hEqX8 ▸ hCov s hs⟩)
      (fun hNE =>
        hHasCentreless x2 ⟨hSz, hL, hTF, hJ2, hOrNE, hNE, h4, hLe, hLt2, hSub7, hCov⟩)
