import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17753_3
    (hUstarEq3 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (k : ℕ) => (k / (11 : ℕ), k % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        x2.size ≤ (21 : ℕ) →
        (1 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        (PEqualNP.TopForm.Ustar x1 x2).card = (3 : ℕ) →
        (16 : ℕ) + (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card ≤ x2.size + (PEqualNP.TopForm.Ustar x1 x2).card + (1 : ℕ) →
        (∀ (x11 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x2)) x11 → x11.card ≤ (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card) →
        (∀ (x12 : Fin (11 : ℕ)), ↑x12 < (4 : ℕ) → (∀ x14 < x2.size, ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x14 x15 x16 : ℕ), x14 < x15 → x15 < x16 → x16 < x2.size → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs → ↑x12 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs) →
        False)
    (hUstarGe4 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (k : ℕ) => (k / (11 : ℕ), k % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        x2.size ≤ (21 : ℕ) →
        (1 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        (4 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card →
        (16 : ℕ) + (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card ≤ x2.size + (PEqualNP.TopForm.Ustar x1 x2).card + (1 : ℕ) →
        (∀ (x11 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x2)) x11 → x11.card ≤ (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card) →
        (∀ (x12 : Fin (11 : ℕ)), ↑x12 < (4 : ℕ) → (∀ x14 < x2.size, ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x14 x15 x16 : ℕ), x14 < x15 → x15 < x16 → x16 < x2.size → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs → ↑x12 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs) →
        False) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → x2.size ≤ (21 : ℕ) → (1 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (16 : ℕ) + (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card ≤ x2.size + (PEqualNP.TopForm.Ustar x1 x2).card + (1 : ℕ) → (∀ (x11 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x2)) x11 → x11.card ≤ (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card) → (∀ (x12 : Fin (11 : ℕ)), ↑x12 < (4 : ℕ) → (∀ x14 < x2.size, ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x14 x15 x16 : ℕ), x14 < x15 → x15 < x16 → x16 < x2.size → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs → ↑x12 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs) → False) :=
  fun x2 hL hTF hJ hSz h1 h2 hU =>
    Or.elim (Nat.eq_or_lt_of_le hU)
      (fun heq => hUstarEq3 x2 hL hTF hJ hSz h1 h2 heq.symm)
      (fun hlt => hUstarGe4 x2 hL hTF hJ hSz h1 h2 hlt)
