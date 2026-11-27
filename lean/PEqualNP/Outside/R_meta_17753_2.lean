import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17753_2
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun k : ℕ => (k / (11 : ℕ), k % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have c : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;
        have u : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x5 : ℕ := (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        have x6 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ c).card;
        have x7 : ℕ := (PEqualNP.TopForm.junk x1 x2).card;
        have g : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;
        have r : Fin (11 : ℕ) → ℕ → Prop := fun v k => ↑v ∈ (g k).inputs;
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          c.card = (0 : ℕ) ∧
          (3 : ℕ) ≤ x7 ∧
          x2.size ≤ (21 : ℕ) ∧
          (1 : ℕ) ≤ (2 : ℕ) * c.card + x5 ∧
          (2 : ℕ) * c.card + x7 + x5 < (2 : ℕ) * u.card ∧
          (3 : ℕ) ≤ u.card ∧
          (16 : ℕ) + x6 + (2 : ℕ) * c.card + x7 + x5 ≤ x2.size + u.card + (1 : ℕ) ∧
          (∀ (s : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑u) s → s.card ≤ x6) ∧
          (∀ (v : Fin (11 : ℕ)), ↑v < (4 : ℕ) → (∀ k < x2.size, r v k → (g k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ a b d : ℕ, a < b → b < d → d < x2.size → r v a → r v b → ¬r v d)) →
        False)
    (hPosCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun k : ℕ => (k / (11 : ℕ), k % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have c : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;
        have u : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x5 : ℕ := (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        have x6 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ c).card;
        have x7 : ℕ := (PEqualNP.TopForm.junk x1 x2).card;
        have g : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;
        have r : Fin (11 : ℕ) → ℕ → Prop := fun v k => ↑v ∈ (g k).inputs;
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧
          PEqualNP.TopForm.TopForm x1 x2 ∧
          (1 : ℕ) ≤ c.card ∧
          (3 : ℕ) ≤ x7 ∧
          x2.size ≤ (21 : ℕ) ∧
          (2 : ℕ) * c.card + x7 + x5 < (2 : ℕ) * u.card ∧
          (3 : ℕ) ≤ u.card ∧
          (16 : ℕ) + x6 + (2 : ℕ) * c.card + x7 + x5 ≤ x2.size + u.card + (1 : ℕ) ∧
          (∀ (s : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑u) s → s.card ≤ x6) ∧
          (∀ (v : Fin (11 : ℕ)), ↑v < (4 : ℕ) → (∀ k < x2.size, r v k → (g k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ a b d : ℕ, a < b → b < d → d < x2.size → r v a → r v b → ¬r v d)) →
        False) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → x2.size ≤ (21 : ℕ) → (1 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (16 : ℕ) + (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card ≤ x2.size + (PEqualNP.TopForm.Ustar x1 x2).card + (1 : ℕ) → (∀ (x11 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x2)) x11 → x11.card ≤ (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card) → (∀ (x12 : Fin (11 : ℕ)), ↑x12 < (4 : ℕ) → (∀ x14 < x2.size, ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x14 x15 x16 : ℕ), x14 < x15 → x15 < x16 → x16 < x2.size → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → ↑x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs → ↑x12 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs) → False) :=
  fun x2 hL hTF hJ hSz hLB hLt hU3 hSum hMC hR2 =>
    Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless _ x2).card)
      (fun hC0 => hNoCentreless x2 ⟨hL, hTF, hC0, hJ, hSz, hLB, hLt, hU3, hSum, hMC, hR2⟩)
      (fun hCPos => hPosCentreless x2 ⟨hL, hTF, hCPos, hJ, hSz, hLt, hU3, hSum, hMC, hR2⟩)
