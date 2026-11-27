import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17535_2
    (hAndOrChainCollapses :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (11 : ℕ)) (x3 x4 : ℕ),
        PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 →
        x3 < x4 →
        x4 < x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ↑x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).inputs →
        (11 : ℕ) + x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).inputs →
        (∃ x5 < (11 : ℕ) + x3, ∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.ReadTwo.wval x1 x6 ((11 : ℕ) + x3) = PEqualNP.ReadTwo.wval x1 x6 x5) ∧
        (∃ x5 < (11 : ℕ) + x4, ∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.ReadTwo.wval x1 x6 ((11 : ℕ) + x4) = PEqualNP.ReadTwo.wval x1 x6 x5))
    (hWithChainCollapse :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x9 : Fin (11 : ℕ)) (x10 x11 : ℕ),
        have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;
        have x6 : (Fin (11 : ℕ) → Bool) → ℕ → Bool := PEqualNP.ReadTwo.wval x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x14 : Fin (11 : ℕ) → ℕ → Prop := fun (x13 : Fin (11 : ℕ)) (x14 : ℕ) => ∃ x15 < (11 : ℕ) + x14, ∀ (x16 : Fin (11 : ℕ) → Bool), x16 x13 = Bool.false → x6 x16 ((11 : ℕ) + x14) = x6 x16 x15;
        ((PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧ x2.size ≤ (21 : ℕ) ∧ x3 ∈ x7 ∧ x4 ∈ x7 ∧ x3 < x4 ∧ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x7.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card ∧ ∀ x8 ∈ [x3, x4], ∀ (x10 : Fin (11 : ℕ) → Bool), x6 x10 ((11 : ℕ) + x8) = Bool.true ↔ ∀ (x11 : Fin (2 : ℕ)), (∃ x12 ∈ PEqualNP.TopForm.side x2 x8 x11, x10 x12 = Bool.true) ∨ x8 = x4 ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x2 (PEqualNP.TopForm.opnd x2 x8 x11) x3 ∧ x6 x10 ((11 : ℕ) + x3) = Bool.true) ∧
         (↑x9 < (4 : ℕ) ∧ x10 < x11 ∧ x11 < x2.size ∧ (x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ x12 < x2.size, ↑x9 ∈ (x5 x12).inputs ↔ x12 = x10) ∧ ∀ x12 < x2.size, (11 : ℕ) + x10 ∈ (x5 x12).inputs ↔ x12 = x11) ∧
         x14 x9 x10 ∧ x14 x9 x11) →
        ∃ (x13 : Fin (11 : ℕ)), ↑x13 < (4 : ℕ) ∧ ∃ (x15 x16 x17 : ℕ), x15 < x16 ∧ x16 < x17 ∧ x17 < x2.size ∧ x14 x13 x15 ∧ x14 x13 x16 ∧ x14 x13 x17) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;   have x6 : (Fin (11 : ℕ) → Bool) → ℕ → Bool := PEqualNP.ReadTwo.wval x2;   have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   (PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧ x2.size ≤ (21 : ℕ) ∧ x3 ∈ x7 ∧ x4 ∈ x7 ∧ x3 < x4 ∧ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x7.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card ∧ ∀ x8 ∈ [x3, x4], ∀ (x10 : Fin (11 : ℕ) → Bool), x6 x10 ((11 : ℕ) + x8) = Bool.true ↔ ∀ (x11 : Fin (2 : ℕ)), (∃ x12 ∈ PEqualNP.TopForm.side x2 x8 x11, x10 x12 = Bool.true) ∨ x8 = x4 ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x2 (PEqualNP.TopForm.opnd x2 x8 x11) x3 ∧ x6 x10 ((11 : ℕ) + x3) = Bool.true) →     ∀ (x9 : Fin (11 : ℕ)) (x10 x11 : ℕ),       (↑x9 < (4 : ℕ) ∧ x10 < x11 ∧ x11 < x2.size ∧ (x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ x12 < x2.size, ↑x9 ∈ (x5 x12).inputs ↔ x12 = x10) ∧ ∀ x12 < x2.size, (11 : ℕ) + x10 ∈ (x5 x12).inputs ↔ x12 = x11) →         ∃ (x13 : Fin (11 : ℕ)),           ↑x13 < (4 : ℕ) ∧             have x14 : ℕ → Prop := fun (x14 : ℕ) => ∃ x15 < (11 : ℕ) + x14, ∀ (x16 : Fin (11 : ℕ) → Bool), x16 x13 = Bool.false → x6 x16 ((11 : ℕ) + x14) = x6 x16 x15;             ∃ (x15 : ℕ) (x16 : ℕ) (x17 : ℕ), x15 < x16 ∧ x16 < x17 ∧ x17 < x2.size ∧ x14 x15 ∧ x14 x16 ∧ x14 x17) := by
  intro x1 x2 x3 x4 x5 x6 x7 hA x9 x10 x11 hB
  have hColl :=
    hAndOrChainCollapses x2 x9 x10 x11 hA.1.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
      ((hB.2.2.2.2.2.1 x10 (Nat.lt_trans hB.2.1 hB.2.2.1)).mpr rfl)
      ((hB.2.2.2.2.2.2 x11 hB.2.2.1).mpr rfl)
  exact hWithChainCollapse x2 x3 x4 x9 x10 x11 ⟨hA, hB, hColl.1, hColl.2⟩
