import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17629_3
    (hGateZero :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        x2.size ≤ (21 : ℕ) →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        ∀ (x10 : ℕ),
          (0 : ℕ) < x10 →
          x10 < x2.size →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          (∀ x16 < x2.size, (1 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = (0 : ℕ)) →
          (∀ x17 < x2.size, (11 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x17).inputs ↔ x17 = x10) →
          ∃ (x18 : Fin (11 : ℕ)),
            ↑x18 < (4 : ℕ) ∧
            have x19 : ℕ → Prop := fun (x19 : ℕ) => ∃ x20 < (11 : ℕ) + x19, ∀ (x21 : Fin (11 : ℕ) → Bool), x21 x18 = Bool.false → PEqualNP.ReadTwo.wval x2 x21 ((11 : ℕ) + x19) = PEqualNP.ReadTwo.wval x2 x21 x20;
            ∃ (x20 : ℕ) (x21 : ℕ) (x22 : ℕ), x20 < x21 ∧ x21 < x22 ∧ x22 < x2.size ∧ x19 x20 ∧ x19 x21 ∧ x19 x22)
    (hGatePos :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        x2.size ≤ (21 : ℕ) →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        ∀ (x9 x10 : ℕ),
          (1 : ℕ) ≤ x9 →
          x9 < x10 →
          x10 < x2.size →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          (∀ x16 < x2.size, (1 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = x9) →
          (∀ x17 < x2.size, (11 : ℕ) + x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x17).inputs ↔ x17 = x10) →
          ∃ (x18 : Fin (11 : ℕ)),
            ↑x18 < (4 : ℕ) ∧
            have x19 : ℕ → Prop := fun (x19 : ℕ) => ∃ x20 < (11 : ℕ) + x19, ∀ (x21 : Fin (11 : ℕ) → Bool), x21 x18 = Bool.false → PEqualNP.ReadTwo.wval x2 x21 ((11 : ℕ) + x19) = PEqualNP.ReadTwo.wval x2 x21 x20;
            ∃ (x20 : ℕ) (x21 : ℕ) (x22 : ℕ), x20 < x21 ∧ x21 < x22 ∧ x22 < x2.size ∧ x19 x20 ∧ x19 x21 ∧ x19 x22) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             ∀ (x8 : Fin (11 : ℕ)) (x9 x10 : ℕ),               ↑x8 = (1 : ℕ) →                 x9 < x10 →                   x10 < x2.size →                     (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and →                       (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or →                         (∀ x16 < x2.size, ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = x9) →                           (∀ x17 < x2.size, (11 : ℕ) + x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x17).inputs ↔ x17 = x10) →                             ∃ (x18 : Fin (11 : ℕ)),                               ↑x18 < (4 : ℕ) ∧                                 have x19 : ℕ → Prop := fun (x19 : ℕ) => ∃ x20 < (11 : ℕ) + x19, ∀ (x21 : Fin (11 : ℕ) → Bool), x21 x18 = Bool.false → PEqualNP.ReadTwo.wval x2 x21 ((11 : ℕ) + x19) = PEqualNP.ReadTwo.wval x2 x21 x20;                                 ∃ (x20 : ℕ) (x21 : ℕ) (x22 : ℕ), x20 < x21 ∧ x21 < x22 ∧ x22 < x2.size ∧ x19 x20 ∧ x19 x21 ∧ x19 x22) :=
  fun x2 h0 h1 h2 h3 h4 x8 x9 x10 hx8 hlt h10 hOp9 hOp10 hUse8 hUse9 =>
    Or.elim (Nat.eq_zero_or_pos x9)
      (fun h9 =>
        hGateZero x2 h0 h1 h2 h3 h4 x10
          (Eq.subst (motive := fun k => k < x10) h9 hlt)
          h10
          (Eq.subst (motive := fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt x2 k).op = PEqualNP.CircuitLowerBounds.GateOp.and) h9 hOp9)
          hOp10
          (Eq.subst (motive := fun k => ∀ x16 < x2.size, (1 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = k) h9
            (Eq.subst (motive := fun v => ∀ x16 < x2.size, v ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = x9) hx8 hUse8))
          (Eq.subst (motive := fun k => ∀ x17 < x2.size, (11 : ℕ) + k ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x17).inputs ↔ x17 = x10) h9 hUse9))
      (fun hPos =>
        hGatePos x2 h0 h1 h2 h3 h4 x9 x10 hPos hlt h10 hOp9 hOp10
          (Eq.subst (motive := fun v => ∀ x16 < x2.size, v ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = x9) hx8 hUse8)
          hUse9)
