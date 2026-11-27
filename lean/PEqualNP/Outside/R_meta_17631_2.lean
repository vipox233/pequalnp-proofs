import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17631_2
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
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x9 x10 : ℕ),
        have x19 : Fin (11 : ℕ) → ℕ → Prop := fun (x18 : Fin (11 : ℕ)) (x19 : ℕ) => ∃ x20 < (11 : ℕ) + x19, ∀ (x21 : Fin (11 : ℕ) → Bool), x21 x18 = Bool.false → PEqualNP.ReadTwo.wval x2 x21 ((11 : ℕ) + x19) = PEqualNP.ReadTwo.wval x2 x21 x20;
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
         x2.size ≤ (21 : ℕ) ∧
         (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card ∧
         x9 < x10 ∧
         x10 < x2.size ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
         (∀ x16 < x2.size, (2 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = x9) ∧
         (∀ x17 < x2.size, (11 : ℕ) + x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x17).inputs ↔ x17 = x10) ∧
         x19 (2 : Fin (11 : ℕ)) x9 ∧
         x19 (2 : Fin (11 : ℕ)) x10) →
        ∃ (x18 : Fin (11 : ℕ)), ↑x18 < (4 : ℕ) ∧ ∃ (x20 x21 x22 : ℕ), x20 < x21 ∧ x21 < x22 ∧ x22 < x2.size ∧ x19 x18 x20 ∧ x19 x18 x21 ∧ x19 x18 x22) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             ∀ (x8 : Fin (11 : ℕ)) (x9 x10 : ℕ),               ↑x8 = (2 : ℕ) →                 x9 < x10 →                   x10 < x2.size →                     (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and →                       (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or →                         (∀ x16 < x2.size, ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = x9) →                           (∀ x17 < x2.size, (11 : ℕ) + x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x17).inputs ↔ x17 = x10) →                             ∃ (x18 : Fin (11 : ℕ)),                               ↑x18 < (4 : ℕ) ∧                                 have x19 : ℕ → Prop := fun (x19 : ℕ) => ∃ x20 < (11 : ℕ) + x19, ∀ (x21 : Fin (11 : ℕ) → Bool), x21 x18 = Bool.false → PEqualNP.ReadTwo.wval x2 x21 ((11 : ℕ) + x19) = PEqualNP.ReadTwo.wval x2 x21 x20;                                 ∃ (x20 : ℕ) (x21 : ℕ) (x22 : ℕ), x20 < x21 ∧ x21 < x22 ∧ x22 < x2.size ∧ x19 x20 ∧ x19 x21 ∧ x19 x22) :=
  fun x2 hL hTF hJ hSz hIneq x8 x9 x10 hEq2 hLt hSz10 hOp9 hOp10 hReadX8 hReadX9 =>
    have hColl :=
      hAndOrChainCollapses x2 x8 x9 x10 hL.1 hLt hSz10 hOp9 hOp10
        ((hReadX8 x9 (Nat.lt_trans hLt hSz10)).mpr rfl)
        ((hReadX9 x10 hSz10).mpr rfl)
    have hEqFin : x8 = (2 : Fin (11 : ℕ)) := Fin.ext hEq2
    hWithChainCollapse x2 x9 x10
      ⟨hL, hTF, hJ, hSz, hIneq, hLt, hSz10, hOp9, hOp10,
       fun g hg => hEq2 ▸ hReadX8 g hg, hReadX9, hEqFin ▸ hColl.1, hEqFin ▸ hColl.2⟩
