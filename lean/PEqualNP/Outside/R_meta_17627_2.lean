import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17627_2
    (hTwoCollapse :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin (11 : ℕ)) (g1 g2 : ℕ),
        PEqualNP.TopForm.IsAO2 (11 : ℕ) C →
        g1 < g2 →
        g2 < C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ↑v ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).inputs →
        (11 : ℕ) + g1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs →
        (∃ w < (11 : ℕ) + g1, ∀ (f : Fin (11 : ℕ) → Bool), f v = Bool.false →
          PEqualNP.ReadTwo.wval C f ((11 : ℕ) + g1) = PEqualNP.ReadTwo.wval C f w) ∧
        (∃ w < (11 : ℕ) + g2, ∀ (f : Fin (11 : ℕ) → Bool), f v = Bool.false →
          PEqualNP.ReadTwo.wval C f ((11 : ℕ) + g2) = PEqualNP.ReadTwo.wval C f w))
    (hWithTwoCollapsed :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have coll : Fin (11 : ℕ) → ℕ → Prop := fun v g =>
          ∃ w < (11 : ℕ) + g, ∀ (f : Fin (11 : ℕ) → Bool), f v = Bool.false →
            PEqualNP.ReadTwo.wval x2 f ((11 : ℕ) + g) = PEqualNP.ReadTwo.wval x2 f w;
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        x2.size ≤ (21 : ℕ) →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        ∀ (x9 x10 : ℕ),
          x9 < x10 →
          x10 < x2.size →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          (∀ g < x2.size, (0 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).inputs ↔ g = x9) →
          (∀ g < x2.size, (11 : ℕ) + x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).inputs ↔ g = x10) →
          coll (0 : Fin (11 : ℕ)) x9 →
          coll (0 : Fin (11 : ℕ)) x10 →
          ∃ (x18 : Fin (11 : ℕ)), ↑x18 < (4 : ℕ) ∧
            ∃ (g1 g2 g3 : ℕ), g1 < g2 ∧ g2 < g3 ∧ g3 < x2.size ∧ coll x18 g1 ∧ coll x18 g2 ∧ coll x18 g3) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             ∀ (x8 : Fin (11 : ℕ)) (x9 x10 : ℕ),               ↑x8 = (0 : ℕ) →                 x9 < x10 →                   x10 < x2.size →                     (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and →                       (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or →                         (∀ x16 < x2.size, ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = x9) →                           (∀ x17 < x2.size, (11 : ℕ) + x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x17).inputs ↔ x17 = x10) →                             ∃ (x18 : Fin (11 : ℕ)),                               ↑x18 < (4 : ℕ) ∧                                 have x19 : ℕ → Prop := fun (x19 : ℕ) => ∃ x20 < (11 : ℕ) + x19, ∀ (x21 : Fin (11 : ℕ) → Bool), x21 x18 = Bool.false → PEqualNP.ReadTwo.wval x2 x21 ((11 : ℕ) + x19) = PEqualNP.ReadTwo.wval x2 x21 x20;                                 ∃ (x20 : ℕ) (x21 : ℕ) (x22 : ℕ), x20 < x21 ∧ x21 < x22 ∧ x22 < x2.size ∧ x19 x20 ∧ x19 x21 ∧ x19 x22) := by
  intro x1 x2 hLeast hTF hJunk hSz hIneq x8 x9 x10 hx8 hlt9 hlt10 hAnd9 hOr10 hOnly8 hOnly9
  have hv0 : x8 = (0 : Fin (11 : ℕ)) := Fin.ext hx8
  subst hv0
  have h9in : ((0 : Fin (11 : ℕ)) : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).inputs :=
    (hOnly8 x9 (Nat.lt_trans hlt9 hlt10)).mpr rfl
  have h10in : (11 : ℕ) + x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs :=
    (hOnly9 x10 hlt10).mpr rfl
  have hTwo := hTwoCollapse x2 (0 : Fin (11 : ℕ)) x9 x10 hLeast.1 hlt9 hlt10 hAnd9 hOr10 h9in h10in
  exact hWithTwoCollapsed x2 hLeast hTF hJunk hSz hIneq x9 x10 hlt9 hlt10 hAnd9 hOr10 hOnly8 hOnly9 hTwo.1 hTwo.2
