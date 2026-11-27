import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18257_2
    (hOrReaderCollapses :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (11 : ℕ)) (x3 : ℕ),
        PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 →
        x3 < x1.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ↑x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).inputs →
        ∃ x4 < (11 : ℕ) + x3,
          ∀ (x5 : Fin (11 : ℕ) → Bool),
            x5 x2 = Bool.false →
            PEqualNP.ReadTwo.wval x1 x5 ((11 : ℕ) + x3) = PEqualNP.ReadTwo.wval x1 x5 x4)
    (hSize21TripleCollapse :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
        x2.size = (21 : ℕ) →
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
        (∀ (x9 : Fin (11 : ℕ)), ↑x9 < (4 : ℕ) →
          (∀ x11 < x2.size, ↑x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∀ (x11 x12 x13 : ℕ), x11 < x12 → x12 < x13 → x13 < x2.size → ↑x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → ↑x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).inputs → ↑x9 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x13).inputs) →
        have x10 : Fin (11 : ℕ) → ℕ → Prop := fun (x10 : Fin (11 : ℕ)) (x11 : ℕ) => ∃ x12 < (11 : ℕ) + x11, ∀ (x13 : Fin (11 : ℕ) → Bool), x13 x10 = Bool.false → PEqualNP.ReadTwo.wval x2 x13 ((11 : ℕ) + x11) = PEqualNP.ReadTwo.wval x2 x13 x12;
        (∀ (x11 : Fin (11 : ℕ)), ↑x11 < (4 : ℕ) → ∀ x12 < x2.size, ↑x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).inputs → x10 x11 x12) →
        ∃ (x11 : Fin (11 : ℕ)), ↑x11 < (4 : ℕ) ∧ ∃ (x12 x13 x14 : ℕ), x12 < x13 ∧ x13 < x14 ∧ x14 < x2.size ∧ x10 x11 x12 ∧ x10 x11 x13 ∧ x10 x11 x14) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           ¬x2.size ≤ (20 : ℕ) →             (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →               (∀ (x9 : Fin (11 : ℕ)), ↑x9 < (4 : ℕ) → (∀ x11 < x2.size, ↑x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x11 x12 x13 : ℕ), x11 < x12 → x12 < x13 → x13 < x2.size → ↑x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → ↑x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).inputs → ↑x9 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x13).inputs) →                 ∃ (x10 : Fin (11 : ℕ)),                   ↑x10 < (4 : ℕ) ∧                     have x11 : ℕ → Prop := fun (x11 : ℕ) => ∃ x12 < (11 : ℕ) + x11, ∀ (x13 : Fin (11 : ℕ) → Bool), x13 x10 = Bool.false → PEqualNP.ReadTwo.wval x2 x13 ((11 : ℕ) + x11) = PEqualNP.ReadTwo.wval x2 x13 x12;                     ∃ (x12 : ℕ) (x13 : ℕ) (x14 : ℕ), x12 < x13 ∧ x13 < x14 ∧ x14 < x2.size ∧ x11 x12 ∧ x11 x13 ∧ x11 x14) :=
  fun x2 hL hTF hJ hLe21 hNotLe20 hIneq hDeg2 =>
    hSize21TripleCollapse x2 hL hTF hJ
      (Nat.le_antisymm hLe21 (Nat.lt_of_not_ge hNotLe20))
      hIneq hDeg2
      (fun v hv g hg hMem => hOrReaderCollapses x2 v g hL.1 hg ((hDeg2 v hv).1 g hg hMem) hMem)
