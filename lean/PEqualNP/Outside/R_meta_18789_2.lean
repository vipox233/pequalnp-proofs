import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18789_2
    (hUnpackDeg2Chain :
      ∀ (G : SimpleGraph (Fin (11 : ℕ))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin (11 : ℕ)) (g h : ℕ),
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt C;
        (PEqualNP.TopForm.IsLeastAO G C ∧
         g < h ∧ h < C.size ∧
         ↑v ∈ (ga g).inputs ∧
         (11 : ℕ) + g ∈ (ga h).inputs) →
        (∃ w < (11 : ℕ) + g, w ≠ ↑v ∧ ((ga g).inputs = [↑v, w] ∨ (ga g).inputs = [w, ↑v])) ∧
        (∃ u < (11 : ℕ) + h, u ≠ (11 : ℕ) + g ∧ ((ga h).inputs = [(11 : ℕ) + g, u] ∨ (ga h).inputs = [u, (11 : ℕ) + g])))
    (hShrinkWithOperands :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Fin (11 : ℕ)) (x9 x10 w u : ℕ),
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
         x2.size ≤ (21 : ℕ) ∧
         (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card ∧
         ↑x8 < (4 : ℕ) ∧ x9 < x10 ∧ x10 < x2.size ∧
         (ga x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
         (ga x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
         w < (11 : ℕ) + x9 ∧ w ≠ ↑x8 ∧ ((ga x9).inputs = [↑x8, w] ∨ (ga x9).inputs = [w, ↑x8]) ∧
         u < (11 : ℕ) + x10 ∧ u ≠ (11 : ℕ) + x9 ∧ ((ga x10).inputs = [(11 : ℕ) + x9, u] ∨ (ga x10).inputs = [u, (11 : ℕ) + x9]) ∧
         (∀ x16 < x2.size, ↑x8 ∈ (ga x16).inputs ↔ x16 = x9) ∧
         (∀ x17 < x2.size, (11 : ℕ) + x9 ∈ (ga x17).inputs ↔ x17 = x10) ∧
         (∀ (x18 : ℕ), (11 : ℕ) + x18 ∈ (ga x9).inputs →
           ∃ x20 < x2.size, x20 ≠ x9 ∧ (11 : ℕ) + x18 ∈ (ga x20).inputs)) →
        ∃ (x19 : Fin (11 : ℕ)) (x20 : PEqualNP.CircuitLowerBounds.Circuit),
          ↑x19 < (4 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (11 : ℕ) x20 ∧ x20.size ≤ (18 : ℕ) ∧
          ∀ (x21 : Fin (11 : ℕ) → Bool), x21 x19 = Bool.false →
            PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x20 x21 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x21) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → x2.size ≤ (21 : ℕ) → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → ∀ (x8 : Fin (11 : ℕ)) (x9 x10 : ℕ), ↑x8 < (4 : ℕ) → x9 < x10 → x10 < x2.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or → (∀ x16 < x2.size, ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x16).inputs ↔ x16 = x9) → (∀ x17 < x2.size, (11 : ℕ) + x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x17).inputs ↔ x17 = x10) → (∀ (x18 : ℕ), (11 : ℕ) + x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).inputs → ∃ x20 < x2.size, x20 ≠ x9 ∧ (11 : ℕ) + x18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x20).inputs) → ∃ (x19 : Fin (11 : ℕ)) (x20 : PEqualNP.CircuitLowerBounds.Circuit), ↑x19 < (4 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (11 : ℕ) x20 ∧ x20.size ≤ (18 : ℕ) ∧ ∀ (x21 : Fin (11 : ℕ) → Bool), x21 x19 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x20 x21 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x21) := by
  intro x1 x2 hL hTF hJ hSz hBnd x8 x9 x10 h8 h910 h10 hOp9 hOp10 hR8 hR9 hShared
  exact
    let hU := hUnpackDeg2Chain x1 x2 x8 x9 x10
      ⟨hL, h910, h10, (hR8 x9 (Nat.lt_trans h910 h10)).mpr rfl, (hR9 x10 h10).mpr rfl⟩
    Exists.elim hU.1 fun w hw =>
      Exists.elim hU.2 fun u hu =>
        hShrinkWithOperands x2 x8 x9 x10 w u
          ⟨hL, hTF, hJ, hSz, hBnd, h8, h910, h10, hOp9, hOp10,
           hw.1, hw.2.1, hw.2.2, hu.1, hu.2.1, hu.2.2, hR8, hR9, hShared⟩
