import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18255_2
    (hReaderCard :
      let G : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
        PEqualNP.TopForm.IsLeastAO G C ∧
        (∀ v : Fin (11 : ℕ), ↑v < (4 : ℕ) →
          (∀ j < C.size, ↑v ∈ (ga j).inputs → (ga j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∀ j1 j2 j3 : ℕ, j1 < j2 → j2 < j3 → j3 < C.size → ↑v ∈ (ga j1).inputs → ↑v ∈ (ga j2).inputs → ↑v ∉ (ga j3).inputs) →
        ∀ v : Fin (11 : ℕ), ↑v < (4 : ℕ) →
          (1 : ℕ) ≤ (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card ∧
          (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card ≤ (2 : ℕ) ∧
          ∀ j ∈ PEqualNP.TopForm.readers (0 : ℕ) C ↑v, (ga j).op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (hWithReaderBounds :
      let G : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C ∧ PEqualNP.TopForm.TopForm G C ∧
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card ∧ C.size ≤ (20 : ℕ) ∧
        (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar G C).card ∧
        (∀ v : Fin (11 : ℕ), ↑v < (4 : ℕ) →
          (1 : ℕ) ≤ (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card ∧
          (PEqualNP.TopForm.readers (0 : ℕ) C ↑v).card ≤ (2 : ℕ) ∧
          ∀ j ∈ PEqualNP.TopForm.readers (0 : ℕ) C ↑v, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        ∃ v : Fin (11 : ℕ), ↑v < (4 : ℕ) ∧
          have col : ℕ → Prop := fun j => ∃ w < (11 : ℕ) + j, ∀ y : Fin (11 : ℕ) → Bool, y v = Bool.false → PEqualNP.ReadTwo.wval C y ((11 : ℕ) + j) = PEqualNP.ReadTwo.wval C y w;
          ∃ j1 j2 j3 : ℕ, j1 < j2 ∧ j2 < j3 ∧ j3 < C.size ∧ col j1 ∧ col j2 ∧ col j3) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           x2.size ≤ (20 : ℕ) →             (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →               (∀ (x9 : Fin (11 : ℕ)), ↑x9 < (4 : ℕ) → (∀ x11 < x2.size, ↑x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x11 x12 x13 : ℕ), x11 < x12 → x12 < x13 → x13 < x2.size → ↑x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → ↑x9 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).inputs → ↑x9 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x13).inputs) →                 ∃ (x10 : Fin (11 : ℕ)),                   ↑x10 < (4 : ℕ) ∧                     have x11 : ℕ → Prop := fun (x11 : ℕ) => ∃ x12 < (11 : ℕ) + x11, ∀ (x13 : Fin (11 : ℕ) → Bool), x13 x10 = Bool.false → PEqualNP.ReadTwo.wval x2 x13 ((11 : ℕ) + x11) = PEqualNP.ReadTwo.wval x2 x13 x12;                     ∃ (x12 : ℕ) (x13 : ℕ) (x14 : ℕ), x12 < x13 ∧ x13 < x14 ∧ x14 < x2.size ∧ x11 x12 ∧ x11 x13 ∧ x11 x14) :=
  fun C hL hTF hJ _ h20 hCh hR => hWithReaderBounds C ⟨hL, hTF, hJ, h20, hCh, hReaderCard C ⟨hL, hR⟩⟩
