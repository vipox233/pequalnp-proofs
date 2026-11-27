import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17535_3
    (hZeroCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (k : ℕ) => (k / (11 : ℕ), k % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
        have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;
        have x6 : (Fin (11 : ℕ) → Bool) → ℕ → Bool := PEqualNP.ReadTwo.wval x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        (PEqualNP.TopForm.centreless x1 x2).card = (0 : ℕ) →
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧ x2.size ≤ (21 : ℕ) ∧ x3 ∈ x7 ∧ x4 ∈ x7 ∧ x3 < x4 ∧ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x7.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card ∧ ∀ x8 ∈ [x3, x4], ∀ (x10 : Fin (11 : ℕ) → Bool), x6 x10 ((11 : ℕ) + x8) = Bool.true ↔ ∀ (x11 : Fin (2 : ℕ)), (∃ x12 ∈ PEqualNP.TopForm.side x2 x8 x11, x10 x12 = Bool.true) ∨ x8 = x4 ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x2 (PEqualNP.TopForm.opnd x2 x8 x11) x3 ∧ x6 x10 ((11 : ℕ) + x3) = Bool.true) →
        ∀ (x9 : Fin (11 : ℕ)) (x10 x11 : ℕ),
          (↑x9 < (4 : ℕ) ∧ x10 < x11 ∧ x11 < x2.size ∧ (x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ x12 < x2.size, ↑x9 ∈ (x5 x12).inputs ↔ x12 = x10) ∧ ∀ x12 < x2.size, (11 : ℕ) + x10 ∈ (x5 x12).inputs ↔ x12 = x11) →
          ∃ (x13 : Fin (11 : ℕ)), ↑x13 < (4 : ℕ) ∧
            have x14 : ℕ → Prop := fun (x14 : ℕ) => ∃ x15 < (11 : ℕ) + x14, ∀ (x16 : Fin (11 : ℕ) → Bool), x16 x13 = Bool.false → x6 x16 ((11 : ℕ) + x14) = x6 x16 x15;
            ∃ (x15 : ℕ) (x16 : ℕ) (x17 : ℕ), x15 < x16 ∧ x16 < x17 ∧ x17 < x2.size ∧ x14 x15 ∧ x14 x16 ∧ x14 x17)
    (hPosCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (k : ℕ) => (k / (11 : ℕ), k % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
        have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;
        have x6 : (Fin (11 : ℕ) → Bool) → ℕ → Bool := PEqualNP.ReadTwo.wval x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        (1 : ℕ) ≤ (PEqualNP.TopForm.centreless x1 x2).card →
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧ x2.size ≤ (21 : ℕ) ∧ x3 ∈ x7 ∧ x4 ∈ x7 ∧ x3 < x4 ∧ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x7.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card ∧ ∀ x8 ∈ [x3, x4], ∀ (x10 : Fin (11 : ℕ) → Bool), x6 x10 ((11 : ℕ) + x8) = Bool.true ↔ ∀ (x11 : Fin (2 : ℕ)), (∃ x12 ∈ PEqualNP.TopForm.side x2 x8 x11, x10 x12 = Bool.true) ∨ x8 = x4 ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x2 (PEqualNP.TopForm.opnd x2 x8 x11) x3 ∧ x6 x10 ((11 : ℕ) + x3) = Bool.true) →
        ∀ (x9 : Fin (11 : ℕ)) (x10 x11 : ℕ),
          (↑x9 < (4 : ℕ) ∧ x10 < x11 ∧ x11 < x2.size ∧ (x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ x12 < x2.size, ↑x9 ∈ (x5 x12).inputs ↔ x12 = x10) ∧ ∀ x12 < x2.size, (11 : ℕ) + x10 ∈ (x5 x12).inputs ↔ x12 = x11) →
          ∃ (x13 : Fin (11 : ℕ)), ↑x13 < (4 : ℕ) ∧
            have x14 : ℕ → Prop := fun (x14 : ℕ) => ∃ x15 < (11 : ℕ) + x14, ∀ (x16 : Fin (11 : ℕ) → Bool), x16 x13 = Bool.false → x6 x16 ((11 : ℕ) + x14) = x6 x16 x15;
            ∃ (x15 : ℕ) (x16 : ℕ) (x17 : ℕ), x15 < x16 ∧ x16 < x17 ∧ x17 < x2.size ∧ x14 x15 ∧ x14 x16 ∧ x14 x17) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;   have x6 : (Fin (11 : ℕ) → Bool) → ℕ → Bool := PEqualNP.ReadTwo.wval x2;   have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   (PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧ x2.size ≤ (21 : ℕ) ∧ x3 ∈ x7 ∧ x4 ∈ x7 ∧ x3 < x4 ∧ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x7.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card ∧ ∀ x8 ∈ [x3, x4], ∀ (x10 : Fin (11 : ℕ) → Bool), x6 x10 ((11 : ℕ) + x8) = Bool.true ↔ ∀ (x11 : Fin (2 : ℕ)), (∃ x12 ∈ PEqualNP.TopForm.side x2 x8 x11, x10 x12 = Bool.true) ∨ x8 = x4 ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x2 (PEqualNP.TopForm.opnd x2 x8 x11) x3 ∧ x6 x10 ((11 : ℕ) + x3) = Bool.true) →     ∀ (x9 : Fin (11 : ℕ)) (x10 x11 : ℕ),       (↑x9 < (4 : ℕ) ∧ x10 < x11 ∧ x11 < x2.size ∧ (x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ x12 < x2.size, ↑x9 ∈ (x5 x12).inputs ↔ x12 = x10) ∧ ∀ x12 < x2.size, (11 : ℕ) + x10 ∈ (x5 x12).inputs ↔ x12 = x11) →         ∃ (x13 : Fin (11 : ℕ)),           ↑x13 < (4 : ℕ) ∧             have x14 : ℕ → Prop := fun (x14 : ℕ) => ∃ x15 < (11 : ℕ) + x14, ∀ (x16 : Fin (11 : ℕ) → Bool), x16 x13 = Bool.false → x6 x16 ((11 : ℕ) + x14) = x6 x16 x15;             ∃ (x15 : ℕ) (x16 : ℕ) (x17 : ℕ), x15 < x16 ∧ x16 < x17 ∧ x17 < x2.size ∧ x14 x15 ∧ x14 x16 ∧ x14 x17) :=
  fun x2 x3 x4 hA x9 x10 x11 hB =>
    Or.elim (Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless (PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (k : ℕ) => (k / (11 : ℕ), k % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)])) x2).card)
      (fun h0 => hZeroCentreless x2 x3 x4 h0 hA x9 x10 x11 hB)
      (fun hPos => hPosCentreless x2 x3 x4 hPos hA x9 x10 x11 hB)
