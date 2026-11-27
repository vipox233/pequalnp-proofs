import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17661_2
    (hOutLt :
      have x2 : ℕ := (26 : ℕ);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | x3.eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true};
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty;
      have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };
      have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (x7 x8 : PEqualNP.CircuitLowerBounds.Circuit) (x13 x14 : ℕ),
        (x7.output < x8.output ∧
          x7.gates = x8.gates ∧
          PEqualNP.MetaComplexity.Monotone2 x7 ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 ∧
          x7.size < (63 : ℕ) ∧
          x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14 ∧
          x4 x7 ∧ x4 x8 ∧ Disjoint (x3 x7) (x3 x8) ∧
          (∀ x17 < x7.size, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) ∧
          (∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        False)
    (hOutGt :
      have x2 : ℕ := (26 : ℕ);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | x3.eval (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true};
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty;
      have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };
      have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (x7 x8 : PEqualNP.CircuitLowerBounds.Circuit) (x13 x14 : ℕ),
        (x8.output < x7.output ∧
          x7.gates = x8.gates ∧
          PEqualNP.MetaComplexity.Monotone2 x7 ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 ∧
          x7.size < (63 : ℕ) ∧
          x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14 ∧
          x4 x7 ∧ x4 x8 ∧ Disjoint (x3 x7) (x3 x8) ∧
          (∀ x17 < x7.size, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) ∧
          (∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        False) :
    (let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit; have x2 : ℕ := (26 : ℕ); have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | PEqualNP.CircuitLowerBounds.Circuit.eval x3 (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true}; have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty; have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }; have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and; ∀ (x7 x8 : x1), x7.gates = x8.gates → PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 → PEqualNP.CircuitLowerBounds.Circuit.size x7 < (63 : ℕ) → (∃ (x13 : ℕ) (x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) → x4 x7 → x4 x8 → Disjoint (x3 x7) (x3 x8) → (∀ x17 < PEqualNP.CircuitLowerBounds.Circuit.size x7, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) → (∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.or) → False) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 hG hM hRB hSz hCone hx47 hx48 hDisj hMin hOr
  rcases hCone with ⟨x13, x14, hA13, hA14, hIC⟩
  have hNeOut : x7.output ≠ x8.output := by
    intro hEqOut
    have hEqC : x7 = x8 := by
      cases x7; cases x8; cases hG; cases hEqOut; rfl
    rw [hEqC] at hx47 hDisj
    exact Finset.not_disjoint_iff.mpr ⟨hx47.2.choose, hx47.2.choose_spec, hx47.2.choose_spec⟩ hDisj
  rcases Nat.lt_or_gt_of_ne hNeOut with hLt | hGt
  · exact hOutLt x7 x8 x13 x14 ⟨hLt, hG, hM, hRB, hSz, hA13, hA14, hIC, hx47, hx48, hDisj, hMin, hOr⟩
  · exact hOutGt x7 x8 x13 x14 ⟨hGt, hG, hM, hRB, hSz, hA13, hA14, hIC, hx47, hx48, hDisj, hMin, hOr⟩
