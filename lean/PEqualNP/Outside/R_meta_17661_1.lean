import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17661_1
    (hEraseMono :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ) (inp : List Bool),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C →
        m < C.size →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        p ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs →
        inp.length = (26 : ℕ) →
        C.eval inp = Bool.true →
        (PEqualNP.CircuitMoves.eraseGate (26 : ℕ) C m p).eval inp = Bool.true)
    (hMain :
      let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit;
      have x2 : ℕ := (26 : ℕ);
      have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | PEqualNP.CircuitLowerBounds.Circuit.eval x3 (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true};
      have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty;
      have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };
      have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;
      ∀ (x7 x8 : x1),
        x7.gates = x8.gates →
        PEqualNP.MetaComplexity.Monotone2 x7 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 →
        PEqualNP.CircuitLowerBounds.Circuit.size x7 < (63 : ℕ) →
        (∃ (x13 : ℕ) (x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) →
        x4 x7 →
        x4 x8 →
        Disjoint (x3 x7) (x3 x8) →
        (∀ x17 < PEqualNP.CircuitLowerBounds.Circuit.size x7,
          ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧
          (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs,
            x3 x7 ⊆ x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20) ∧
            x3 x8 ⊆ x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20) ∧
            ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) →
        (∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        False) :
    (let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit; have x2 : ℕ := (26 : ℕ); have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | PEqualNP.CircuitLowerBounds.Circuit.eval x3 (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true}; have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty; have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }; have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and; ∀ (x7 x8 : x1), x7.gates = x8.gates → PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 → PEqualNP.CircuitLowerBounds.Circuit.size x7 < (63 : ℕ) → (∃ (x13 : ℕ) (x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) → x4 x7 → x4 x8 → Disjoint (x3 x7) (x3 x8) → (∀ x17 < PEqualNP.CircuitLowerBounds.Circuit.size x7, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) → (∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.or) → False) := by
  dsimp only
  intro x7 x8 hGates hMono7 hRB7 hSz7 hCone hx4_7 hx4_8 hDisj hMin hOr
  have hMono8 : PEqualNP.MetaComplexity.Monotone2 x8 :=
    fun g hg => hMono7 g (by rw [hGates]; exact hg)
  have hGateAt8 : ∀ j : ℕ,
      PEqualNP.MetaComplexity.NestedCover.gateAt x8 j =
      PEqualNP.MetaComplexity.NestedCover.gateAt x7 j :=
    fun j => by
      show x8.gates.getD j _ = x7.gates.getD j _
      rw [hGates]
  have hSz8 :
      PEqualNP.CircuitLowerBounds.Circuit.size x8 =
      PEqualNP.CircuitLowerBounds.Circuit.size x7 := by
    show x8.gates.length = x7.gates.length
    rw [hGates]
  have hRB8 : PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x8 :=
    fun j hj i hi =>
      hRB7 j (by show j < x7.gates.length; rw [hGates]; exact hj) i (by rw [← hGateAt8 j]; exact hi)
  have hLen : ∀ Q : Finset (Fin (13 : ℕ)),
      (PEqualNP.GenericRejection.incidenceInput Q
        (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)).length = (26 : ℕ) := by
    intro Q
    show (List.ofFn _ ++ List.ofFn _).length = (26 : ℕ)
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  refine hMain x7 x8 hGates hMono7 hRB7 hSz7 hCone hx4_7 hx4_8 hDisj ?_ hOr
  intro x17 hx17
  have hPair := (hMin x17 hx17).1
  have hErase := (hMin x17 hx17).2
  refine ⟨hPair, fun hAnd x20 hx20 => ⟨?_, ?_, hErase hAnd x20 hx20⟩⟩
  · intro Q hQ
    have hQ' := Finset.mem_filter.mp hQ
    exact Finset.mem_filter.mpr
      ⟨hQ'.1, hEraseMono x7 x17 x20 _ hMono7 hRB7 hx17 hAnd hx20 (hLen Q) hQ'.2⟩
  · intro Q hQ
    have hQ' := Finset.mem_filter.mp hQ
    exact Finset.mem_filter.mpr
      ⟨hQ'.1, hEraseMono x8 x17 x20 _ hMono8 hRB8 (by rw [hSz8]; exact hx17)
        (by rw [hGateAt8 x17]; exact hAnd) (by rw [hGateAt8 x17]; exact hx20) (hLen Q) hQ'.2⟩
