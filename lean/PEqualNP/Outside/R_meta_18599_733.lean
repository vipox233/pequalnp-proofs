import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18599_733
    (a1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size = (18 : ℕ) →
      (∀ (x6 : Fin (10 : ℕ)) (x7 : Finset ℕ), (∀ x8 ∈ x7, ∃ (x10 : PEqualNP.CircuitLowerBounds.Gate), (x1.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate }])[x8]? = Option.some x10 ∧ ↑x6 ∈ x10.inputs ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.not → x10.inputs.head? = Option.some ↑x6)) → x7.card ≤ (3 : ℕ)) →
      x1.output < 10 →
      ∃ (x7 : Fin (10 : ℕ) → Bool), ((x1.wires (List.ofFn x7)).getD x2 Bool.false || (x1.wires (List.ofFn x7)).getD x3 Bool.false) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))))
    (a2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size = (18 : ℕ) →
      (∀ (x6 : Fin (10 : ℕ)) (x7 : Finset ℕ), (∀ x8 ∈ x7, ∃ (x10 : PEqualNP.CircuitLowerBounds.Gate), (x1.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate }])[x8]? = Option.some x10 ∧ ↑x6 ∈ x10.inputs ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.not → x10.inputs.head? = Option.some ↑x6)) → x7.card ≤ (3 : ℕ)) →
      10 ≤ x1.output →
      ∃ (x7 : Fin (10 : ℕ) → Bool), ((x1.wires (List.ofFn x7)).getD x2 Bool.false || (x1.wires (List.ofFn x7)).getD x3 Bool.false) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size = (18 : ℕ) →
      (∀ (x6 : Fin (10 : ℕ)) (x7 : Finset ℕ), (∀ x8 ∈ x7, ∃ (x10 : PEqualNP.CircuitLowerBounds.Gate), (x1.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate }])[x8]? = Option.some x10 ∧ ↑x6 ∈ x10.inputs ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.not → x10.inputs.head? = Option.some ↑x6)) → x7.card ≤ (3 : ℕ)) →
      ∃ (x7 : Fin (10 : ℕ) → Bool), ((x1.wires (List.ofFn x7)).getD x2 Bool.false || (x1.wires (List.ofFn x7)).getD x3 Bool.false) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) := by
  intro x1 x2 x3 h1 h2 h3
  by_cases h : x1.output < 10
  · exact a1 x1 x2 x3 h1 h2 h3 h
  · exact a2 x1 x2 x3 h1 h2 h3 (Nat.le_of_not_lt h)
