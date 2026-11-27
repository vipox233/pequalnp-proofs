import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18073_2
    (hOutInput :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (x1.size ≤ (62 : ℕ) ∧
          x1.output < (26 : ℕ) ∧
          (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧
          (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) ∧
          (∀ (x4 x5 : Fin (26 : ℕ)), x4 ≠ x5 → ∃ x7 ∈ x1.gates, ↑x4 ∈ x7.inputs ∧ ↑x5 ∉ x7.inputs) ∧
          x1.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (13 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate }) →
        False)
    (hOutGate :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (x1.size ≤ (62 : ℕ) ∧
          (26 : ℕ) ≤ x1.output ∧
          (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧
          (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) ∧
          (∀ (x4 x5 : Fin (26 : ℕ)), x4 ≠ x5 → ∃ x7 ∈ x1.gates, ↑x4 ∈ x7.inputs ∧ ↑x5 ∉ x7.inputs) ∧
          x1.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (13 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate }) →
        False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (∀ (x4 x5 : Fin (26 : ℕ)), x4 ≠ x5 → ∃ x7 ∈ x1.gates, ↑x4 ∈ x7.inputs ∧ ↑x5 ∉ x7.inputs) → x1.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (13 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (63 : ℕ) ≤ x1.size) :=
  fun x1 hAO hEval hSep hHead =>
    Or.elim (Nat.lt_or_ge x1.size (63 : ℕ))
      (fun hLt =>
        False.elim
          (Or.elim (Nat.lt_or_ge x1.output (26 : ℕ))
            (fun hI => hOutInput x1 ⟨Nat.le_of_lt_succ hLt, hI, hAO, hEval, hSep, hHead⟩)
            (fun hG => hOutGate x1 ⟨Nat.le_of_lt_succ hLt, hG, hAO, hEval, hSep, hHead⟩)))
      id
