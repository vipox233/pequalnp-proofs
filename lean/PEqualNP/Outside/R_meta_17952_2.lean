import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17952_2
    (hMaxFanoutLe3 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
        (∀ (x3 : Fin (26 : ℕ)), (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x3 ∈ x4.inputs)) x1.gates).length ≤ (3 : ℕ)) →
        x1.size = (62 : ℕ) →
        (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) →
        (∀ (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ), x2 x6 x7 = (x1.wires (List.ofFn x6)).getD x7 Bool.false) →
        (∀ (x7 : Fin (26 : ℕ) → Bool), x2 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        ∃ (x8 : Fin (26 : ℕ)) (x9 : Finset ℕ), (5 : ℕ) ≤ x9.card ∧ ∀ x10 ∈ x9, x10 < x1.size ∧ ∃ (x12 : Bool) (x13 : Bool), ∃ x14 < (26 : ℕ) + x10, ∀ (x15 : Fin (26 : ℕ) → Bool), x15 x8 = Bool.false → x2 x15 ((26 : ℕ) + x10) = (x12 && x2 x15 x14 || x13))
    (hHasFanout4 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool),
        (∀ (x3 : Fin (26 : ℕ)), (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x3 ∈ x4.inputs)) x1.gates).length ≤ (4 : ℕ)) →
        (∃ (x3 : Fin (26 : ℕ)), (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x3 ∈ x4.inputs)) x1.gates).length = (4 : ℕ)) →
        x1.size = (62 : ℕ) →
        (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) →
        (∀ (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ), x2 x6 x7 = (x1.wires (List.ofFn x6)).getD x7 Bool.false) →
        (∀ (x7 : Fin (26 : ℕ) → Bool), x2 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        ∃ (x8 : Fin (26 : ℕ)) (x9 : Finset ℕ), (5 : ℕ) ≤ x9.card ∧ ∀ x10 ∈ x9, x10 < x1.size ∧ ∃ (x12 : Bool) (x13 : Bool), ∃ x14 < (26 : ℕ) + x10, ∀ (x15 : Fin (26 : ℕ) → Bool), x15 x8 = Bool.false → x2 x15 ((26 : ℕ) + x10) = (x12 && x2 x15 x14 || x13)) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool), (∀ (x3 : Fin (26 : ℕ)), (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x3 ∈ x4.inputs)) x1.gates).length ≤ (4 : ℕ)) → x1.size = (62 : ℕ) → (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) → (∀ (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ), x2 x6 x7 = (x1.wires (List.ofFn x6)).getD x7 Bool.false) → (∀ (x7 : Fin (26 : ℕ) → Bool), x2 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) → ∃ (x8 : Fin (26 : ℕ)) (x9 : Finset ℕ), (5 : ℕ) ≤ x9.card ∧ ∀ x10 ∈ x9, x10 < x1.size ∧ ∃ (x12 : Bool) (x13 : Bool), ∃ x14 < (26 : ℕ) + x10, ∀ (x15 : Fin (26 : ℕ) → Bool), x15 x8 = Bool.false → x2 x15 ((26 : ℕ) + x10) = (x12 && x2 x15 x14 || x13)) :=
  fun x1 x2 hFan hSz hAO2 hWires hEval =>
    Or.elim (Classical.em (∃ (x3 : Fin (26 : ℕ)), (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x3 ∈ x4.inputs)) x1.gates).length = (4 : ℕ)))
      (fun hEx => hHasFanout4 x1 x2 hFan hEx hSz hAO2 hWires hEval)
      (fun hNo4 => hMaxFanoutLe3 x1 x2 (fun x3 => Nat.le_of_lt_succ (Nat.lt_of_le_of_ne (hFan x3) (fun hEq => hNo4 ⟨x3, hEq⟩))) hSz hAO2 hWires hEval)
