import PEqualNP.Defs

-- A case split on the output wire of the circuit. Either the output is one of the 42 input
-- wires (the circuit returns one input bit), or it is a later wire, produced by a gate or
-- past the end of the circuit. Each case is the step with that one extra hypothesis.
theorem PEqualNP.Outside.R_meta_7750_37
    (outIn : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (42 : ℕ) → PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 → x1.size ≤ (123 : ℕ) → ∃ (x4 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true))
    (outGate : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (42 : ℕ) ≤ x1.output → PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 → x1.size ≤ (123 : ℕ) → ∃ (x4 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (42 : ℕ) x1 → x1.size ≤ (123 : ℕ) → ∃ (x4 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) := by
  intro x1
  rcases Nat.lt_or_ge x1.output (42 : ℕ) with h | h
  · exact outIn x1 h
  · exact outGate x1 h
