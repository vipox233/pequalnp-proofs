import PEqualNP.Defs

-- A case split on the output wire of the circuit. Either the output is one of the 14 input
-- wires (the circuit returns one input bit), or it is a later wire, produced by a gate or
-- past the end of the circuit. Each case is the step with that one extra hypothesis.
theorem PEqualNP.Outside.R_meta_7065_37
    (outIn : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (14 : ℕ) → x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (12 : ℕ) ≤ {x5 ∈ Finset.range x1.size | (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op.eval [Bool.false, Bool.true] = Bool.true}.card)
    (outGate : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (14 : ℕ) ≤ x1.output → x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (12 : ℕ) ≤ {x5 ∈ Finset.range x1.size | (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op.eval [Bool.false, Bool.true] = Bool.true}.card) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (12 : ℕ) ≤ {x5 ∈ Finset.range x1.size | (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op.eval [Bool.false, Bool.true] = Bool.true}.card := by
  intro x1
  rcases Nat.lt_or_ge x1.output (14 : ℕ) with h | h
  · exact outIn x1 h
  · exact outGate x1 h
