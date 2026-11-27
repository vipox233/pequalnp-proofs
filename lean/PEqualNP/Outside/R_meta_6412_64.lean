import PEqualNP.Defs

-- A case split on the output wire of the circuit. Either the output is one of the 14 input
-- wires (the circuit returns one input bit), or it is a later wire. Each piece is the step
-- with that one extra conjunct.
theorem PEqualNP.Outside.R_meta_6412_64
    (outIn : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (14 : ℕ) ∧ x1.size ≤ (26 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs.Nodup) ∧ PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x3 ∈ PEqualNP.CircuitLowerBounds.fanoLines x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true))
    (outGate : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (14 : ℕ) ≤ x1.output ∧ x1.size ≤ (26 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs.Nodup) ∧ PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x3 ∈ PEqualNP.CircuitLowerBounds.fanoLines x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true)) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs.Nodup) ∧ PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x3 ∈ PEqualNP.CircuitLowerBounds.fanoLines x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) := by
  rintro ⟨x1, hb⟩
  rcases Nat.lt_or_ge x1.output (14 : ℕ) with h | h
  · exact outIn ⟨x1, h, hb⟩
  · exact outGate ⟨x1, h, hb⟩
