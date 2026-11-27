import PEqualNP.Defs

-- A case split on the output wire of the circuit. Either the output is one of the 14 input
-- wires (the circuit returns one input bit), or it is a later wire, produced by a gate or
-- past the end of the circuit. Each case is the step with that one extra hypothesis.
theorem PEqualNP.Outside.R_meta_7447_37
    (outIn : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (14 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x4 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true)) → (27 : ℕ) ≤ x1.size)
    (outGate : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (14 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x4 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true)) → (27 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x4 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true)) → (27 : ℕ) ≤ x1.size := by
  intro x1
  rcases Nat.lt_or_ge x1.output (14 : ℕ) with h | h
  · exact outIn x1 h
  · exact outGate x1 h
