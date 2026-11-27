import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The circuit has no gates, or it has at least one.
theorem PEqualNP.Outside.R_meta_6706_840
    (emptyCircuit :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x9 ∈ x3 x10 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → (x3 x10 ∩ x3 x11).card = (1 : ℕ)) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 : Finset (Fin x2)), x14.card ≤ x1 → x4.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x3 x14) x14) = Bool.false) → (x4.size = (0 : ℕ)) → x2 * x1 ≤ (100 : ℕ) * x4.size)
    (nonEmptyCircuit :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x9 ∈ x3 x10 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → (x3 x10 ∩ x3 x11).card = (1 : ℕ)) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 : Finset (Fin x2)), x14.card ≤ x1 → x4.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x3 x14) x14) = Bool.false) → ((1 : ℕ) ≤ x4.size) → x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x9 ∈ x3 x10 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → (x3 x10 ∩ x3 x11).card = (1 : ℕ)) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 : Finset (Fin x2)), x14.card ≤ x1 → x4.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x3 x14) x14) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  by_cases h : (x4.size = (0 : ℕ))
  · exact emptyCircuit x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h
  · exact nonEmptyCircuit x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (by omega)
