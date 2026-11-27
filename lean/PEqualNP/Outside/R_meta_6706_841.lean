import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-6706`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_6706_841 :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x9 ∈ x3 x10 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → (x3 x10 ∩ x3 x11).card = (1 : ℕ)) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 : Finset (Fin x2)), x14.card ≤ x1 → x4.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x3 x14) x14) = Bool.false) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → x2 * x1 ≤ (100 : ℕ) * x4.size) →
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x9 ∈ x3 x10 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → (x3 x10 ∩ x3 x11).card = (1 : ℕ)) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 : Finset (Fin x2)), x14.card ≤ x1 → x4.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x3 x14) x14) = Bool.false) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → x2 * x1 ≤ (100 : ℕ) * x4.size) →
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x9 ∈ x3 x10 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → (x3 x10 ∩ x3 x11).card = (1 : ℕ)) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 : Finset (Fin x2)), x14.card ≤ x1 → x4.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x3 x14) x14) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size) := by
  classical
  intro h1 h2 x1 x2 x3 x4
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
