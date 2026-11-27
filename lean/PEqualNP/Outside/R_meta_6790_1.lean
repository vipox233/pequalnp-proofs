import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-6790`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_6790_1 :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (1 : ℕ) ≤ x1 → (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x5.gates[1]? = Option.some g) → Fintype.card { x10 : Fin x2 × Fin x2 // x3 x10.1 x10.2 ∧ ∃ (x11 : Fin (4 : ℕ)), [↑x11, (1 : ℕ)] ∈ (PEqualNP.ReadK.readVectors x5 (x2 + x2) [↑x10.1, x2 + ↑x10.2] (2 : ℕ)).getD x5.output [] } ≤ (8 : ℕ) * x5.size + x2) →
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (1 : ℕ) ≤ x1 → (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x5.gates[1]? = Option.some g) → Fintype.card { x10 : Fin x2 × Fin x2 // x3 x10.1 x10.2 ∧ ∃ (x11 : Fin (4 : ℕ)), [↑x11, (1 : ℕ)] ∈ (PEqualNP.ReadK.readVectors x5 (x2 + x2) [↑x10.1, x2 + ↑x10.2] (2 : ℕ)).getD x5.output [] } ≤ (8 : ℕ) * x5.size + x2) →
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (1 : ℕ) ≤ x1 → (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) → Fintype.card { x10 : Fin x2 × Fin x2 // x3 x10.1 x10.2 ∧ ∃ (x11 : Fin (4 : ℕ)), [↑x11, (1 : ℕ)] ∈ (PEqualNP.ReadK.readVectors x5 (x2 + x2) [↑x10.1, x2 + ↑x10.2] (2 : ℕ)).getD x5.output [] } ≤ (8 : ℕ) * x5.size + x2) := by
  classical
  intro h1 h2 x1 x2 x3 x4 x5
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x5.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
