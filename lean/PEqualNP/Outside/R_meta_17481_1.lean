import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-17481`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_17481_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin x2 → ℕ), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x5 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x7 : Fin (10 : ℕ)) => x5.testBit ↑x7) = Bool.true) → (∀ x6 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x8 : Fin (10 : ℕ)) => x6.testBit ↑x8) = Bool.false) → Function.Injective x3 → (∀ (x8 : Fin x2), x3 x8 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 x8)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (14 : ℕ) + x2 ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin x2 → ℕ), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x5 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x7 : Fin (10 : ℕ)) => x5.testBit ↑x7) = Bool.true) → (∀ x6 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x8 : Fin (10 : ℕ)) => x6.testBit ↑x8) = Bool.false) → Function.Injective x3 → (∀ (x8 : Fin x2), x3 x8 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 x8)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (14 : ℕ) + x2 ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin x2 → ℕ), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x5 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x7 : Fin (10 : ℕ)) => x5.testBit ↑x7) = Bool.true) → (∀ x6 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x8 : Fin (10 : ℕ)) => x6.testBit ↑x8) = Bool.false) → Function.Injective x3 → (∀ (x8 : Fin x2), x3 x8 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 x8)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (14 : ℕ) + x2 ≤ x1.size) := by
  classical
  intro h1 h2 x1 x2 x3
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
