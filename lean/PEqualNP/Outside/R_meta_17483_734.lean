import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-17483`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_17483_734 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x5 : Fin (10 : ℕ)) => x3.testBit ↑x5) = Bool.true) → (∀ x4 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x6 : Fin (10 : ℕ)) => x4.testBit ↑x6) = Bool.false) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x5 : Fin (6 : ℕ) → ℕ), Function.Injective x5 ∧ ∀ (x6 : Fin (6 : ℕ)), x5 x6 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x5 x6)).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x5 : Fin (10 : ℕ)) => x3.testBit ↑x5) = Bool.true) → (∀ x4 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x6 : Fin (10 : ℕ)) => x4.testBit ↑x6) = Bool.false) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x5 : Fin (6 : ℕ) → ℕ), Function.Injective x5 ∧ ∀ (x6 : Fin (6 : ℕ)), x5 x6 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x5 x6)).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x5 : Fin (10 : ℕ)) => x3.testBit ↑x5) = Bool.true) → (∀ x4 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 fun (x6 : Fin (10 : ℕ)) => x4.testBit ↑x6) = Bool.false) → ∃ (x5 : Fin (6 : ℕ) → ℕ), Function.Injective x5 ∧ ∀ (x6 : Fin (6 : ℕ)), x5 x6 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x5 x6)).op = PEqualNP.CircuitLowerBounds.GateOp.and) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
