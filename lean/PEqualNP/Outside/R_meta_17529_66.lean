import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-17529`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_17529_66 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (17 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard → {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (21 : ℕ) ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (17 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard → {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (21 : ℕ) ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (17 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard → {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) → (21 : ℕ) ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
