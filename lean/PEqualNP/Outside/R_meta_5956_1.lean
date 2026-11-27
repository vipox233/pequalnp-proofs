import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-5956`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_5956_1 :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.edgeFinset.Nonempty → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x4.size ∧ (PEqualNP.TopForm.junk x2 x10).card < (PEqualNP.TopForm.junk x2 x4).card) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.edgeFinset.Nonempty → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x4.size ∧ (PEqualNP.TopForm.junk x2 x10).card < (PEqualNP.TopForm.junk x2 x4).card) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.edgeFinset.Nonempty → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.circuitFun x1 x10 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x10.size ≤ x4.size ∧ (PEqualNP.TopForm.junk x2 x10).card < (PEqualNP.TopForm.junk x2 x4).card) := by
  classical
  intro h1 h2 x1 x2 x3 x4
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
