import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-18378`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_18378_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (32 : ℕ)) (x5 : Fin (32 : ℕ)), (↑x4 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x5 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x4 (0 : ℕ)).testBit (↑x5 - (16 : ℕ)) = Bool.true) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (79 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (32 : ℕ)) (x5 : Fin (32 : ℕ)), (↑x4 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x5 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x4 (0 : ℕ)).testBit (↑x5 - (16 : ℕ)) = Bool.true) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (79 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (32 : ℕ)) (x5 : Fin (32 : ℕ)), (↑x4 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x5 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x4 (0 : ℕ)).testBit (↑x5 - (16 : ℕ)) = Bool.true) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (79 : ℕ) ≤ x1.size) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
