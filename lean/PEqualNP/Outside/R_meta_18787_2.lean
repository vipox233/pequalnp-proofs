import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18787_2
    (hTopAnd : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (58 : ℕ) ≤ x1.size)
    (hTopNotAnd : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and → (58 : ℕ) ≤ x1.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) → (58 : ℕ) ≤ x1.size) := by
  intro x1 hM hEval
  by_cases hTop : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact hTopAnd x1 hM hEval hTop
  · exact hTopNotAnd x1 hM hEval hTop
