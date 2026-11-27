import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The last gate of the circuit is an AND gate or it is not, so the step is asked once under
-- each of the two cases and the two children together give the step by a case split.
theorem PEqualNP.Outside.R_meta_17453_1
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (59 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (59 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (59 : ℕ) ≤ x1.size := by
  intros x1 h1 h2 h3 h4 h5
  by_cases hq : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact lastAnd x1 h1 h2 h3 h4 h5 hq
  · exact lastOr x1 h1 h2 h3 h4 h5 hq
