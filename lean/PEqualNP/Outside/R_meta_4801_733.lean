import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4801_733
    (a1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
      x1.size < (64 : ℕ) →
      (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) →
      x1.output < 26 →
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x5 ∧ x5.size ≤ x1.size ∧ (∀ (x6 : Fin (26 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6)) ∧ ¬∃ (x6 : ℕ) (x7 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x6 x7)
    (a2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
      x1.size < (64 : ℕ) →
      (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) →
      26 ≤ x1.output →
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x5 ∧ x5.size ≤ x1.size ∧ (∀ (x6 : Fin (26 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6)) ∧ ¬∃ (x6 : ℕ) (x7 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x6 x7)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
      x1.size < (64 : ℕ) →
      (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) →
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x5 ∧ x5.size ≤ x1.size ∧ (∀ (x6 : Fin (26 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6)) ∧ ¬∃ (x6 : ℕ) (x7 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x6 x7 := by
  intro x1 h1 h2 h3
  by_cases h : x1.output < 26
  · exact a1 x1 h1 h2 h3 h
  · exact a2 x1 h1 h2 h3 (Nat.le_of_not_lt h)
