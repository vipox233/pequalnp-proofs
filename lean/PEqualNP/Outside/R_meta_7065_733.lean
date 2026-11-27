import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7065_733
    (a1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      x1.size ≤ (27 : ℕ) →
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
      (∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) →
      x1.output < 14 →
      (12 : ℕ) ≤ {x5 ∈ Finset.range x1.size | (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op.eval [Bool.false, Bool.true] = Bool.true}.card)
    (a2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      x1.size ≤ (27 : ℕ) →
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
      (∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) →
      14 ≤ x1.output →
      (12 : ℕ) ≤ {x5 ∈ Finset.range x1.size | (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op.eval [Bool.false, Bool.true] = Bool.true}.card)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      x1.size ≤ (27 : ℕ) →
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
      (∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) →
      (12 : ℕ) ≤ {x5 ∈ Finset.range x1.size | (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op.eval [Bool.false, Bool.true] = Bool.true}.card := by
  intro x1 h1 h2 h3
  by_cases h : x1.output < 14
  · exact a1 x1 h1 h2 h3 h
  · exact a2 x1 h1 h2 h3 (Nat.le_of_not_lt h)
