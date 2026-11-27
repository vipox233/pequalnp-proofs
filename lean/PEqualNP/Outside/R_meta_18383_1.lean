import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18383_1
    (hLeft : ∀ (x1 : Fin (26 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), x1 = (0 : Fin (26 : ℕ)) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x6 ≠ x1 ∧ Fin.natAdd (13 : ℕ) x7 ≠ x1 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (59 : ℕ) ≤ x2.size)
    (hRight : ∀ (x1 : Fin (26 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), x1 = (13 : Fin (26 : ℕ)) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x6 ≠ x1 ∧ Fin.natAdd (13 : ℕ) x7 ≠ x1 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (59 : ℕ) ≤ x2.size) :
    (∀ (x1 : Fin (26 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), x1 = (0 : Fin (26 : ℕ)) ∨ x1 = (13 : Fin (26 : ℕ)) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ Fin.castAdd (13 : ℕ) x6 ≠ x1 ∧ Fin.natAdd (13 : ℕ) x7 ≠ x1 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (59 : ℕ) ≤ x2.size) := by
  intro x1 x2 hOr
  rcases hOr with hl | hr
  · exact hLeft x1 x2 hl
  · exact hRight x1 x2 hr
