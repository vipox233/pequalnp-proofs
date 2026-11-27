import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18023_734
    (a1 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
      (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →
      x5.output < x1 + x2 →
      ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ))
    (a2 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
      (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →
      x1 + x2 ≤ x5.output →
      ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ))
    : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
      (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →
      ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 h1 h2 h3
  by_cases h : x5.output < x1 + x2
  · exact a1 x1 x2 x3 x5 h1 h2 h3 h
  · exact a2 x1 x2 x3 x5 h1 h2 h3 (Nat.le_of_not_lt h)
